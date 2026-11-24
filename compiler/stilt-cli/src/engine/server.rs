//! The engine's side: it holds the program's database, takes in the edits to its files before
//! each command, and answers each command from a handle of its own.

mod language;
mod repl;
mod runs;
mod tests;

use std::io;
use std::os::unix::net::{UnixListener, UnixStream};
use std::panic::AssertUnwindSafe;
use std::path::Path;
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use stilt_db::{Database, Program};
use stilt_rc::Counted;

use super::Command;
use super::place::{Place, identity};
use super::private;
use super::wire::{Reply, receive_request, send};
use crate::report::{self, Report};
use crate::sync::Synced;
use crate::test::Memory;

/// The program, held in the database that every command reads.
struct Held {
    db: Database,
    synced: Synced,
    /// How many times an edit of the program's files has been taken in.
    revision: u64,
}

impl Held {
    /// Takes in the edits made to the program's files since the last look, and gives the
    /// revision that holds them.
    fn sync(&mut self) -> Result<u64, String> {
        if self.synced.sync(&mut self.db)? {
            self.revision += 1;
        }
        Ok(self.revision)
    }
}

/// Why the engine can't answer.
enum Unanswered {
    /// The program's files can't be read.
    Unreadable(String),
    /// A query panicked.
    Panicked,
}

impl Unanswered {
    fn message(self) -> String {
        match self {
            Unanswered::Unreadable(message) => message,
            Unanswered::Panicked => "a query panicked".to_owned(),
        }
    }
}

/// A running engine.
struct Engine {
    place: Place,
    identity: String,
    held: Mutex<Held>,
    /// The reference counting of the functions that runs reach, which every run shares, so
    /// that a run after another counts only what an edit changed.
    counted: Mutex<Counted>,
    /// What the last build kept, so that a build after another counts and compiles only what
    /// an edit changed (goal compile-time-code-rebuilds).
    built: Mutex<crate::build::Kept>,
    /// What the runs of tests it answered left: their results, and the files of those whose
    /// verdict wasn't done.
    tests: Mutex<Memory>,
    /// How many commands, a run's looks among them, are being answered.
    active: AtomicUsize,
    /// Whether a command lowered the program's code since the database last forgot results.
    lowered: AtomicBool,
    /// How many sessions of the REPL are open, which keep the engine from idling.
    sessions: AtomicUsize,
    /// When the last command was answered.
    last: Mutex<Instant>,
    idle: Duration,
}

/// Holds the program at `path` and answers commands about it until it has been idle for `idle`
/// seconds, or is asked to stop, keeping a record of the queries it runs when `record`.
/// Another engine holding the program already is no error.
pub(crate) fn serve(path: &Path, idle: u64, record: bool) -> ExitCode {
    let Some(place) = Place::of(path) else {
        return Report::refuse(&format!("{} doesn't exist", path.display())).print();
    };
    let lock = match place.hold() {
        Ok(Some(lock)) => lock,
        Ok(None) => {
            eprintln!("stilt: an engine holds {} already", path.display());
            return ExitCode::SUCCESS;
        }
        Err(e) => return Report::refuse(&format!("cannot hold {}: {e}", path.display())).print(),
    };
    let mut db = if record {
        Database::recording()
    } else {
        Database::default()
    };
    stilt_db::keep_trees(&mut db, TREES);
    stilt_types::keep_typed(&mut db, usize::MAX);
    let synced = match Synced::load(&db, &place.program) {
        Ok(synced) => synced,
        Err(message) => return Report::refuse(&message).print(),
    };
    let _ = std::fs::remove_file(&place.socket);
    let listener = match UnixListener::bind(&place.socket).and_then(|listener| {
        private::close(&place.socket)?;
        Ok(listener)
    }) {
        Ok(listener) => listener,
        Err(e) => return Report::refuse(&format!("cannot listen: {e}")).print(),
    };
    let engine = Arc::new(Engine {
        place,
        identity: identity(),
        held: Mutex::new(Held {
            db,
            synced,
            revision: 0,
        }),
        counted: Mutex::new(Counted::default()),
        built: Mutex::default(),
        tests: Mutex::new(Memory::default()),
        active: AtomicUsize::new(0),
        lowered: AtomicBool::new(false),
        sessions: AtomicUsize::new(0),
        last: Mutex::new(Instant::now()),
        idle: Duration::from_secs(idle),
    });
    let watcher = Arc::clone(&engine);
    std::thread::spawn(move || watcher.watch_idle());
    // A process of another user gets no answer (engines.private).
    for stream in listener.incoming().flatten().filter(private::same_user) {
        let engine = Arc::clone(&engine);
        std::thread::spawn(move || engine.answer(&stream));
    }
    drop(lock);
    ExitCode::SUCCESS
}

/// How many syntax trees an engine keeps between commands: those it read last. The queries
/// after the parse keep what they need of a tree, so a tree is read again only when its file
/// changes, or a module it names does (goal bounded-cache).
const TREES: usize = 64;

/// How many typed bodies an engine keeps once a command has lowered the program's code: those
/// it read last. The MIR of every function the command reached is kept, so only an edit, which
/// checks the bodies it changes again, or a command that reads a body's types needs a typed
/// body again (goal bounded-cache). Until then, the engine keeps every typed body, counting
/// them as they are read, so that the bound keeps the right ones; and it keeps every body's
/// HIR, since an edit compares each body of the file it changes with the last, and finds most
/// of them unchanged.
const TYPED: usize = 64;

impl Engine {
    fn held(&self) -> MutexGuard<'_, Held> {
        self.held.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The counting that runs share. An edit that cancels a run's counting leaves it whole,
    /// since what it keeps of each function is replaced at once.
    fn counted(&self) -> MutexGuard<'_, Counted> {
        self.counted.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Forgets the results beyond the bounds, when no other command is being answered, since
    /// that writes to the database: the typed bodies too once a command has lowered the code,
    /// but not after a check, whose build reads them (one-engine).
    fn forget(&self) {
        let mut held = self.held();
        if self.active.load(Ordering::SeqCst) == 1 {
            let lowered = self.lowered.swap(false, Ordering::SeqCst);
            if lowered {
                stilt_types::keep_typed(&mut held.db, TYPED);
            }
            salsa::Database::trigger_lru_eviction(&mut held.db);
            if lowered {
                stilt_types::keep_typed(&mut held.db, usize::MAX);
            }
        }
    }

    /// Notes that a command lowered the program's code.
    fn lowered(&self) {
        self.lowered.store(true, Ordering::SeqCst);
    }

    /// Stops the engine once it has answered no command for its idle time.
    fn watch_idle(&self) {
        loop {
            std::thread::sleep(self.idle.min(Duration::from_secs(1)));
            let since = self
                .last
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .elapsed();
            let idle = self.active.load(Ordering::SeqCst) == 0
                && self.sessions.load(Ordering::SeqCst) == 0;
            if idle && since >= self.idle {
                self.exit();
            }
        }
    }

    fn exit(&self) -> ! {
        let _ = std::fs::remove_file(&self.place.socket);
        std::process::exit(0)
    }

    /// Counts a command as being answered.
    fn begin(&self) {
        self.active.fetch_add(1, Ordering::SeqCst);
    }

    /// Counts a command as answered, once the results beyond the bounds are forgotten if it
    /// `computed` any.
    fn end(&self, computed: bool) {
        if computed {
            self.forget();
        }
        *self.last.lock().unwrap_or_else(PoisonError::into_inner) = Instant::now();
        self.active.fetch_sub(1, Ordering::SeqCst);
    }

    /// Answers one connection: a command, or a run, whose looks it answers until the run
    /// ends. A command from another compiler, which this engine can't read, gets no answer,
    /// so that it runs in its own process, and stops the engine, so that the next one to
    /// start is that compiler's; so does a request in another protocol, which only another
    /// compiler writes.
    fn answer(&self, stream: &UnixStream) {
        self.begin();
        let stops = match receive_request(stream, &self.identity) {
            Ok(Ok(Command::Run)) => return self.run(stream),
            Ok(Ok(Command::Repl)) => return self.repl(stream),
            Ok(Ok(Command::Test { json })) => {
                self.test(stream, json);
                false
            }
            Ok(Ok(command)) => {
                let stops = command == Command::Stop;
                if matches!(command, Command::Build(_)) {
                    self.lowered();
                }
                let _ = send(stream, &self.reply(command));
                stops
            }
            Ok(Err(_)) => true,
            Err(e) if e.kind() == io::ErrorKind::InvalidData => true,
            Err(e) => {
                let _ = send(stream, &Reply::Elsewhere(e.to_string()));
                false
            }
        };
        self.end(true);
        if stops {
            self.exit();
        }
    }

    fn reply(&self, command: Command) -> Reply {
        match command {
            Command::Check { json } => self.report(|db, program| report::check(db, program, json)),
            Command::Build(build) => {
                self.report(|db, program| crate::build::build(db, program, &build, &self.built))
            }
            Command::Show {
                address,
                json,
                expanded,
            } => {
                let how = crate::show::How { json, expanded };
                self.report(|db, program| crate::show::show(db, program, &address, how))
            }
            Command::Ran => Reply::Ran(self.held().db.ran()),
            Command::Language(query) => self.language(query),
            Command::Stop => Reply::Stopping,
            Command::Run | Command::Test { .. } | Command::Repl => {
                Reply::Elsewhere("a run is answered apart".to_owned())
            }
        }
    }

    /// The report of `f` on the program as its files are now.
    fn report(&self, f: impl Fn(&Database, Program) -> Report) -> Reply {
        match self.answered(f) {
            Ok((report, _)) => Reply::Report(report),
            Err(why) => Reply::Elsewhere(why.message()),
        }
    }

    /// `f` on the program as its files are now, with the revision it read. A command that an
    /// edit cancels takes the edit in and answers again.
    fn answered<T>(
        &self,
        mut f: impl FnMut(&Database, Program) -> T,
    ) -> Result<(T, u64), Unanswered> {
        loop {
            let (db, program, revision) = {
                let mut held = self.held();
                let revision = held.sync().map_err(Unanswered::Unreadable)?;
                (held.db.clone(), held.synced.program, revision)
            };
            match salsa::Cancelled::catch(AssertUnwindSafe(|| f(&db, program))) {
                Ok(value) => return Ok((value, revision)),
                Err(salsa::Cancelled::PropagatedPanic) => return Err(Unanswered::Panicked),
                Err(_) => {}
            }
        }
    }
}
