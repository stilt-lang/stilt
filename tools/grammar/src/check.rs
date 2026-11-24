//! Feeds the bytes of programs to a published grammar, read by llguidance, and checks that
//! every prefix stays viable.

use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use llguidance::api::TopLevelGrammar;
use llguidance::{Matcher, ParserFactory};
use toktrie::ApproximateTokEnv;

use crate::suite::Program;

/// A grammar that cannot continue a program.
pub(crate) struct Rejection {
    pub(crate) program: String,
    pub(crate) offset: usize,
    pub(crate) line: usize,
    pub(crate) context: String,
    pub(crate) reason: String,
}

/// The Lark text read by llguidance, ready to check programs against.
pub(crate) struct Checker {
    factory: ParserFactory,
    lark: String,
}

impl Checker {
    pub(crate) fn new(lark: String) -> Result<Self, String> {
        let env = ApproximateTokEnv::single_byte_env();
        let mut factory = ParserFactory::new_simple(&env).map_err(|e| e.to_string())?;
        factory.quiet();
        let checker = Self { factory, lark };
        checker.matcher()?;
        Ok(checker)
    }

    fn matcher(&self) -> Result<Matcher, String> {
        let parser = self
            .factory
            .create_parser(TopLevelGrammar::from_lark(self.lark.clone()))
            .map_err(|e| format!("{e:#}"))?;
        Ok(Matcher::new(Ok(parser)))
    }

    /// Checks the programs, on as many threads as the machine has, each starting a program
    /// from the start of the grammar. The rejections come in order of program.
    pub(crate) fn check_all(&self, programs: &[Program]) -> Result<Vec<Rejection>, String> {
        let threads = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(programs.len().max(1));
        let matchers = (0..threads)
            .map(|_| self.matcher())
            .collect::<Result<Vec<_>, _>>()?;
        let next = AtomicUsize::new(0);
        let found = Mutex::new(Vec::new());
        let (next_ref, found_ref) = (&next, &found);
        std::thread::scope(|scope| {
            let (next, found) = (next_ref, found_ref);
            for mut matcher in matchers {
                scope.spawn(move || {
                    while let Some(program) = programs.get(next.fetch_add(1, Ordering::Relaxed)) {
                        if matcher.reset().is_err() {
                            match self.matcher() {
                                Ok(fresh) => matcher = fresh,
                                Err(_) => return,
                            }
                        }
                        if let Some(rejection) =
                            check_program(&mut matcher, program, &|| self.matcher())
                        {
                            found.lock().expect("a worker panicked").push(rejection);
                        }
                    }
                });
            }
        });
        let mut rejections = found.into_inner().map_err(|e| e.to_string())?;
        rejections.sort_by(|a, b| a.program.cmp(&b.program));
        Ok(rejections)
    }
}

/// Whether the grammar takes the program's bytes, in one call, and can finish after them.
fn accepts(matcher: &mut Matcher, bytes: &[u8]) -> bool {
    let tokens: Vec<u32> = bytes.iter().map(|&b| u32::from(b)).collect();
    matcher.consume_tokens(&tokens).is_ok() && matcher.is_accepting().unwrap_or(false)
}

/// The first byte of the program that no continuation accepts, if any, or the end of a
/// program that the grammar cannot finish there. A program that passes is checked in one call,
/// and only a rejected one is read again byte by byte, by a matcher of its own, to find where.
fn check_program(
    matcher: &mut Matcher,
    program: &Program,
    fresh: &dyn Fn() -> Result<Matcher, String>,
) -> Option<Rejection> {
    if accepts(matcher, &program.bytes) {
        return None;
    }
    let failure = |offset: usize, reason: String| {
        let head = &program.bytes[..offset.min(program.bytes.len())];
        let start = head.len().saturating_sub(60);
        Rejection {
            program: program.name.clone(),
            offset,
            line: head.split(|&b| b == b'\n').count(),
            context: String::from_utf8_lossy(&head[start..]).into_owned(),
            reason,
        }
    };
    let mut replay = match fresh() {
        Ok(replay) => replay,
        Err(reason) => return Some(failure(0, reason)),
    };
    for (offset, &byte) in program.bytes.iter().enumerate() {
        if let Err(e) = replay.consume_token(u32::from(byte)) {
            let reason = format!("{e:#}");
            return Some(failure(
                offset,
                reason.lines().next().unwrap_or_default().to_owned(),
            ));
        }
    }
    Some(failure(
        program.bytes.len(),
        "the program is not a complete sentence".into(),
    ))
}
