//! The checker takes any program of one file without panicking. One database holds the
//! standard library for every input, as the engine does, and each input replaces the file's
//! bytes, so that the checks run incrementally, as they do while a person types.

#![no_main]

use std::sync::{Mutex, OnceLock};

use stilt_db::{Database, Program, SourceFile};
use libfuzzer_sys::fuzz_target;
use salsa::Setter as _;

struct Held {
    db: Database,
    program: Program,
    file: SourceFile,
}

fn held() -> &'static Mutex<Held> {
    static HELD: OnceLock<Mutex<Held>> = OnceLock::new();
    HELD.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("stilt-fuzz-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temporary directory");
        let path = dir.join("main.lt");
        std::fs::write(&path, "fn main() {}\n").expect("the file is written");
        let db = Database::default();
        let program = stilt_db::load(&db, &path).expect("the program loads");
        let file = program.files(&db)[0];
        Mutex::new(Held { db, program, file })
    })
}

fuzz_target!(|data: &[u8]| {
    let mut held = held()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let Held { db, program, file } = &mut *held;
    file.set_bytes(db).to(data.to_vec());
    let _ = stilt_rc::check_in_parallel(&*db, *program);
});
