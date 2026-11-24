//! The database of one program, which can record the queries it runs, so that a test or a client of
//! the engine can tell what an update ran again (goals body-edits-recheck-one-body and one-engine).

use std::fmt;
use std::sync::{Arc, Mutex, PoisonError};

use salsa::{DatabaseKeyIndex, EventKind, Storage};

use crate::Db;

/// The queries a database ran, each with its key, in the order they started.
type Ran = Arc<Mutex<Vec<DatabaseKeyIndex>>>;

/// The database of one program.
#[salsa::db]
#[derive(Clone, Default)]
pub struct Database {
    storage: Storage<Self>,
    ran: Option<Ran>,
    extras: crate::Extras,
}

impl Database {
    /// A database that records each query it runs.
    #[must_use]
    pub fn recording() -> Self {
        let ran = Ran::default();
        let recorded = Arc::clone(&ran);
        Self {
            storage: Storage::new(Some(Box::new(move |event| {
                if let EventKind::WillExecute { database_key } = event.kind {
                    recorded
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(database_key);
                }
            }))),
            ran: Some(ran),
            extras: crate::Extras::default(),
        }
    }

    /// The queries this database ran since this was last asked, each as its name and key,
    /// such as `infer_body(Id(2c01))`: none for a database that doesn't record them.
    #[must_use]
    pub fn ran(&self) -> Vec<String> {
        let Some(ran) = &self.ran else {
            return Vec::new();
        };
        let ran = std::mem::take(&mut *ran.lock().unwrap_or_else(PoisonError::into_inner));
        salsa::attach(self, || ran.iter().map(|key| format!("{key:?}")).collect())
    }

    /// The names of the queries this database ran since this was last asked, such as
    /// `infer_body`, without their keys.
    #[must_use]
    pub fn ran_queries(&self) -> Vec<String> {
        let mut names = self.ran();
        for name in &mut names {
            name.truncate(name.find('(').unwrap_or(name.len()));
        }
        names
    }
}

impl fmt::Debug for Database {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Database").finish_non_exhaustive()
    }
}

#[salsa::db]
impl salsa::Database for Database {}

#[salsa::db]
impl Db for Database {
    fn extras(&self) -> &crate::Extras {
        &self.extras
    }
}
