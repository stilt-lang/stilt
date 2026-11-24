//! The check of `without alloc` in debug builds (facts.without-alloc; `stilt_runtime`'s
//! `limits`). A function that a `without alloc` limits counts its frames on entry and stops counting
//! them on return. A function that allocates, which a limited one reaches only through a function
//! value whose facts it doesn't inherit (facts.calls-through-function-values), runs with the
//! count at 0 and puts it back on return. Every other function leaves the count as it is, so an
//! allocation in it while a limited frame runs ends the program: the facts were wrong.

use stilt_mir::Guard;

use crate::translate::Translator;

impl Translator<'_, '_> {
    /// The entry of a guarded function: the count raised, or set to 0 and the count it found
    /// kept for its returns.
    pub(crate) fn guard_entry(&mut self) -> Result<(), String> {
        self.guard = self.reg.guard(&self.f.name);
        match self.guard {
            Some(Guard::Limited) => {
                self.runtime("stilt_rt_alloc_limit_enter", &[], false)?;
            }
            Some(Guard::Allocating) => {
                self.saved_count = self.runtime("stilt_rt_alloc_limit_suspend", &[], true)?;
            }
            None => {}
        }
        Ok(())
    }

    /// A return of a guarded function: the count lowered, or put back as its entry found it.
    pub(crate) fn guard_return(&mut self) -> Result<(), String> {
        match (self.guard, self.saved_count) {
            (Some(Guard::Limited), _) => {
                self.runtime("stilt_rt_alloc_limit_leave", &[], false)?;
            }
            (Some(Guard::Allocating), Some(saved)) => {
                self.runtime("stilt_rt_alloc_limit_resume", &[saved], false)?;
            }
            _ => {}
        }
        Ok(())
    }
}
