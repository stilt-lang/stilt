//! The counts of a macro's run (macros.step-limits): its steps, its frames, and the frames of the
//! macro's module's own functions that are running, which a run that stops names, innermost
//! last, a run of one function's frames written once with its count.

use stilt_hir::hir::Name;

use crate::eval::{Flow, Stop};

pub(crate) const STEPS: u64 = 10_000_000;
pub(crate) const FRAMES: u32 = 10_000;

/// The counts of a run.
#[derive(Debug)]
pub(crate) struct Run {
    /// The macro's module, whose functions' frames a run that stops names.
    pub(crate) home: Name,
    pub(crate) steps: u64,
    pub(crate) depth: u32,
    /// The names of the module's own functions that are running, outermost first.
    pub(crate) frames: Vec<Name>,
}

impl Run {
    pub(crate) fn new(home: Name) -> Self {
        Self {
            home,
            steps: 0,
            depth: 0,
            frames: Vec::new(),
        }
    }

    /// A call of a function, a method, a closure or a native, or a turn of a loop.
    pub(crate) fn step<'a>(&mut self) -> Result<(), Flow<'a>> {
        self.steps += 1;
        if self.steps > STEPS {
            return Err(Flow::Stop(Stop::Steps));
        }
        if !crate::value::fits(0) {
            return Err(Flow::Stop(Stop::Memory));
        }
        Ok(())
    }

    /// Enters a frame of a body of module `module`, the function `name`, or of a closure.
    pub(crate) fn enter<'a>(&mut self, module: Option<Name>, name: Name) -> Result<(), Flow<'a>> {
        if self.depth >= FRAMES {
            return Err(Flow::Stop(Stop::Frames));
        }
        self.depth += 1;
        if module == Some(self.home) {
            self.frames.push(name);
        }
        Ok(())
    }

    /// Leaves the frame that [`Run::enter`] entered, unless the run stops, which keeps the
    /// frames that were running.
    pub(crate) fn leave(&mut self, module: Option<Name>, stopping: bool) {
        if stopping {
            return;
        }
        self.depth = self.depth.saturating_sub(1);
        if module == Some(self.home) {
            self.frames.pop();
        }
    }

    /// The frames of the module's own functions that were running, as E0226 names them.
    pub(crate) fn shown_frames(&self) -> String {
        let mut runs: Vec<(Name, u32)> = Vec::new();
        for f in &self.frames {
            match runs.last_mut() {
                Some((g, n)) if g == f => *n += 1,
                _ => runs.push((*f, 1)),
            }
        }
        if runs.is_empty() {
            return String::new();
        }
        let shown: Vec<String> = runs
            .iter()
            .map(|(f, n)| {
                if *n == 1 {
                    format!("`{f}`")
                } else {
                    format!("`{f}` {n} times")
                }
            })
            .collect();
        format!("; running {}", shown.join(", then "))
    }
}
