//! The function that `task.scope` is given where it is called, and its calls of `s.spawn`
//! (tasks.scope-failure). Under `task.threads()` a task of a scope runs on a thread while the
//! scope's function goes on, as if the task doesn't raise, which is what the sequential run
//! does after the call only if a raise there leaves the scope at once. So a call of `s.spawn`
//! in that function, around which nothing catches, tells the runtime that its task may run on a
//! thread; any other runs where it starts, as the sequential run does.

use stilt_types::tast::{self, Callee as TCallee, ExprKind};

use super::Lower;
use super::calls::Forms;
use super::places::Writeback;
use crate::FnRef;
use crate::mir::{Arg, Runtime, Shared, Stmt};

/// Where code stands to the function of a scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Scoped {
    Outside,
    /// The arguments of a call of `task.scope`, whose closure literal is the scope's function.
    Arguments,
    /// The scope's function.
    Function,
}

impl Scoped {
    /// Where the code of a closure literal written here stands.
    pub(crate) fn inner(self) -> Self {
        match self {
            Self::Arguments => Self::Function,
            _ => Self::Outside,
        }
    }
}

/// Whether a call's first argument is the function of a scope, written as a closure literal at
/// a call of `task.scope`.
fn scope_function(callee: &TCallee, args: &[tast::Arg]) -> bool {
    matches!(callee, TCallee::Function(item) if &*item.home == "std.task" && &*item.name == "scope")
        && matches!(
            args.first().map(|a| &a.value.kind),
            Some(ExprKind::Closure(..))
        )
}

impl Lower<'_> {
    /// The arguments of a call, lowering the closure literal that a call of `task.scope` is
    /// given as a scope's function.
    pub(crate) fn scoped_arguments(
        &mut self,
        callee: &TCallee,
        args: &[tast::Arg],
        forms: &Forms,
    ) -> (Vec<Arg>, Vec<Writeback>) {
        let outer = self.scope;
        if scope_function(callee, args) {
            self.scope = Scoped::Arguments;
        }
        let lowered = self.arguments(args, forms);
        self.scope = outer;
        lowered
    }

    /// Before a call of the native `f`: if it is `s.spawn`, in a scope's function, with nothing
    /// around it that catches, tells the runtime that its raise leaves the scope at once.
    pub(crate) fn scope_spawn(&mut self, f: &FnRef) {
        let spawn = matches!(f, FnRef::Member(owner, name)
            if &*owner.home == "std.task" && &*owner.name == "Scope" && &**name == "spawn");
        if spawn && self.scope == Scoped::Function && self.catchers.is_empty() {
            self.b
                .emit(Stmt::Effect(Runtime::Shared(Shared::Direct), Vec::new()));
        }
    }
}
