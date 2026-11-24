//! The grants of manifests (packages.grants, packages.own-effects, packages.ungranted-effects and
//! packages.running-with-ungranted-effect; facts.capability-grants, facts.own-capabilities and
//! facts.ungranted-capabilities): each entry that doesn't grant a capability its dependency's own
//! code has, or `io` that it performs without one, is an E0608 for each, which offers the narrowest
//! grant.

use stilt_db::{Db, Dependency, Granting, Program};
use stilt_diag::{Diagnostic, Edit, File, Fix, codes};
use stilt_hir::FileDiagnostic;

use super::{IoCall, Need, fetched, io_calls};

/// What manifests of the program don't grant the packages they name, which their own code needs
/// (packages.running-with-ungranted-effect): each package with each need. Each of its functions
/// that has the need panics with `check-error` when it is called.
#[salsa::tracked(returns(ref))]
pub fn ungranted(db: &dyn Db, program: Program) -> Vec<(u32, Need)> {
    let mut found = Vec::new();
    for package in &program.packages(db).list {
        for dep in &package.deps {
            let Some(target) = dep.package.and_then(|t| u32::try_from(t).ok()) else {
                continue;
            };
            for call in io_calls(db, program, target) {
                let ungranted = (target, call.need);
                if !call.need.granted(dep.may) && !found.contains(&ungranted) {
                    found.push(ungranted);
                }
            }
        }
    }
    found.sort_unstable();
    found
}

/// The diagnostics of the program's manifests: those found when they were read, the E0608s of
/// each entry that doesn't grant what its dependency needs, and the E0607 of each fetched
/// dependency with errors.
#[salsa::tracked(returns(ref))]
pub fn diagnostics(db: &dyn Db, program: Program) -> Vec<FileDiagnostic> {
    let packages = program.packages(db);
    let mut found: Vec<FileDiagnostic> = packages
        .problems
        .iter()
        .map(|(file, diagnostic)| FileDiagnostic {
            file: *file,
            diagnostic: diagnostic.clone(),
        })
        .collect();
    for package in packages.list.iter().filter(|p| !p.fetched) {
        let Some(manifest) = package.manifest else {
            continue;
        };
        for dep in &package.deps {
            found.extend(
                ungranted_entries(db, program, dep)
                    .into_iter()
                    .map(|diagnostic| FileDiagnostic {
                        file: manifest,
                        diagnostic,
                    }),
            );
        }
    }
    found.extend(fetched::errors(db, program));
    found
}

/// The E0608s of an entry, one for each capability that it doesn't grant and its dependency's
/// own code has, in the order of facts.capabilities, and one for `io` that it performs without one,
/// each at the first function that has it (packages.ungranted-effects;
/// facts.ungranted-capabilities).
pub(crate) fn ungranted_entries(
    db: &dyn Db,
    program: Program,
    dep: &Dependency,
) -> Vec<Diagnostic> {
    let Some(target) = dep.package.and_then(|t| u32::try_from(t).ok()) else {
        return Vec::new();
    };
    let calls = io_calls(db, program, target);
    let mut needs: Vec<Need> = calls.iter().map(|c| c.need).collect();
    needs.sort_unstable();
    needs.dedup();
    needs
        .iter()
        .filter(|need| !need.granted(dep.may))
        .filter_map(|need| calls.iter().find(|c| c.need == *need))
        .map(|call| ungranted_entry(db, dep, call, &needs))
        .collect()
}

/// The E0608 of the first function whose call `call` needs what `dep` doesn't grant, with the
/// fix that grants the narrowest list for `needs`, everything its dependency needs.
fn ungranted_entry(db: &dyn Db, dep: &Dependency, call: &IoCall, needs: &[Need]) -> Diagnostic {
    let text = String::from_utf8_lossy(call.file.bytes(db)).into_owned();
    let path = call.file.path(db);
    let at = File::new(path, &text).position(call.at);
    let granted = if dep.may.io || !dep.may.capabilities.is_empty() || dep.may.unsafe_code {
        format!("doesn't grant `{}` to `{}`", call.need.text(), dep.name)
    } else if call.need == Need::Unsafe {
        format!("grants `{}` nothing", dep.name)
    } else {
        format!("grants `{}` no effect", dep.name)
    };
    let how = match call.need {
        Need::Unsafe => String::new(),
        Need::Capability(_) | Need::Io => format!(", by calling `{}`", call.callee),
    };
    let message = format!(
        "`{}` {}{how} at {path}:{at}, but this manifest {granted}",
        call.function,
        call.need.verb(),
    );
    let d = Diagnostic::new(codes::E0608, dep.key, message);
    let Some(granting) = &dep.grant else {
        return d;
    };
    let narrowest = narrowest(needs);
    let list = format!(
        "[{}]",
        narrowest
            .iter()
            .map(|n| format!("\"{}\"", n.text()))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let edit = match granting {
        Granting::Replace(at) => Edit::replace(*at, list),
        Granting::Insert(at, before) => Edit::insert(*at, format!("{before}{list}")),
    };
    let named: Vec<String> = narrowest
        .iter()
        .map(|n| format!("`{}`", n.text()))
        .collect();
    let label = format!("grant {} to `{}`", and_list(&named), dep.name);
    d.with_fix(Fix::new(label, vec![edit]))
}

/// The narrowest grant of `needs` (facts.ungranted-capabilities): `io` alone when the code performs
/// `io` without a capability, and its capabilities otherwise, in the order of facts.capabilities,
/// then `unsafe` when it holds an `unsafe` block, which `io` doesn't grant (c.granting-unsafe).
fn narrowest(needs: &[Need]) -> Vec<Need> {
    if needs.contains(&Need::Io) {
        let unsafe_code = needs.contains(&Need::Unsafe).then_some(Need::Unsafe);
        std::iter::once(Need::Io).chain(unsafe_code).collect()
    } else {
        needs.to_vec()
    }
}

/// Words joined as prose: "`a`", "`a` and `b`", "`a`, `b` and `c`".
fn and_list(words: &[String]) -> String {
    match words {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}
