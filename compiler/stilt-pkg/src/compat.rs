//! Compatible selections (versions.compatible-selections): where a manifest asks for one version of
//! a repository and a higher one is selected, the change in the API from the one to the other must
//! need no new major version, so that each compatible release is checked where it is used.

use std::path::Path;

use stilt_diag::codes;

use crate::api::{Apis, changes};
use crate::fill::Unfilled;
use crate::graph::manifest_in;
use crate::select::Served;
use crate::version::Change;

/// The E0605 of each request that its selected version breaks, at the root's entry through
/// which the request arrives, the first change that needs a new major version named by its
/// address.
pub fn incompatible(root: &Path, served: &[Served], apis: &mut dyn Apis) -> Vec<Unfilled> {
    let mut found: Vec<Unfilled> = Vec::new();
    // Two majors are an E0605 of their own.
    for s in served.iter().filter(|s| s.asked.major == s.selected.major) {
        let (Ok(old), Ok(new)) = (apis.api(&s.asked_dir), apis.api(&s.selected_dir)) else {
            continue;
        };
        let steps = changes(&old, &new);
        let Some(first) = steps.iter().find(|step| step.needs == Change::Major) else {
            continue;
        };
        let name = manifest_in(&s.selected_dir)
            .and_then(|(manifest, _)| manifest.name)
            .unwrap_or_default();
        let selector = s.selector.as_deref().unwrap_or("this manifest");
        let asked = match &s.asker {
            None => format!("the {} asked for here", s.asked),
            Some(asker) => format!("the {} that {asker} asks for", s.asked),
        };
        let message = format!(
            "{selector} asks for `{name}` {}, which {}, which {asked} has",
            s.selected,
            first.described()
        );
        let unfilled = Unfilled {
            dir: root.to_path_buf(),
            entry: s.entry,
            code: codes::E0605,
            message,
        };
        if !found.contains(&unfilled) {
            found.push(unfilled);
        }
    }
    found
}
