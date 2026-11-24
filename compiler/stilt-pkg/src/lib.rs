//! Packages (packages.manifest and packages.content-hash): the manifest, `stilt.toml`, in TOML
//! 1.0; the packages that a program's manifests name, read from directories or fetched from git
//! repositories and pinned by their content hashes; the versions that minimal version selection
//! picks; and the release toolchain, fetched and checked against its SHA-256
//! (builds.fetching-toolchain).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag` and `stilt-
//! syntax` alone, and on no database or phase after parsing.
#![warn(missing_docs)]

pub mod api;
pub mod compat;
pub mod edition;
pub mod fetch;
pub mod files;
pub mod fill;
pub mod git;
pub mod graph;
pub mod hash;
pub mod manifest;
mod net;
pub mod select;
pub mod toml;
pub mod toolchain;
pub mod version;

pub use graph::{Fetcher, Graph, Package};
pub use manifest::{Entry, Manifest, Source};
pub use version::{Change, Version};
