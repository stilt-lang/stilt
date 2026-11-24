//! Who may reach an engine: only the user who started it (engines.private). Its socket lies in
//! a directory of the user's own, under the system's temporary directory, that no other user
//! may open, and each end of a connection checks that the other runs as the same user, where
//! the system says who the peer is. Whoever answers a command decides what it reports, and
//! for `run` and `test` the code it runs, so an engine of another user is never asked.

use std::fs::{self, DirBuilder, Permissions};
use std::io;
use std::os::unix::fs::{DirBuilderExt as _, MetadataExt as _, PermissionsExt as _};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

/// The directory of this user's engines, named after the user's id.
pub(crate) fn directory() -> PathBuf {
    std::env::temp_dir().join(format!("stilt-{}", user()))
}

/// Makes `tmp`, given to a command as its temporary directory, one in which this user's
/// engines' directory can't be made, since a file has its name, so that the command uses no
/// engine and runs in its own process.
pub(crate) fn without_engines(tmp: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(tmp)?;
    std::fs::write(tmp.join(format!("stilt-{}", user())), "")
}

/// The effective user id of this process.
fn user() -> u32 {
    nix::unistd::geteuid().as_raw()
}

/// Makes `dir` the user's private directory: makes it, open to the user alone, or checks the
/// one there, closing it to others when the user owns it. A directory that another user owns,
/// or something there that isn't a directory, as a link is, can't be made private.
pub(super) fn make_private(dir: &Path) -> Result<(), String> {
    match DirBuilder::new().mode(0o700).create(dir) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(format!("cannot make {}: {e}", dir.display())),
    }
    let meta = fs::symlink_metadata(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let seen = Seen {
        directory: meta.is_dir(),
        owner: meta.uid(),
        mode: meta.mode(),
    };
    match judge(&seen, user()) {
        Judged::Private => Ok(()),
        Judged::Open => fs::set_permissions(dir, Permissions::from_mode(0o700))
            .map_err(|e| format!("cannot close {} to other users: {e}", dir.display())),
        Judged::Foreign(why) => Err(format!("{} {why}", dir.display())),
    }
}

/// What the directory's entry says of it, without following a link.
#[derive(Debug)]
struct Seen {
    directory: bool,
    owner: u32,
    mode: u32,
}

/// Whether a directory can hold a user's engines.
#[derive(Debug, PartialEq, Eq)]
enum Judged {
    /// The user's own, and only the user may open it.
    Private,
    /// The user's own, but others may open it, so it must be closed first.
    Open,
    /// It can't, for this reason.
    Foreign(&'static str),
}

fn judge(seen: &Seen, user: u32) -> Judged {
    if !seen.directory {
        Judged::Foreign("isn't a directory")
    } else if seen.owner != user {
        Judged::Foreign("belongs to another user")
    } else if seen.mode & 0o077 != 0 {
        Judged::Open
    } else {
        Judged::Private
    }
}

/// Closes an engine's socket to every user but its owner, which the directory already does.
pub(super) fn close(socket: &Path) -> io::Result<()> {
    fs::set_permissions(socket, Permissions::from_mode(0o600))
}

/// Whether the process at the other end of `stream` runs as this user. A system that can't
/// say counts as a refusal.
pub(super) fn same_user(stream: &UnixStream) -> bool {
    peer(stream).is_some_and(|peer| peer == user())
}

/// The effective user id of the process at the other end of `stream`.
#[cfg(any(target_os = "linux", target_os = "android"))]
fn peer(stream: &UnixStream) -> Option<u32> {
    use nix::sys::socket::{getsockopt, sockopt::PeerCredentials};
    getsockopt(stream, PeerCredentials).ok().map(|c| c.uid())
}

/// The effective user id of the process at the other end of `stream`.
#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "netbsd",
    target_os = "openbsd"
))]
fn peer(stream: &UnixStream) -> Option<u32> {
    nix::unistd::getpeereid(stream)
        .ok()
        .map(|(uid, _)| uid.as_raw())
}

/// A system that doesn't say who the peer is: the private directory alone keeps other users
/// out.
#[cfg(not(any(
    target_os = "linux",
    target_os = "android",
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "netbsd",
    target_os = "openbsd"
)))]
fn peer(_: &UnixStream) -> Option<u32> {
    Some(user())
}

#[cfg(test)]
mod tests {
    use super::{Judged, Seen, judge};

    const ME: u32 = 501;

    fn seen(directory: bool, owner: u32, mode: u32) -> Seen {
        Seen {
            directory,
            owner,
            mode,
        }
    }

    #[test]
    fn the_users_own_closed_directory_is_private() {
        assert_eq!(judge(&seen(true, ME, 0o40_700), ME), Judged::Private);
        assert_eq!(judge(&seen(true, ME, 0o40_500), ME), Judged::Private);
    }

    #[test]
    fn a_directory_of_the_users_that_others_may_open_is_closed_first() {
        for mode in [0o40_777, 0o40_750, 0o40_701, 0o41_777] {
            assert_eq!(judge(&seen(true, ME, mode), ME), Judged::Open, "{mode:o}");
        }
    }

    #[test]
    fn a_directory_of_another_user_is_refused_whatever_its_mode() {
        for mode in [0o40_700, 0o40_777] {
            assert_eq!(
                judge(&seen(true, ME + 1, mode), ME),
                Judged::Foreign("belongs to another user")
            );
        }
        assert_eq!(
            judge(&seen(true, 0, 0o40_700), ME),
            Judged::Foreign("belongs to another user"),
            "not even root's"
        );
    }

    #[test]
    fn a_link_or_a_file_is_refused_even_the_users_own() {
        assert_eq!(
            judge(&seen(false, ME, 0o120_777), ME),
            Judged::Foreign("isn't a directory")
        );
        assert_eq!(
            judge(&seen(false, ME, 0o100_600), ME),
            Judged::Foreign("isn't a directory")
        );
    }

    #[test]
    fn the_peer_of_a_connection_within_this_process_is_this_user() {
        let (a, b) = std::os::unix::net::UnixStream::pair().expect("a pair of sockets");
        assert!(super::same_user(&a));
        assert!(super::same_user(&b));
        assert_eq!(super::peer(&a), Some(super::user()));
    }
}
