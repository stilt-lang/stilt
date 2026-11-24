//! Waiting for a child to end without reaping it, so that the system still holds its counts.

use std::io;

/// Returns once the child `pid` has ended, leaving it a zombie, which its [`std::process::Child`]
/// then reaps.
pub(crate) fn until_ended(pid: u32) -> io::Result<()> {
    let id = libc::id_t::try_from(pid).map_err(io::Error::other)?;
    loop {
        let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
        // SAFETY: `waitid` writes a `siginfo_t` into the buffer, which is one, for a child of
        // this process; `WNOWAIT` leaves the child unreaped, so its pid stays its own.
        let status = unsafe {
            libc::waitid(
                libc::P_PID,
                id,
                info.as_mut_ptr(),
                libc::WEXITED | libc::WNOWAIT,
            )
        };
        if status == 0 {
            return Ok(());
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}
