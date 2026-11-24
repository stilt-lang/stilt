//! The natives of `std.net`'s UDP sockets (std.net-datagrams). Binding a socket and sending a
//! datagram raise a `std.io.IoError` that names the address, as opening a connection does; a
//! receive gives `None` where it fails.

use super::done;
use super::sockets::{self, Socket};
use crate::abi::{Ret, option};
use crate::object::Header;
use crate::{list, text};

/// `datagrams(host, port)`: a UDP socket bound to `port` of `host`, by its number.
///
/// # Safety
///
/// `host` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_datagrams(
    _loc: u64,
    host: u64,
    port: i64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the call, and the room.
    unsafe {
        let bound = sockets::datagrams(text::text(&host), port);
        done(bound.map(|id| id as u64), err)
    }
}

/// `send_datagram(id, bytes, host, port)`: sends `bytes` as one datagram to `port` of `host`.
///
/// # Safety
///
/// `bytes` is a live list of `u8`, `host` a live string, and `err` points to room for an error's
/// two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_send_datagram(
    _loc: u64,
    id: i64,
    bytes: u64,
    host: u64,
    port: i64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the list and the string, which outlive the send, and the
    // room.
    unsafe {
        let (bytes, host) = (list::as_bytes(bytes as *mut Header), text::text(&host));
        let sent = sockets::with(id, |s| s.send_to(bytes, host, port)).map(|()| 0);
        done(sent, err)
    }
}

/// `received(id)`: the bytes of the next datagram, or `None` where the wait ends without one.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_received(_loc: u64, id: i64) -> Ret {
    let bytes = sockets::with(id, Socket::receive);
    option(bytes.map(|b| list::of_bytes(&b) as u64))
}

/// `sender(id)`: the address of the sender of the datagram received last.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_sender(_loc: u64, id: i64) -> Ret {
    Ret::ok(text::from(&sockets::with(id, |s| s.sender())))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_net_datagrams,
        stilt_std_net_send_datagram,
        stilt_std_net_received,
        stilt_std_net_sender,
    ]
}
