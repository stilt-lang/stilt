//! The natives of `std.net` (std.net, std.net-streams and std.net-listeners), and those of its UDP
//! sockets in [`datagrams`], on the sockets
//! of [`sockets`]. Opening a connection or a listener, a lookup, accepting and writing raise a
//! `std.io.IoError` that names the address, written to the memory that the caller passes a
//! pointer to, as its last argument (`crate::abi`); reads end where they fail.

pub(crate) mod datagrams;
mod sockets;

use sockets::{Failure, Socket};

use crate::abi::{Ret, immediate, option};
use crate::object::Header;
use crate::{list, text};

/// Raises the failure: writes the error's two words, the tag of its variant and a new string
/// of the address it names, to the memory `err` points to.
///
/// # Safety
///
/// `err` points to room for two words.
unsafe fn raise((error, at): Failure, err: u64) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the room for two words.
    unsafe {
        err.write(immediate(error as u64));
        err.add(1).write(text::from(&at));
    }
    Ret::raise(0)
}

/// The word of a result, or its failure raised.
///
/// # Safety
///
/// `err` points to room for an error's two words.
unsafe fn done(result: Result<u64, Failure>, err: u64) -> Ret {
    match result {
        Ok(word) => Ret::ok(word),
        // SAFETY: the caller guarantees the room.
        Err(failure) => unsafe { raise(failure, err) },
    }
}

/// `lookup(host)`: the addresses of `host`, as text.
///
/// # Safety
///
/// `host` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_lookup(_loc: u64, host: u64, err: u64) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the lookup.
    let found = sockets::lookup(unsafe { text::text(&host) });
    let words = found.map(|names| {
        let words: Vec<u64> = names.iter().map(|n| text::from(n)).collect();
        list::from_words(&words, crate::shape::STR) as u64
    });
    // SAFETY: the caller guarantees the room.
    unsafe { done(words, err) }
}

/// `open(host, port)`: a connection to `port` of `host`, by its number.
///
/// # Safety
///
/// `host` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_open(
    _loc: u64,
    host: u64,
    port: i64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the call, and the room.
    unsafe {
        done(
            sockets::connect(text::text(&host), port).map(|id| id as u64),
            err,
        )
    }
}

/// `bind(host, port)`: a listener on `port` of `host`, by its number.
///
/// # Safety
///
/// `host` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_bind(
    _loc: u64,
    host: u64,
    port: i64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the call, and the room.
    unsafe {
        done(
            sockets::listen(text::text(&host), port).map(|id| id as u64),
            err,
        )
    }
}

/// `local_port(id)`: the port that a listener listens on.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_local_port(_loc: u64, id: i64) -> Ret {
    Ret::ok(sockets::with(id, |s| s.port()) as u64)
}

/// `accepted(id)`: the next connection to a listener, by its number.
///
/// # Safety
///
/// `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_accepted(_loc: u64, id: i64, err: u64) -> Ret {
    let accepted = sockets::with(id, Socket::accept).map(|id| id as u64);
    // SAFETY: the caller guarantees the room.
    unsafe { done(accepted, err) }
}

/// `send(id, text)`: writes `text` to a connection.
///
/// # Safety
///
/// `s` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_send(_loc: u64, id: i64, s: u64, err: u64) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the write.
    let bytes = unsafe { text::bytes(&s) };
    let sent = sockets::with(id, |socket| socket.send(bytes)).map(|()| 0);
    // SAFETY: the caller guarantees the room.
    unsafe { done(sent, err) }
}

/// `send_bytes(id, bytes)`: writes `bytes` to a connection.
///
/// # Safety
///
/// `bytes` is a live list of `u8`, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_net_send_bytes(
    _loc: u64,
    id: i64,
    bytes: u64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the list, which outlives the write.
    let bytes = unsafe { list::as_bytes(bytes as *mut Header) };
    let sent = sockets::with(id, |socket| socket.send(bytes)).map(|()| 0);
    // SAFETY: the caller guarantees the room.
    unsafe { done(sent, err) }
}

/// `next_line(id)`: the next line of a connection, or `None` at its end.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_next_line(_loc: u64, id: i64) -> Ret {
    let line = sockets::with(id, Socket::read_line);
    option(line.map(|l| text::from(&l)))
}

/// `next_bytes(id, n)`: at most `n` bytes of a connection, fewer only at its end.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_next_bytes(_loc: u64, id: i64, n: i64) -> Ret {
    let n = u64::try_from(n).unwrap_or(0);
    let bytes = sockets::with(id, |s| s.read_bytes(n));
    Ret::ok(list::of_bytes(&bytes) as u64)
}

/// `rest(id)`: the rest of a connection, until its end, with invalid UTF-8 replaced.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_rest(_loc: u64, id: i64) -> Ret {
    let bytes = sockets::with(id, |s| s.read_bytes(u64::MAX));
    Ret::ok(text::from(&String::from_utf8_lossy(&bytes)))
}

/// `timeout(id, ms)`: gives up on reads and writes that wait longer than `ms` milliseconds.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_timeout(_loc: u64, id: i64, ms: i64) -> Ret {
    sockets::with(id, |s| s.set_timeout(ms));
    Ret::unit()
}

/// `shut(id)`: closes a connection's writing side.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_shut(_loc: u64, id: i64) -> Ret {
    sockets::with(id, Socket::shutdown);
    Ret::unit()
}

/// `closed(id)`: closes a connection or a listener.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_net_closed(_loc: u64, id: i64) -> Ret {
    sockets::with(id, Socket::close);
    Ret::unit()
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_net_lookup,
        stilt_std_net_open,
        stilt_std_net_bind,
        stilt_std_net_local_port,
        stilt_std_net_accepted,
        stilt_std_net_send,
        stilt_std_net_send_bytes,
        stilt_std_net_next_line,
        stilt_std_net_next_bytes,
        stilt_std_net_rest,
        stilt_std_net_timeout,
        stilt_std_net_shut,
        stilt_std_net_closed,
    ]
}
