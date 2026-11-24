//! The sockets of `std.net` (std.net, std.net-streams, std.net-listeners and std.net-datagrams):
//! the addresses of a host, TCP connections, read through a buffer and written whole, listeners,
//! and UDP sockets, each known by its number. A failure names the address that a socket was opened
//! with, the peer that a listener accepted, or the address that a datagram was sent to.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{IpAddr, Shutdown, SocketAddr, TcpListener, TcpStream, ToSocketAddrs, UdpSocket};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use crate::std_io::IoError;

/// Why a socket didn't open, or a write failed: the variant of `IoError`, and the address it
/// names.
pub(super) type Failure = (IoError, String);

/// What a socket is: a connection, with the buffer it reads through, a listener, a UDP socket,
/// with the sender of the datagram it received last, or none of them once it is closed.
enum Kind {
    Stream(BufReader<TcpStream>),
    Listener(TcpListener),
    Datagrams(UdpSocket, String),
    Closed,
}

/// The most bytes of a datagram that a socket receives: the most that UDP carries.
const DATAGRAM: usize = 65536;

/// A socket, with the address that its failures name.
pub(super) struct Socket {
    address: String,
    kind: Kind,
}

/// The sockets, by their numbers, each behind its own lock, so that a read from one waits for
/// no other.
static SOCKETS: LazyLock<Mutex<HashMap<i64, Arc<Mutex<Socket>>>>> = LazyLock::new(Mutex::default);

/// The number of the latest socket.
static COUNT: AtomicI64 = AtomicI64::new(0);

fn locked<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

fn register(address: String, kind: Kind) -> i64 {
    let id = COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    let socket = Arc::new(Mutex::new(Socket { address, kind }));
    locked(&SOCKETS).insert(id, socket);
    id
}

/// Calls `f` on the socket of number `id`.
pub(super) fn with<T>(id: i64, f: impl FnOnce(&mut Socket) -> T) -> T {
    let socket = Arc::clone(
        locked(&SOCKETS)
            .get(&id)
            .expect("a socket that `std.net` opened"),
    );
    let mut socket = locked(&socket);
    f(&mut socket)
}

/// The addresses of `host`, in the system's order, each once; none for an empty name or one
/// that holds NUL.
fn addresses(host: &str) -> Vec<IpAddr> {
    if host.is_empty() || host.contains('\0') {
        return Vec::new();
    }
    let mut found: Vec<IpAddr> = Vec::new();
    for a in (host, 0).to_socket_addrs().into_iter().flatten() {
        if !found.contains(&a.ip()) {
            found.push(a.ip());
        }
    }
    found
}

/// `lookup(host)`: the addresses of `host`, as text.
pub(super) fn lookup(host: &str) -> Result<Vec<String>, Failure> {
    // WebAssembly opens no socket (wasm.what-std-reads).
    if cfg!(target_os = "wasi") {
        return Err((IoError::PermissionDenied, host.to_owned()));
    }
    if host.contains('\0') {
        return Err((IoError::Other, host.to_owned()));
    }
    let found = addresses(host);
    if found.is_empty() {
        return Err((IoError::NotFound, host.to_owned()));
    }
    Ok(found.iter().map(ToString::to_string).collect())
}

/// Opens a socket on each address of `host` in turn with `open`, until one opens, and gives
/// the first, or the failure of the last attempt.
fn first_of(
    host: &str,
    port: i64,
    open: impl Fn(SocketAddr) -> std::io::Result<Kind>,
) -> Result<i64, Failure> {
    let at = format!("{host}:{port}");
    if cfg!(target_os = "wasi") {
        return Err((IoError::PermissionDenied, at));
    }
    let Ok(port) = u16::try_from(port) else {
        return Err((IoError::Other, at));
    };
    if host.contains('\0') {
        return Err((IoError::Other, at));
    }
    let mut last = IoError::NotFound;
    for ip in addresses(host) {
        match open(SocketAddr::new(ip, port)) {
            Ok(kind) => return Ok(register(at, kind)),
            Err(e) => last = IoError::of(&e),
        }
    }
    Err((last, at))
}

/// `open(host, port)`: a connection to `port` of `host`.
pub(super) fn connect(host: &str, port: i64) -> Result<i64, Failure> {
    first_of(host, port, |a| {
        TcpStream::connect(a).map(|s| Kind::Stream(BufReader::new(s)))
    })
}

/// `bind(host, port)`: a listener on `port` of `host`.
pub(super) fn listen(host: &str, port: i64) -> Result<i64, Failure> {
    first_of(host, port, |a| TcpListener::bind(a).map(Kind::Listener))
}

/// `datagrams(host, port)`: a UDP socket bound to `port` of `host`.
pub(super) fn datagrams(host: &str, port: i64) -> Result<i64, Failure> {
    first_of(host, port, |a| {
        UdpSocket::bind(a).map(|s| Kind::Datagrams(s, String::new()))
    })
}

/// The address `host:port` that a datagram is sent to, and the socket addresses of `host`, or the
/// failure that names it: `Other` for a port outside 0 to 65535 or a host that holds NUL, and
/// `NotFound` for a host without an address.
fn destinations(host: &str, port: i64) -> Result<Vec<SocketAddr>, Failure> {
    let at = || format!("{host}:{port}");
    let port = u16::try_from(port).map_err(|_| (IoError::Other, at()))?;
    if host.contains('\0') {
        return Err((IoError::Other, at()));
    }
    let found: Vec<SocketAddr> = (addresses(host).into_iter())
        .map(|ip| SocketAddr::new(ip, port))
        .collect();
    if found.is_empty() {
        return Err((IoError::NotFound, at()));
    }
    Ok(found)
}

impl Socket {
    fn other(&self) -> Failure {
        (IoError::Other, self.address.clone())
    }

    /// The port that a listener listens on, or a UDP socket is bound to, or 0.
    pub(super) fn port(&self) -> i64 {
        let local = match &self.kind {
            Kind::Listener(l) => l.local_addr(),
            Kind::Datagrams(s, _) => s.local_addr(),
            _ => return 0,
        };
        local.map_or(0, |a| i64::from(a.port()))
    }

    /// Sends `bytes` as one datagram to `port` of `host`, to each of its addresses in turn until
    /// one takes it, or gives the failure that names `host:port`: the system's refusal of the last
    /// address, `Other` once the socket is closed.
    pub(super) fn send_to(&mut self, bytes: &[u8], host: &str, port: i64) -> Result<(), Failure> {
        let at = format!("{host}:{port}");
        let found = destinations(host, port)?;
        let Kind::Datagrams(socket, _) = &self.kind else {
            return Err((IoError::Other, at));
        };
        let mut last = IoError::Other;
        for a in found {
            match socket.send_to(bytes, a) {
                Ok(_) => return Ok(()),
                Err(e) => last = IoError::of(&e),
            }
        }
        Err((last, at))
    }

    /// The bytes of the next datagram a UDP socket receives, whose sender it keeps, or `None`
    /// when the wait gives up, fails, or the socket is closed.
    pub(super) fn receive(&mut self) -> Option<Vec<u8>> {
        let Kind::Datagrams(socket, from) = &mut self.kind else {
            return None;
        };
        let mut bytes = vec![0; DATAGRAM];
        let (n, peer) = socket.recv_from(&mut bytes).ok()?;
        bytes.truncate(n);
        *from = peer.to_string();
        Some(bytes)
    }

    /// The address of the sender of the datagram a UDP socket received last, `ip:port`.
    pub(super) fn sender(&self) -> String {
        match &self.kind {
            Kind::Datagrams(_, from) => from.clone(),
            _ => String::new(),
        }
    }

    /// Waits for a connection to a listener, and gives its number.
    pub(super) fn accept(&mut self) -> Result<i64, Failure> {
        let Kind::Listener(listener) = &self.kind else {
            return Err(self.other());
        };
        match listener.accept() {
            Ok((stream, peer)) => Ok(register(
                peer.to_string(),
                Kind::Stream(BufReader::new(stream)),
            )),
            Err(_) => Err(self.other()),
        }
    }

    /// Writes `bytes` whole to a connection.
    pub(super) fn send(&mut self, bytes: &[u8]) -> Result<(), Failure> {
        let other = self.other();
        let Kind::Stream(reader) = &mut self.kind else {
            return Err(other);
        };
        let stream = reader.get_mut();
        stream
            .write_all(bytes)
            .and_then(|()| stream.flush())
            .map_err(|_| other)
    }

    fn reader(&mut self) -> Option<&mut BufReader<TcpStream>> {
        match &mut self.kind {
            Kind::Stream(reader) => Some(reader),
            _ => None,
        }
    }

    /// The next line of a connection, without its `\n` and a `\r` before it, or `None` at its
    /// end or where a read fails.
    pub(super) fn read_line(&mut self) -> Option<String> {
        let reader = self.reader()?;
        let mut line = Vec::new();
        if reader.read_until(b'\n', &mut line).unwrap_or(0) == 0 {
            return None;
        }
        if line.last() == Some(&b'\n') {
            line.pop();
        }
        if line.last() == Some(&b'\r') {
            line.pop();
        }
        Some(String::from_utf8_lossy(&line).into_owned())
    }

    /// At most `n` bytes, fewer only at the end of the connection or where a read fails.
    pub(super) fn read_bytes(&mut self, n: u64) -> Vec<u8> {
        let mut bytes = Vec::new();
        if let Some(reader) = self.reader() {
            let _ = reader.take(n).read_to_end(&mut bytes);
        }
        bytes
    }

    /// Gives up on reads and writes that wait longer than `ms` milliseconds, or on none.
    pub(super) fn set_timeout(&mut self, ms: i64) {
        let limit = u64::try_from(ms)
            .ok()
            .filter(|&ms| ms > 0)
            .map(Duration::from_millis);
        if let Some(reader) = self.reader() {
            let _ = reader.get_ref().set_read_timeout(limit);
            let _ = reader.get_ref().set_write_timeout(limit);
        } else if let Kind::Datagrams(socket, _) = &self.kind {
            let _ = socket.set_read_timeout(limit);
            let _ = socket.set_write_timeout(limit);
        }
    }

    /// Closes a connection's writing side.
    pub(super) fn shutdown(&mut self) {
        if let Some(reader) = self.reader() {
            let _ = reader.get_ref().shutdown(Shutdown::Write);
        }
    }

    /// Closes the socket.
    pub(super) fn close(&mut self) {
        self.kind = Kind::Closed;
    }
}
