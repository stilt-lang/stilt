//! What a command and its engine say to each other. A command sends a request and reads one
//! reply, but for `run`, which then sends a look each time it looks at the program's files and
//! reads the update the engine answers with, until the program ends.
//!
//! Each message is a frame: a magic word, the length of the message, and the message in
//! postcard's form, which writes each value as serde gives it, with integers in as few bytes
//! as their values take and no names. The MIR that a run receives is most of what flows: for
//! the 100K-line project, 1.7 MB, a seventh of what JSON takes, written in 4 ms and read in
//! 9. The magic word ends with a newline, so that a peer that speaks another protocol and
//! reads lines gives up at once rather than wait, and a frame without it isn't read. A request
//! names its compiler before its command, so that an engine reads which compiler asks before
//! it reads a command that another build of the compiler may write differently.

use std::io::{self, Read as _, Write as _};
use std::os::unix::net::UnixStream;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use super::Command;
use crate::repl::Opened;
use crate::report::Report;
use crate::run::Start;
use crate::test::Plan;

/// What each frame begins with.
const MAGIC: [u8; 8] = *b"stilt\0\0\n";

/// A command, from a compiler.
#[derive(Debug)]
pub(super) struct Request {
    /// Which compiler asks (`super::place::identity`).
    pub(super) identity: String,
    pub(super) command: Command,
}

/// What an engine answers. It answers nothing to another compiler, whose command it can't
/// read, and closes the connection.
#[derive(Debug, Serialize, Deserialize)]
pub(super) enum Reply {
    /// The command's report.
    Report(Report),
    /// What starting a run needs, after which the connection takes the run's looks.
    Started(Start),
    /// What a session of the REPL reports first, after which the connection takes its asks.
    Opened(Opened),
    /// What running the program's tests needs, after which the connection takes their
    /// results, one for each case.
    Tested(Plan),
    /// The results of the tests are remembered.
    Recorded,
    /// The queries run since they were last asked for.
    Ran(Vec<String>),
    /// The answer to the language server, from the engine of this process id: a new one
    /// holds none of the buffers that the last one held.
    Language { engine: u32, answer: super::Answer },
    /// Why the engine can't answer, so that the command runs in its own process.
    Elsewhere(String),
    /// The engine stops.
    Stopping,
}

/// A run's look at the program's files, which the engine answers with the update since the
/// last (`crate::run::Update`).
#[derive(Debug, Serialize, Deserialize)]
pub(super) struct Look;

/// Writes `value` as a frame.
pub(super) fn send<T: Serialize>(stream: &UnixStream, value: &T) -> io::Result<()> {
    write_frame(
        stream,
        &postcard::to_stdvec(value).map_err(io::Error::other)?,
    )
}

/// Reads a frame, as a `T`.
pub(super) fn receive<T: DeserializeOwned>(stream: &UnixStream) -> io::Result<T> {
    postcard::from_bytes(&read_frame(stream)?).map_err(io::Error::other)
}

/// Writes a request: the compiler's identity, then its command.
pub(super) fn send_request(stream: &UnixStream, request: &Request) -> io::Result<()> {
    let mut bytes = postcard::to_stdvec(&request.identity).map_err(io::Error::other)?;
    bytes.extend(postcard::to_stdvec(&request.command).map_err(io::Error::other)?);
    write_frame(stream, &bytes)
}

/// Reads a request: the identity of the compiler that sends it, and its command, which only
/// a compiler of `identity` is known to write as this one reads it, and so is read only then.
pub(super) fn receive_request(
    stream: &UnixStream,
    identity: &str,
) -> io::Result<Result<Command, String>> {
    let bytes = read_frame(stream)?;
    let (theirs, rest) = postcard::take_from_bytes::<String>(&bytes).map_err(io::Error::other)?;
    if theirs != identity {
        return Ok(Err(theirs));
    }
    Ok(Ok(postcard::from_bytes(rest).map_err(io::Error::other)?))
}

fn write_frame(mut stream: &UnixStream, bytes: &[u8]) -> io::Result<()> {
    let len = u64::try_from(bytes.len()).map_err(io::Error::other)?;
    let mut head = [0; 16];
    head[..8].copy_from_slice(&MAGIC);
    head[8..].copy_from_slice(&len.to_le_bytes());
    stream.write_all(&head)?;
    stream.write_all(bytes)?;
    stream.flush()
}

fn read_frame(mut stream: &UnixStream) -> io::Result<Vec<u8>> {
    let mut head = [0; 16];
    stream.read_exact(&mut head)?;
    if head[..8] != MAGIC {
        // The one error of this kind, which tells a peer of another protocol.
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "the peer speaks another protocol",
        ));
    }
    let len = u64::from_le_bytes(head[8..].try_into().map_err(io::Error::other)?);
    let mut bytes = vec![0; usize::try_from(len).map_err(io::Error::other)?];
    stream.read_exact(&mut bytes)?;
    Ok(bytes)
}
