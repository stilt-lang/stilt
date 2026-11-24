//! The messages of the protocol on a stream: each a header of `Content-Length`, a blank line,
//! then that many bytes of JSON.

use std::io::{self, BufRead, Read, Write};

use serde_json::Value;

/// The next message, or `None` at the end of the stream.
///
/// # Errors
///
/// When the stream can't be read, or holds a message without a length or that isn't JSON.
pub(crate) fn read(input: &mut impl BufRead) -> io::Result<Option<Value>> {
    let mut length = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':')
            && name.eq_ignore_ascii_case("content-length")
        {
            length = value.trim().parse::<usize>().ok();
        }
    }
    let length = length.ok_or_else(|| io::Error::other("a message without a length"))?;
    // The body grows as its bytes arrive, so that a length past what the stream holds fails
    // when the stream ends rather than when its room can't be had.
    let mut body = Vec::new();
    input.by_ref().take(length as u64).read_to_end(&mut body)?;
    if body.len() < length {
        return Err(io::ErrorKind::UnexpectedEof.into());
    }
    serde_json::from_slice(&body)
        .map(Some)
        .map_err(io::Error::other)
}

/// Writes a message.
///
/// # Errors
///
/// When the stream can't be written.
pub(crate) fn write(output: &mut impl Write, message: &Value) -> io::Result<()> {
    let body = message.to_string();
    write!(output, "Content-Length: {}\r\n\r\n{body}", body.len())?;
    output.flush()
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::{read, write};

    #[test]
    fn a_length_past_the_stream_fails_without_taking_its_room() {
        let mut input = &b"Content-Length: 144410973884777480\r\n\r\n{}"[..];
        let error = read(&mut input).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::UnexpectedEof);
    }

    #[test]
    fn a_message_reads_as_it_was_written() {
        let mut bytes = Vec::new();
        let message = json!({"jsonrpc": "2.0", "method": "exit"});
        write(&mut bytes, &message).unwrap();
        assert!(bytes.starts_with(b"Content-Length: 33\r\n\r\n"));
        let mut input = bytes.as_slice();
        assert_eq!(read(&mut input).unwrap(), Some(message));
        assert_eq!(read(&mut input).unwrap(), None);
    }
}
