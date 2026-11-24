//! The framing of an HTTP/1.1 answer: its status line, its headers, and its body, whole by its
//! `Content-Length` or in chunks.

/// An answer: its status, where it redirects, and its body.
#[derive(Debug)]
pub(super) struct Answer {
    pub(super) status: u16,
    pub(super) location: Option<String>,
    pub(super) body: Vec<u8>,
}

/// The answer that `received` holds, all of it.
pub(super) fn answer(received: &[u8]) -> Result<Answer, String> {
    let early = || "the answer ends early".to_owned();
    let end = find(received, b"\r\n\r\n").ok_or_else(early)?;
    let head = String::from_utf8_lossy(&received[..end]);
    let mut lines = head.split("\r\n");
    let status = lines
        .next()
        .and_then(|l| l.split(' ').nth(1))
        .and_then(|s| s.parse().ok())
        .ok_or("a malformed answer")?;
    let mut headers = Vec::new();
    for line in lines {
        if let Some((name, value)) = line.split_once(':') {
            headers.push((name.trim().to_ascii_lowercase(), value.trim().to_owned()));
        }
    }
    let header = |name: &str| {
        headers
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.clone())
    };
    let rest = &received[end + 4..];
    let body = if header("transfer-encoding").is_some_and(|v| v.eq_ignore_ascii_case("chunked")) {
        chunks(rest).ok_or_else(early)?
    } else if let Some(length) = header("content-length").and_then(|v| v.parse::<usize>().ok()) {
        rest.get(..length).ok_or_else(early)?.to_vec()
    } else {
        rest.to_vec()
    };
    Ok(Answer {
        status,
        location: header("location"),
        body,
    })
}

/// The body that the chunks of `data` make, if they end.
fn chunks(mut data: &[u8]) -> Option<Vec<u8>> {
    let mut body = Vec::new();
    loop {
        let line = find(data, b"\r\n")?;
        let size = String::from_utf8_lossy(&data[..line]);
        let size = usize::from_str_radix(size.split(';').next()?.trim(), 16).ok()?;
        data = &data[line + 2..];
        if size == 0 {
            return Some(body);
        }
        body.extend_from_slice(data.get(..size)?);
        data = data.get(size + 2..)?;
    }
}

fn find(data: &[u8], needle: &[u8]) -> Option<usize> {
    data.windows(needle.len()).position(|w| w == needle)
}
