//! A repository that `HOST/PATH` names, reached at `https://HOST/PATH` by git's smart HTTP
//! protocol (packages.fetching): its refs from `info/refs`, then, for a tag, a pack of the
//! tag's commit alone from `git-upload-pack`, read by [`super::stream`].

use super::{Id, files_at, parse_id, stream, to_hex};
use crate::hash::Files;
use crate::net;

/// A repository over HTTPS, with its tags as it advertised them.
#[derive(Debug)]
pub(crate) struct Remote {
    url: String,
    tags: Vec<(String, Id)>,
}

impl Remote {
    /// The repository at `url`, with its refs.
    ///
    /// # Errors
    ///
    /// A message for people, when it can't be reached or holds no repository.
    pub(crate) fn open(url: &str) -> Result<Self, String> {
        let refs = net::get(&format!("{url}/info/refs?service=git-upload-pack"))?;
        if refs.status != 200 {
            return Err(format!("it answers {} for its refs", refs.status));
        }
        let mut tags = Vec::new();
        for line in lines(&refs.body)?.into_iter().flatten() {
            let line = line.split(|&b| b == 0).next().unwrap_or_default();
            let text = String::from_utf8_lossy(line);
            let Some((hex, name)) = text.trim_end().split_once(' ') else {
                continue;
            };
            if let (Some(id), Some(tag)) = (parse_id(hex), name.strip_prefix("refs/tags/"))
                && !tag.ends_with("^{}")
            {
                tags.push((tag.to_owned(), id));
            }
        }
        tags.sort();
        Ok(Self {
            url: url.to_owned(),
            tags,
        })
    }

    /// The repository's tags, each with the object it names.
    pub(crate) fn tags(&self) -> Vec<(String, Id)> {
        self.tags.clone()
    }

    /// The files that building the package at the tag `id` reads, from a pack of its commit
    /// alone, or `None` when its tree holds no `stilt.toml`.
    ///
    /// # Errors
    ///
    /// A message for people, when the pack can't be had or read.
    pub(crate) fn files_at(&self, id: Id) -> Result<Option<Files>, String> {
        let mut request = pkt(&format!(
            "want {} ofs-delta shallow agent=stilt\n",
            to_hex(&id)
        ));
        request.extend(pkt("deepen 1\n"));
        request.extend(b"0000");
        request.extend(pkt("done\n"));
        let url = format!("{}/git-upload-pack", self.url);
        let response = net::post(&url, "application/x-git-upload-pack-request", &request)?;
        if response.status != 200 {
            return Err(format!("it answers {} for a pack", response.status));
        }
        let pack = after_acknowledgment(&response.body)?;
        files_at(&stream::read(pack)?, id)
    }
}

/// A line of git's protocol: its length in four hexadecimal digits, then its text.
fn pkt(text: &str) -> Vec<u8> {
    format!("{:04x}{text}", text.len() + 4).into_bytes()
}

/// The length of the line of git's protocol at the start of `data`: `None` for a flush.
fn length(data: &[u8]) -> Result<Option<usize>, String> {
    let hex = std::str::from_utf8(data.get(..4).ok_or("the repository's answer ends early")?)
        .map_err(|_| "a malformed answer")?;
    let n = usize::from_str_radix(hex, 16).map_err(|_| "a malformed answer")?;
    Ok((n >= 4).then_some(n))
}

/// The lines of `data`, `None` for each flush.
fn lines(data: &[u8]) -> Result<Vec<Option<&[u8]>>, String> {
    let mut found = Vec::new();
    let mut at = 0;
    while at < data.len() {
        match length(&data[at..])? {
            None => {
                found.push(None);
                at += 4;
            }
            Some(n) => {
                found.push(Some(data.get(at + 4..at + n).ok_or("a malformed answer")?));
                at += n;
            }
        }
    }
    Ok(found)
}

/// The pack that follows the shallow lines and the `NAK` or `ACK` of an answer to a request.
fn after_acknowledgment(data: &[u8]) -> Result<&[u8], String> {
    let mut at = 0;
    loop {
        match length(&data[at..])? {
            None => at += 4,
            Some(n) => {
                let line = data.get(at + 4..at + n).ok_or("a malformed answer")?;
                at += n;
                if line.starts_with(b"NAK") || line.starts_with(b"ACK") {
                    return Ok(&data[at..]);
                }
                if line.starts_with(b"ERR") {
                    return Err(String::from_utf8_lossy(line).trim().to_owned());
                }
            }
        }
    }
}
