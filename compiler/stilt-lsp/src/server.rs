//! The server: it reads the editor's messages, keeps the text of the buffers the editor has
//! open, and answers from the backend. A thread reads the messages as they come, so that
//! changes that arrive together are all taken in before the diagnostics are published once,
//! which they are before any request after them is answered.

use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Sender};

use serde_json::{Value, json};

use crate::jobs::{Finished, Jobs};
use crate::text::{offset, path, uri};
use crate::{Backend, Diagnostic, convert, transport};

/// What handling a message leaves to do.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Nothing,
    /// A buffer changed, so the diagnostics are published again.
    Changed,
    Exit,
}

/// What the server's loop takes in: the editor's messages, as a thread reads them, and the
/// jobs of code lenses that end.
pub(crate) enum Incoming {
    Message(Value),
    /// The editor closed the server's input.
    Closed,
    Failed(io::Error),
    Finished(Finished),
}

/// A buffer the editor has open.
struct Document {
    /// The URI the editor names it by.
    uri: String,
    text: String,
}

pub(crate) struct Server<'b, W> {
    output: W,
    pub(crate) backend: &'b mut dyn Backend,
    /// The open buffers, by their files' canonical paths.
    documents: HashMap<PathBuf, Document>,
    /// The diagnostics last published, by file, with their fixes for code actions.
    pub(crate) published: HashMap<PathBuf, Vec<Diagnostic>>,
    /// What the editor can do, from its `initialize`.
    pub(crate) client: convert::Client,
    /// The code lenses' jobs and their results.
    pub(crate) jobs: Jobs,
    /// Where a job sends what it gave once it ends.
    pub(crate) incoming: Sender<Incoming>,
}

/// Serves the editor that writes to `input` and reads `output`, with `backend`, until the
/// editor sends `exit` or closes `input`.
///
/// # Errors
///
/// When a message can't be read or written.
pub fn serve<R, W>(input: R, output: W, backend: &mut dyn Backend) -> io::Result<()>
where
    R: BufRead + Send + 'static,
    W: Write,
{
    let (send, messages) = mpsc::channel();
    let reader = send.clone();
    std::thread::spawn(move || {
        let mut input = input;
        loop {
            let (incoming, last) = match transport::read(&mut input) {
                Ok(Some(message)) => (Incoming::Message(message), false),
                Ok(None) => (Incoming::Closed, true),
                Err(e) => (Incoming::Failed(e), true),
            };
            if reader.send(incoming).is_err() || last {
                break;
            }
        }
    });
    let mut server = Server {
        output,
        backend,
        documents: HashMap::new(),
        published: HashMap::new(),
        client: convert::Client::default(),
        jobs: Jobs::default(),
        incoming: send,
    };
    while let Ok(incoming) = messages.recv() {
        let mut next = Some(incoming);
        let mut changed = false;
        while let Some(incoming) = next {
            match incoming {
                Incoming::Message(message) => match server.handle(&message)? {
                    Step::Exit => return Ok(()),
                    Step::Changed => changed = true,
                    Step::Nothing => {}
                },
                Incoming::Finished(finished) => server.finished(&finished)?,
                Incoming::Closed => return server.flush(changed),
                Incoming::Failed(e) => return Err(e),
            }
            next = match messages.try_recv() {
                Ok(Incoming::Message(message)) if changed && message.get("id").is_some() => {
                    server.flush(changed)?;
                    changed = false;
                    Some(Incoming::Message(message))
                }
                Ok(incoming) => Some(incoming),
                Err(_) => None,
            };
        }
        server.flush(changed)?;
    }
    Ok(())
}

impl<W: Write> Server<'_, W> {
    fn flush(&mut self, changed: bool) -> io::Result<()> {
        if changed { self.publish() } else { Ok(()) }
    }

    pub(crate) fn send(&mut self, message: &Value) -> io::Result<()> {
        transport::write(&mut self.output, message)
    }

    /// Writes `message` to the editor's log, as an error.
    fn log(&mut self, message: &str) -> io::Result<()> {
        let params = json!({ "type": 1, "message": format!("stilt: {message}") });
        self.send(&json!({ "jsonrpc": "2.0", "method": "window/logMessage", "params": params }))
    }

    fn handle(&mut self, message: &Value) -> io::Result<Step> {
        let Some(method) = message["method"].as_str() else {
            return Ok(Step::Nothing);
        };
        let params = &message["params"];
        let Some(id) = message.get("id") else {
            return self.notification(method, params);
        };
        let reply = match self.request(method, params) {
            Ok(result) => json!({ "jsonrpc": "2.0", "id": id, "result": result }),
            Err((code, error)) => {
                let error = json!({ "code": code, "message": error });
                json!({ "jsonrpc": "2.0", "id": id, "error": error })
            }
        };
        self.send(&reply)?;
        Ok(Step::Nothing)
    }

    fn notification(&mut self, method: &str, params: &Value) -> io::Result<Step> {
        let document = &params["textDocument"];
        let file = || path(document["uri"].as_str().unwrap_or_default()).map(|p| canonical(&p));
        let text = match method {
            "exit" => return Ok(Step::Exit),
            // A file changed on disk, or was made or removed: the engine reads the disk again
            // as it answers, so the diagnostics are published again.
            "workspace/didChangeWatchedFiles" => {
                self.jobs.changed();
                return Ok(Step::Changed);
            }
            "textDocument/didOpen" => document["text"].as_str().map(str::to_owned),
            "textDocument/didChange" => {
                self.jobs.changed();
                params["contentChanges"]
                    .as_array()
                    .and_then(|changes| changes.last())
                    .and_then(|change| change["text"].as_str())
                    .map(str::to_owned)
            }
            "textDocument/didClose" => None,
            _ => return Ok(Step::Nothing),
        };
        let Some(file) = file() else {
            return Ok(Step::Nothing);
        };
        let held = self.backend.buffer(&file, text.as_deref());
        match text {
            Some(text) => {
                let uri = document["uri"].as_str().unwrap_or_default().to_owned();
                self.documents.insert(file, Document { uri, text });
            }
            None => {
                self.documents.remove(&file);
            }
        }
        if let Err(e) = held {
            self.log(&e)?;
        }
        Ok(Step::Changed)
    }

    /// The file of a request's document, with its URI and its text.
    pub(crate) fn document(&self, params: &Value) -> (PathBuf, String, String) {
        let uri = params["textDocument"]["uri"].as_str().unwrap_or_default();
        let file = path(uri).map(|p| canonical(&p)).unwrap_or_default();
        let (_, text) = self.text_of(&file);
        (file, uri.to_owned(), text)
    }

    /// The file and the byte of a request's position.
    pub(crate) fn at(&self, params: &Value) -> (PathBuf, u32) {
        let (file, _, text) = self.document(params);
        (file, byte(offset(&text, &params["position"])))
    }

    /// The URI and the text of a file: its buffer's, if the editor has it open, and
    /// otherwise the disk's.
    pub(crate) fn text_of(&self, file: &Path) -> (String, String) {
        match self.documents.get(file) {
            Some(d) => (d.uri.clone(), d.text.clone()),
            None => (uri(file), std::fs::read_to_string(file).unwrap_or_default()),
        }
    }

    /// Publishes the diagnostics of every file that has any, and none for each open buffer
    /// and each file that had some and has none now.
    fn publish(&mut self) -> io::Result<()> {
        let files = match self.backend.diagnostics() {
            Ok(files) => files,
            Err(e) => return self.log(&e),
        };
        let mut now = HashSet::new();
        let mut published = HashMap::new();
        for f in files {
            let (uri, text) = self.text_of(&f.path);
            let list: Vec<Value> = (f.diagnostics.iter())
                .map(|d| convert::diagnostic(&text, &uri, d))
                .collect();
            self.notify_diagnostics(&uri, &list)?;
            now.insert(f.path.clone());
            published.insert(f.path, f.diagnostics);
        }
        let gone: Vec<PathBuf> = (self.published.keys().chain(self.documents.keys()))
            .filter(|p| !now.contains(*p))
            .cloned()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        for file in gone {
            let (uri, _) = self.text_of(&file);
            self.notify_diagnostics(&uri, &[])?;
        }
        self.published = published;
        Ok(())
    }

    fn notify_diagnostics(&mut self, uri: &str, diagnostics: &[Value]) -> io::Result<()> {
        let params = json!({ "uri": uri, "diagnostics": diagnostics });
        let method = "textDocument/publishDiagnostics";
        self.send(&json!({ "jsonrpc": "2.0", "method": method, "params": params }))
    }
}

/// The folder the editor opened: its root URI, its first workspace folder, or its root path,
/// and otherwise the current directory.
pub(crate) fn root(params: &Value) -> PathBuf {
    let uri = params["rootUri"]
        .as_str()
        .or_else(|| params["workspaceFolders"][0]["uri"].as_str());
    uri.and_then(path)
        .or_else(|| params["rootPath"].as_str().map(PathBuf::from))
        .unwrap_or_else(|| PathBuf::from("."))
}

/// A byte of a file, which is under 4 GiB.
pub(crate) fn byte(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

fn canonical(path: &Path) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}
