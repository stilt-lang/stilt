//! `lsp`: the edit script replayed through the language server, as an editor sends it, against the
//! engine that `stilt lsp` asks (goals edit-to-diagnostics and one-engine). Each edit's file is
//! opened first, untimed, and each edit is then the file's whole new text, timed from the change
//! sent until the server publishes that file's diagnostics, by the cycles of the server and the
//! engine (Goals, Timing). The server publishes every open buffer's diagnostics after each change,
//! in no order, so before the next edit the harness waits, untimed, until it has published them all:
//! otherwise the next edit's wait could end on a publication of the change before, and count the
//! time of one edit in the next.

use std::io::{BufRead, BufReader, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::Duration;

use serde_json::{Value, json};
use stilt_lsp::uri;

use crate::clock::Clock;
use crate::replay::Project;
use crate::script::{Kind, script};

/// How long the harness waits for the server's answer.
const PATIENCE: Duration = Duration::from_secs(300);

/// An editor's session with `stilt lsp`.
struct Session {
    child: Child,
    input: ChildStdin,
    messages: Receiver<Value>,
}

impl Session {
    /// Starts the server of `stilt` for the program at `root`.
    fn start(stilt: &Path, root: &Path) -> Result<Self, String> {
        let mut child = Command::new(stilt)
            .arg("lsp")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| format!("cannot start {}: {e}", stilt.display()))?;
        let input = child.stdin.take().ok_or("no stdin")?;
        let output = BufReader::new(child.stdout.take().ok_or("no stdout")?);
        let (send, messages) = channel();
        std::thread::spawn(move || read_all(output, &send));
        let mut session = Self {
            child,
            input,
            messages,
        };
        let params = json!({ "rootUri": uri(root), "capabilities": {} });
        session.send(
            &json!({ "jsonrpc": "2.0", "id": 0, "method": "initialize", "params": params }),
        )?;
        session.until(|m| m["id"] == 0)?;
        session.notify("initialized", &json!({}))?;
        Ok(session)
    }

    fn send(&mut self, message: &Value) -> Result<(), String> {
        let body = message.to_string();
        write!(self.input, "Content-Length: {}\r\n\r\n{body}", body.len())
            .and_then(|()| self.input.flush())
            .map_err(|e| format!("cannot write to the server: {e}"))
    }

    fn notify(&mut self, method: &str, params: &Value) -> Result<(), String> {
        self.send(&json!({ "jsonrpc": "2.0", "method": method, "params": params }))
    }

    fn until(&self, wanted: impl Fn(&Value) -> bool) -> Result<Value, String> {
        loop {
            let m = (self.messages.recv_timeout(PATIENCE))
                .map_err(|_| "the server doesn't answer".to_owned())?;
            if wanted(&m) {
                return Ok(m);
            }
        }
    }

    /// Waits for the diagnostics of the file of `uri`.
    fn published(&self, uri: &str) -> Result<(), String> {
        let method = "textDocument/publishDiagnostics";
        self.until(|m| m["method"] == method && m["params"]["uri"] == uri)
            .map(drop)
    }

    /// Waits until the server has sent everything it publishes for the changes so far: it
    /// publishes the diagnostics of every file it holds a buffer of, or has published some for,
    /// in no order, so a file's publication can arrive before those of other files from the same
    /// changes, which the next edit would otherwise take for its own. A request is answered only
    /// once the changes before it are published, so the answer to one comes after them all.
    fn settle(&mut self, uri: &str) -> Result<(), String> {
        let id = "settled";
        let params = json!({ "textDocument": { "uri": uri } });
        let method = "textDocument/foldingRange";
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }))?;
        self.until(|m| m["id"] == id).map(drop)
    }

    fn end(mut self) {
        let _ = self.send(&json!({ "jsonrpc": "2.0", "id": 1, "method": "shutdown" }));
        let _ = self.until(|m| m["id"] == 1);
        let _ = self.notify("exit", &Value::Null);
        let _ = self.child.wait();
    }
}

fn read_all(mut output: impl BufRead, send: &Sender<Value>) {
    loop {
        let mut length = 0;
        loop {
            let mut line = String::new();
            if output.read_line(&mut line).unwrap_or(0) == 0 {
                return;
            }
            match line.trim().split_once(':') {
                Some((name, n)) if name.eq_ignore_ascii_case("content-length") => {
                    length = n.trim().parse().unwrap_or(0);
                }
                _ if line.trim().is_empty() => break,
                _ => {}
            }
        }
        let mut body = vec![0; length];
        let parsed = output
            .read_exact(&mut body)
            .ok()
            .and_then(|()| serde_json::from_slice(&body).ok());
        let Some(m) = parsed else {
            return;
        };
        if send.send(m).is_err() {
            return;
        }
    }
}

/// Replays the edit script on the project at `root` through the server of `stilt`, and gives
/// each edit's kind and time.
pub(crate) fn replay(
    stilt: &Path,
    root: &Path,
    pairs: usize,
    seed: u64,
) -> Result<Vec<(Kind, Duration)>, String> {
    let root = root
        .canonicalize()
        .map_err(|e| format!("cannot open {}: {e}", root.display()))?;
    let project = Project::load(&root)?;
    let modules: Vec<String> = project.modules.iter().map(|m| m.join(".")).collect();
    let edits = script(&project.texts, &modules, pairs, seed);
    let files: Vec<PathBuf> = project.paths.iter().map(|p| root.join(p)).collect();
    let _ = Command::new(stilt)
        .args(["engine", "--stop"])
        .arg(&root)
        .output();
    let mut session = Session::start(stilt, &root)?;
    let mut open = vec![false; files.len()];
    let mut times = Vec::new();
    for edit in &edits {
        let uri = uri(&files[edit.file]);
        if !open[edit.file] {
            open[edit.file] = true;
            let document = json!({ "uri": uri, "languageId": "stilt", "version": 0, "text": project.texts[edit.file] });
            session.notify("textDocument/didOpen", &json!({ "textDocument": document }))?;
            session.published(&uri)?;
            session.settle(&uri)?;
        }
        let changes = json!([{ "text": edit.text }]);
        let params = json!({ "textDocument": { "uri": uri, "version": times.len() + 1 }, "contentChanges": changes });
        let start = Clock::of_client(session.child.id(), &root);
        session.notify("textDocument/didChange", &params)?;
        session.published(&uri)?;
        times.push((edit.kind, start.elapsed()));
        session.settle(&uri)?;
    }
    session.end();
    let _ = Command::new(stilt)
        .args(["engine", "--stop"])
        .arg(&root)
        .output();
    Ok(times)
}
