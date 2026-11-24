//! An editor's side of a session with `stilt lsp`, over its stdin and stdout, for the tests of
//! the language server.

use std::io::{BufRead, BufReader, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, ExitStatus, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

/// An editor's side of a session with `stilt lsp`.
pub(crate) struct Editor {
    child: Child,
    input: ChildStdin,
    messages: Receiver<Value>,
    pub(crate) dir: PathBuf,
    next: u64,
    /// What the server said it can do, when it was initialized.
    pub(crate) capabilities: Value,
}

impl Editor {
    /// Starts the server, and opens the folder of a program whose `main.lt` is `source`.
    pub(crate) fn open(name: &str, source: &str) -> Self {
        Self::open_with(name, source, &[])
    }

    /// Starts the server, and opens the folder of a program whose `main.lt` is `source`, beside
    /// the `others`, each a file's path in the folder and its text.
    pub(crate) fn open_with(name: &str, source: &str, others: &[(&str, &str)]) -> Self {
        Self::open_as(name, source, others, &json!({ "capabilities": {} }))
    }

    /// Starts the server as the editor that `client` describes, the parameters of its
    /// `initialize` but its root, and opens the folder of a program as [`Editor::open_with`] does.
    pub(crate) fn open_as(
        name: &str,
        source: &str,
        others: &[(&str, &str)],
        client: &Value,
    ) -> Self {
        let exe = Path::new(env!("CARGO_BIN_EXE_stilt"));
        Self::start(exe, (name, source, others), client)
    }

    /// Starts the server of the executable `exe`, and opens the folder of a program whose
    /// `main.lt` is `source`.
    pub(crate) fn open_from(exe: &Path, name: &str, source: &str) -> Self {
        Self::start(exe, (name, source, &[]), &json!({ "capabilities": {} }))
    }

    fn start(
        exe: &Path,
        (name, source, others): (&str, &str, &[(&str, &str)]),
        client: &Value,
    ) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("lsp")
            .join(name);
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("main.lt"), source).unwrap();
        for (file, text) in others {
            let path = dir.join(file);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        let dir = dir.canonicalize().unwrap();
        let mut child = Command::new(exe)
            .arg("lsp")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("stilt runs");
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        let (send, messages) = channel();
        std::thread::spawn(move || read_all(output, &send));
        let mut editor = Self {
            child,
            input,
            messages,
            dir,
            next: 1,
            capabilities: Value::Null,
        };
        let mut initialize = client.clone();
        initialize["rootUri"] = json!(format!("file://{}", editor.dir.display()));
        let reply = editor.request("initialize", &initialize);
        editor.capabilities = reply["result"]["capabilities"].clone();
        assert_eq!(editor.capabilities["hoverProvider"], true);
        editor.notify("initialized", &json!({}));
        editor
    }

    /// The URI of `main.lt`.
    pub(crate) fn uri(&self) -> String {
        self.uri_of("main.lt")
    }

    /// The URI of a file of the program.
    pub(crate) fn uri_of(&self, file: &str) -> String {
        format!("file://{}", self.dir.join(file).display())
    }

    fn send(&mut self, message: &Value) {
        let body = message.to_string();
        write!(self.input, "Content-Length: {}\r\n\r\n{body}", body.len()).unwrap();
        self.input.flush().unwrap();
    }

    pub(crate) fn notify(&mut self, method: &str, params: &Value) {
        self.send(&json!({ "jsonrpc": "2.0", "method": method, "params": params }));
    }

    /// How the server ended, if it does within `within`.
    pub(crate) fn ended(&mut self, within: Duration) -> Option<ExitStatus> {
        let end = Instant::now() + within;
        while Instant::now() < end {
            if let Ok(Some(status)) = self.child.try_wait() {
                return Some(status);
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        None
    }

    /// The server's reply to a request, its result or its error.
    pub(crate) fn request(&mut self, method: &str, params: &Value) -> Value {
        let id = self.next;
        self.next += 1;
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }));
        self.until(|m| m["id"] == id)
    }

    /// The next message for which `wanted` holds, the others skipped.
    pub(crate) fn until(&self, wanted: impl Fn(&Value) -> bool) -> Value {
        loop {
            let m = self
                .messages
                .recv_timeout(Duration::from_secs(60))
                .expect("the server answers");
            if wanted(&m) {
                return m;
            }
        }
    }

    /// The diagnostics published next, after the buffer is set to `text`.
    pub(crate) fn change(&mut self, text: &str, first: bool) -> Value {
        let document =
            json!({ "uri": self.uri(), "version": 1, "languageId": "stilt", "text": text });
        if first {
            self.notify("textDocument/didOpen", &json!({ "textDocument": document }));
        } else {
            let changes = json!([{ "text": text }]);
            let params = json!({ "textDocument": document, "contentChanges": changes });
            self.notify("textDocument/didChange", &params);
        }
        let published = self.until(|m| m["method"] == "textDocument/publishDiagnostics");
        published["params"]["diagnostics"].clone()
    }

    /// The result of a request about a position of `main.lt`, with more parameters.
    pub(crate) fn at_with(
        &mut self,
        method: &str,
        (line, character): (u64, u64),
        more: &Value,
    ) -> Value {
        let position = json!({ "line": line, "character": character });
        let mut params = json!({ "textDocument": { "uri": self.uri() }, "position": position });
        for (key, value) in more.as_object().into_iter().flatten() {
            params[key] = value.clone();
        }
        self.request(method, &params)["result"].clone()
    }

    /// The result of a request about a position of `main.lt`.
    pub(crate) fn at(&mut self, method: &str, line: u64, character: u64) -> Value {
        self.at_with(method, (line, character), &json!({}))
    }

    /// The result of a request about `main.lt` as a whole, with more parameters.
    pub(crate) fn about(&mut self, method: &str, more: &Value) -> Value {
        let mut params = json!({ "textDocument": { "uri": self.uri() } });
        for (key, value) in more.as_object().into_iter().flatten() {
            params[key] = value.clone();
        }
        self.request(method, &params)["result"].clone()
    }

    pub(crate) fn hover(&mut self, line: u64, character: u64) -> String {
        self.hover_in("main.lt", line, character)
    }

    /// What a hover at a position of a file of the program shows.
    pub(crate) fn hover_in(&mut self, file: &str, line: u64, character: u64) -> String {
        let position = json!({ "line": line, "character": character });
        let params = json!({ "textDocument": { "uri": self.uri_of(file) }, "position": position });
        let shown = &self.request("textDocument/hover", &params)["result"];
        shown["contents"]["value"]
            .as_str()
            .unwrap_or_default()
            .to_owned()
    }

    /// Opens a file of the program, holding `text`, as the editor opens one.
    pub(crate) fn open_document(&mut self, file: &str, text: &str) {
        let document =
            json!({ "uri": self.uri_of(file), "version": 1, "languageId": "stilt", "text": text });
        self.notify("textDocument/didOpen", &json!({ "textDocument": document }));
    }
}

impl Drop for Editor {
    fn drop(&mut self) {
        if self.child.try_wait().is_ok_and(|s| s.is_some()) {
            super::stop_engine(&self.dir, Path::new("."));
            return;
        }
        self.request("shutdown", &Value::Null);
        self.notify("exit", &Value::Null);
        let _ = self.child.wait();
        super::stop_engine(&self.dir, Path::new("."));
    }
}

/// A range of one line, as the protocol writes it.
pub(crate) fn range(line: u64, start: u64, end: u64) -> Value {
    json!({ "start": { "line": line, "character": start }, "end": { "line": line, "character": end } })
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
        if output.read_exact(&mut body).is_err() {
            return;
        }
        if send.send(serde_json::from_slice(&body).unwrap()).is_err() {
            return;
        }
    }
}
