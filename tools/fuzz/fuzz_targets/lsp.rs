//! The language server takes any session of an editor's messages without panicking, with a
//! backend whose answers come from the input too (`lsp/fake.rs`). The input gives a document's
//! text and then the messages, each framed as an editor frames it: opening and changing
//! buffers, and asking at positions that may be past the last line, inside a character, or not
//! numbers at all. Each request gets one answer, every message the server writes is framed
//! JSON, and only a broken frame, which the session may end with, fails it.

#![no_main]

use std::io::Cursor;

use libfuzzer_sys::fuzz_target;
use serde::Deserialize as _;
use serde_json::{Value, json};

#[path = "lsp/bytes.rs"]
mod bytes;
#[path = "lsp/fake.rs"]
mod fake;

use bytes::Bytes;

/// The URIs the editor names its documents by, those of the backend's paths: one in ASCII, one
/// whose escapes stand for characters of two and four bytes, one in a folder, and one that
/// isn't a file's.
const URIS: [&str; 4] = [
    "file:///stilt-fuzz/main.lt",
    "file:///stilt-fuzz/%C3%A9t%C3%A9%20%F0%9F%98%80.lt",
    "file:///stilt-fuzz/lib/other.lt",
    "untitled:Untitled-1",
];

/// The most messages of one session, which keeps each input quick.
const MESSAGES: usize = 48;

/// The requests that ask about a document, each at a position, over a range, or of it whole.
const AT: [&str; 9] = [
    "textDocument/hover",
    "textDocument/definition",
    "textDocument/declaration",
    "textDocument/typeDefinition",
    "textDocument/completion",
    "textDocument/signatureHelp",
    "textDocument/documentHighlight",
    "textDocument/prepareRename",
    "stilt/whereabouts",
];
const OVER: [&str; 2] = ["textDocument/inlayHint", "textDocument/codeAction"];
const WHOLE: [&str; 5] = [
    "textDocument/semanticTokens/full",
    "textDocument/foldingRange",
    "textDocument/codeLens",
    "textDocument/formatting",
    "textDocument/documentSymbol",
];

/// The session an editor writes, built from the input.
struct Session<'a> {
    bytes: Bytes<'a>,
    /// The document's text the input starts with.
    text: String,
    stream: Vec<u8>,
    /// The requests framed before the session ended.
    requests: usize,
    /// Whether the session ended with a broken frame, which fails the server.
    broken: bool,
    /// Whether it ended, with `exit` or a broken frame, after which nothing is read.
    ended: bool,
}

impl<'a> Session<'a> {
    fn new(data: &'a [u8]) -> Self {
        let mut bytes = Bytes::new(data);
        let length = usize::from(bytes.u16()) % 2048;
        let text = String::from_utf8_lossy(bytes.take(length)).into_owned();
        Session {
            bytes,
            text,
            stream: Vec::new(),
            requests: 0,
            broken: false,
            ended: false,
        }
    }

    fn write(&mut self) {
        for _ in 0..MESSAGES {
            if self.ended || self.bytes.done() {
                break;
            }
            self.message();
        }
    }

    /// Frames `body` with its length, as an editor does, its header's name in either case and
    /// with a content type or without.
    fn frame(&mut self, body: &Value) {
        let body = body.to_string();
        let name = if self.bytes.below(8) == 0 {
            "content-length"
        } else {
            "Content-Length"
        };
        let mut header = format!("{name}: {}\r\n", body.len());
        if self.bytes.below(8) == 0 {
            header.push_str("Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n");
        }
        self.stream.extend_from_slice(header.as_bytes());
        self.stream.extend_from_slice(b"\r\n");
        self.stream.extend_from_slice(body.as_bytes());
    }

    fn notify(&mut self, method: &str, params: Value) {
        let mut message = json!({ "jsonrpc": "2.0", "method": method });
        message["params"] = params;
        self.frame(&message);
    }

    fn ask(&mut self, method: &str, params: Value) {
        let id = match self.bytes.below(8) {
            0 => json!(format!("q{}", self.requests)),
            1 => Value::Null,
            _ => json!(self.requests),
        };
        self.requests += 1;
        let mut message = json!({ "jsonrpc": "2.0", "id": id, "method": method });
        message["params"] = params;
        self.frame(&message);
    }

    /// A number where the protocol has one: small, large, past what `u32` holds, negative,
    /// fractional, or a string.
    fn number(&mut self) -> Value {
        match self.bytes.below(9) {
            0 | 1 => json!(self.bytes.below(4)),
            2 => json!(self.bytes.byte()),
            3 => json!(self.bytes.u16()),
            4 => json!(self.bytes.u32()),
            5 => json!(u64::MAX),
            6 => json!(-1),
            7 => json!(1.5),
            _ => json!("2"),
        }
    }

    fn position(&mut self) -> Value {
        if self.bytes.below(16) == 0 {
            return Value::Null;
        }
        json!({ "line": self.number(), "character": self.number() })
    }

    fn range(&mut self) -> Value {
        json!({ "start": self.position(), "end": self.position() })
    }

    fn document(&mut self) -> Value {
        json!({ "uri": self.bytes.pick(&URIS) })
    }

    /// The text of a buffer: the input's, the input's with a piece put in at a character, a
    /// few pieces, or bytes of the input.
    fn buffer_text(&mut self) -> String {
        match self.bytes.below(4) {
            0 => self.text.clone(),
            1 => {
                let mut text = self.text.clone();
                let mut at = usize::from(self.bytes.u16()) % (text.len() + 1);
                while !text.is_char_boundary(at) {
                    at -= 1;
                }
                text.insert_str(at, &self.bytes.words());
                text
            }
            2 => self.bytes.words(),
            _ => {
                let n = self.bytes.below(64);
                String::from_utf8_lossy(self.bytes.take(n)).into_owned()
            }
        }
    }

    fn message(&mut self) {
        match self.bytes.below(24) {
            0..=2 => self.open(),
            3..=5 => self.change(),
            6 => {
                let params = json!({ "textDocument": self.document() });
                self.notify("textDocument/didClose", params);
            }
            7..=10 => {
                let method = self.bytes.pick(&AT);
                let params =
                    json!({ "textDocument": self.document(), "position": self.position() });
                self.ask(method, params);
            }
            11 | 12 => {
                let method = self.bytes.pick(&OVER);
                let only = self
                    .bytes
                    .pick(&[json!([]), json!(["quickfix"]), json!(["source"])]);
                let params = json!({
                    "textDocument": self.document(),
                    "range": self.range(),
                    "context": { "diagnostics": [], "only": only },
                });
                self.ask(method, params);
            }
            13 | 14 => {
                let method = self.bytes.pick(&WHOLE);
                let params = json!({ "textDocument": self.document(), "options": {} });
                self.ask(method, params);
            }
            15 => self.others(),
            16 => self.selection(),
            17 => self.initialize(),
            18 => self.rename(),
            19 => self.ask("shutdown", Value::Null),
            20 => {
                self.notify("exit", Value::Null);
                self.ended = true;
            }
            21 => self.broken(),
            _ => self.references(),
        }
    }

    fn open(&mut self) {
        let document = json!({
            "uri": self.bytes.pick(&URIS),
            "languageId": "stilt",
            "version": self.number(),
            "text": self.buffer_text(),
        });
        self.notify("textDocument/didOpen", json!({ "textDocument": document }));
    }

    fn change(&mut self) {
        let changes: Vec<Value> = (0..self.bytes.below(3))
            .map(|_| json!({ "text": self.buffer_text() }))
            .collect();
        let params = json!({ "textDocument": self.document(), "contentChanges": changes });
        self.notify("textDocument/didChange", params);
    }

    fn initialize(&mut self) {
        let client = self.bytes.pick(&["Visual Studio Code", "Neovim", ""]);
        let item = json!({
            "snippetSupport": self.bytes.flag(),
            "labelDetailsSupport": self.bytes.flag(),
        });
        let params = json!({
            "rootUri": self.bytes.pick(&[json!("file:///stilt-fuzz"), Value::Null]),
            "clientInfo": { "name": client },
            "capabilities": {
                "textDocument": { "completion": { "completionItem": item } },
                "workspace": { "codeLens": { "refreshSupport": self.bytes.flag() } },
            },
        });
        self.ask("initialize", params);
        if self.bytes.flag() {
            self.notify("initialized", json!({}));
        }
    }

    fn selection(&mut self) {
        let positions: Vec<Value> = (0..self.bytes.below(6)).map(|_| self.position()).collect();
        let params = json!({ "textDocument": self.document(), "positions": positions });
        self.ask("textDocument/selectionRange", params);
    }

    fn rename(&mut self) {
        let params = json!({
            "textDocument": self.document(),
            "position": self.position(),
            "newName": self.bytes.words(),
        });
        self.ask("textDocument/rename", params);
    }

    fn references(&mut self) {
        let params = json!({
            "textDocument": self.document(),
            "position": self.position(),
            "context": { "includeDeclaration": self.bytes.flag() },
        });
        self.ask("textDocument/references", params);
    }

    /// The rest: the program's symbols, a lens's command, a change on disk, a method the server
    /// doesn't have, and an answer to a request of the server's.
    fn others(&mut self) {
        match self.bytes.below(5) {
            0 => {
                let params = json!({ "query": self.bytes.words() });
                self.ask("workspace/symbol", params);
            }
            1 => {
                let command = self.bytes.pick(&[
                    "stilt.lens.run",
                    "stilt.lens.stop",
                    "stilt.lens.show",
                    "",
                ]);
                let argument = self.bytes.pick(&[json!("tests"), json!("main"), json!(3)]);
                let params = json!({ "command": command, "arguments": [argument] });
                self.ask("workspace/executeCommand", params);
            }
            2 => self.notify("workspace/didChangeWatchedFiles", json!({ "changes": [] })),
            3 => self.ask("textDocument/unknown", json!({})),
            _ => self.frame(&json!({ "jsonrpc": "2.0", "id": "stilt-1", "result": null })),
        }
    }

    /// A frame no editor writes, which ends the session: a length past what the input holds,
    /// none, one that isn't a number, or a body that isn't JSON.
    fn broken(&mut self) {
        let n = self.bytes.below(16);
        let mut body = b"}".to_vec();
        body.extend_from_slice(self.bytes.take(n));
        let header = match self.bytes.below(4) {
            0 => format!("Content-Length: {}\r\n\r\n", self.bytes.u64()),
            1 => "\r\n".to_owned(),
            2 => "Content-Length: many\r\n\r\n".to_owned(),
            _ => format!("Content-Length: {}\r\n\r\n", body.len()),
        };
        self.stream.extend_from_slice(header.as_bytes());
        self.stream.extend_from_slice(&body);
        self.broken = true;
        self.ended = true;
    }
}

/// The number of answers among the messages the server wrote, each of which must be framed
/// JSON.
fn answers(mut output: &[u8]) -> usize {
    let mut answers = 0;
    while !output.is_empty() {
        let head = (output.windows(4).position(|w| w == b"\r\n\r\n")).expect("a header ends");
        let header = std::str::from_utf8(&output[..head]).expect("a header is text");
        let length: usize = (header.strip_prefix("Content-Length: "))
            .and_then(|n| n.parse().ok())
            .expect("a header gives the length");
        let body = (output.get(head + 4..head + 4 + length)).expect("the body is as long");
        let mut json = serde_json::Deserializer::from_slice(body);
        json.disable_recursion_limit();
        let message = Value::deserialize(&mut json).expect("a body is JSON");
        if message.get("method").is_none() {
            let answered = message.get("result").is_some() != message.get("error").is_some();
            assert!(answered, "an answer has a result or an error: {message}");
            answers += 1;
        }
        output = &output[head + 4 + length..];
    }
    answers
}

fuzz_target!(|data: &[u8]| {
    let mut session = Session::new(data);
    session.write();
    let mut backend = fake::Fake::new(data);
    let mut output = Vec::new();
    let served = stilt_lsp::serve(Cursor::new(session.stream), &mut output, &mut backend);
    assert_eq!(
        served.is_err(),
        session.broken,
        "only a broken frame fails: {served:?}"
    );
    assert_eq!(
        answers(&output),
        session.requests,
        "each request gets one answer"
    );
});
