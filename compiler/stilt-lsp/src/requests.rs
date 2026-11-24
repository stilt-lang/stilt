//! The requests the server answers, each from the backend, its answer written in the
//! protocol's positions.

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;

use serde_json::{Value, json};

use crate::server::{Server, byte, root};
use crate::text::{offset, range};
use crate::{Place, convert, tokens};

/// The protocol's code of a request for a method the server doesn't have.
const METHOD_NOT_FOUND: i64 = -32601;

/// The protocol's code of a request that failed.
const INTERNAL: i64 = -32603;

/// The protocol's code of a request that is valid but can't be done, as a rename of a
/// standard library's name.
const REQUEST_FAILED: i64 = -32803;

/// A request's failure: its code and its message.
pub(crate) type Failure = (i64, String);

fn failed(e: String) -> Failure {
    (INTERNAL, e)
}

impl<W: Write> Server<'_, W> {
    pub(crate) fn request(&mut self, method: &str, params: &Value) -> Result<Value, Failure> {
        match method {
            "initialize" => {
                self.client = convert::Client::of(params);
                let lenses = &params["capabilities"]["workspace"]["codeLens"];
                self.jobs.refreshes = lenses["refreshSupport"] == true;
                self.backend.open(&root(params)).map_err(failed)?;
                Ok(convert::capabilities(self.client))
            }
            "shutdown" => Ok(Value::Null),
            "textDocument/hover" => {
                let (file, at) = self.at(params);
                let shown = self.backend.hover(&file, at).map_err(failed)?;
                Ok(shown.map_or(Value::Null, |s| convert::hover(&s)))
            }
            "textDocument/definition"
            | "textDocument/declaration"
            | "textDocument/typeDefinition" => {
                let (file, at) = self.at(params);
                let found = if method.ends_with("typeDefinition") {
                    self.backend.type_definition(&file, at)
                } else {
                    self.backend.definition(&file, at)
                };
                Ok(found
                    .map_err(failed)?
                    .map_or(Value::Null, |p| self.locations(&[p])[0].clone()))
            }
            "textDocument/codeAction" => Ok(self.actions(params)),
            "textDocument/codeLens" => Ok(self.lenses(params)),
            "workspace/executeCommand" => {
                self.execute(params).map_err(|e| failed(e.to_string()))?;
                Ok(Value::Null)
            }
            "textDocument/completion" => self.completion(params),
            "textDocument/signatureHelp" => self.signature(params),
            "textDocument/references" => self.references(params),
            "textDocument/documentHighlight" => self.highlights(params),
            "textDocument/prepareRename" => self.prepare_rename(params),
            "textDocument/rename" => self.rename(params),
            _ => self.reading(method, params),
        }
    }

    /// The requests about a file as it reads: its symbols, hints, tokens, folds, selections,
    /// formatting and whereabouts.
    fn reading(&mut self, method: &str, params: &Value) -> Result<Value, Failure> {
        let (file, uri, text) = self.document(params);
        match method {
            "textDocument/documentSymbol" => {
                let symbols = self.backend.symbols(&file, &text);
                Ok(json!(convert::symbols(&text, &symbols)))
            }
            "workspace/symbol" => self.workspace_symbols(params),
            "textDocument/inlayHint" => {
                let hints = self.backend.hints(&file).map_err(failed)?;
                let from = offset(&text, &params["range"]["start"]);
                let to = offset(&text, &params["range"]["end"]);
                let shown = hints
                    .iter()
                    .filter(|h| (from..=to).contains(&(h.at as usize)))
                    .map(|h| convert::hint(&text, &uri, h));
                Ok(Value::Array(shown.collect()))
            }
            "textDocument/semanticTokens/full" => {
                let found = self.backend.tokens(&file).map_err(failed)?;
                Ok(json!({ "data": tokens::encode(&text, &found) }))
            }
            "textDocument/foldingRange" => {
                let folds = self.backend.folds(&text);
                Ok(Value::Array(
                    folds
                        .iter()
                        .filter_map(|f| convert::fold(&text, f))
                        .collect(),
                ))
            }
            "textDocument/selectionRange" => Ok(self.selections(params, &text)),
            "textDocument/formatting" => Ok(self
                .backend
                .format(&text)
                .map_or(Value::Null, |new| convert::whole_edit(&text, &new))),
            "stilt/whereabouts" => {
                let at = byte(offset(&text, &params["position"]));
                let found = self.backend.whereabouts(&file, at).map_err(failed)?;
                Ok(json!(found))
            }
            _ => Err((METHOD_NOT_FOUND, format!("no method `{method}`"))),
        }
    }

    /// The protocol's locations of places, each file's text read once.
    fn locations(&self, places: &[Place]) -> Vec<Value> {
        let mut texts: HashMap<PathBuf, (String, String)> = HashMap::new();
        places
            .iter()
            .map(|p| {
                let (uri, text) = texts
                    .entry(p.path.clone())
                    .or_insert_with(|| self.text_of(&p.path));
                json!({ "uri": uri, "range": range(text, p.start, p.end) })
            })
            .collect()
    }

    fn completion(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        let found = self.backend.completion(&file, at).map_err(failed)?;
        let client = self.client;
        let items: Vec<Value> = found
            .iter()
            .map(|c| convert::completion(c, client))
            .collect();
        Ok(json!({ "isIncomplete": false, "items": items }))
    }

    fn signature(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        let found = self.backend.signature(&file, at).map_err(failed)?;
        Ok(found.map_or(Value::Null, |s| convert::signature(&s)))
    }

    fn references(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        let mut found = self.backend.references(&file, at).map_err(failed)?;
        if params["context"]["includeDeclaration"] == false
            && let Some(Place { path, start, end }) =
                self.backend.definition(&file, at).ok().flatten()
        {
            found.retain(|p| !(p.path == path && p.start == start && p.end == end));
        }
        Ok(Value::Array(self.locations(&found)))
    }

    /// The places of the request's file that name what its position names, each a highlight
    /// of kind write, 3, where code binds or assigns it, and of kind read, 2, elsewhere.
    fn highlights(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        let found = self.backend.highlights(&file, at).map_err(failed)?;
        let (_, text) = self.text_of(&file);
        let shown = found.iter().map(|h| {
            let kind = if h.write { 3 } else { 2 };
            json!({ "range": range(&text, h.start, h.end), "kind": kind })
        });
        Ok(Value::Array(shown.collect()))
    }

    fn prepare_rename(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        match self.backend.prepare_rename(&file, at).map_err(failed)? {
            Ok(p) => {
                let (_, text) = self.text_of(&p.path);
                let placeholder = text
                    .get(p.start as usize..p.end as usize)
                    .unwrap_or_default();
                Ok(json!({ "range": range(&text, p.start, p.end), "placeholder": placeholder }))
            }
            Err(why) => Err((REQUEST_FAILED, why)),
        }
    }

    fn rename(&mut self, params: &Value) -> Result<Value, Failure> {
        let (file, at) = self.at(params);
        let name = params["newName"].as_str().unwrap_or_default();
        let files = match self.backend.rename(&file, at, name).map_err(failed)? {
            Ok(files) => files,
            Err(why) => return Err((REQUEST_FAILED, why)),
        };
        let mut changes = serde_json::Map::new();
        for (path, edits) in files {
            let (uri, text) = self.text_of(&path);
            let edits: Vec<Value> = edits
                .iter()
                .map(|e| json!({ "range": range(&text, e.start, e.end), "newText": e.text }))
                .collect();
            changes.insert(uri, Value::Array(edits));
        }
        Ok(json!({ "changes": changes }))
    }

    fn workspace_symbols(&mut self, params: &Value) -> Result<Value, Failure> {
        let query = params["query"].as_str().unwrap_or_default();
        let found = self.backend.workspace_symbols(query).map_err(failed)?;
        let mut texts: HashMap<PathBuf, (String, String)> = HashMap::new();
        let shown = found.iter().map(|s| {
            let (uri, text) = texts
                .entry(s.path.clone())
                .or_insert_with(|| self.text_of(&s.path));
            convert::workspace_symbol(uri, text, s)
        });
        Ok(Value::Array(shown.collect()))
    }

    /// The selection ranges at each position of the request, each the smallest span around it
    /// with its parents.
    fn selections(&mut self, params: &Value, text: &str) -> Value {
        let positions = params["positions"].as_array().cloned().unwrap_or_default();
        let ranges = positions.iter().map(|position| {
            let at = byte(offset(text, position));
            let spans = self.backend.selections(text, at);
            let mut nested = Value::Null;
            for &(start, end) in spans.iter().rev() {
                let mut node = json!({ "range": range(text, start, end) });
                if !nested.is_null() {
                    node["parent"] = nested;
                }
                nested = node;
            }
            if nested.is_null() {
                let here = range(text, at, at);
                nested = json!({ "range": here });
            }
            nested
        });
        Value::Array(ranges.collect())
    }

    /// The fixes of the diagnostics last published for a file that overlap the range asked
    /// about, as quick fixes, and the action that applies every fix of the file, each where the
    /// kinds asked for, if any, hold it.
    fn actions(&self, params: &Value) -> Value {
        let (file, uri, text) = self.document(params);
        let start = offset(&text, &params["range"]["start"]);
        let end = offset(&text, &params["range"]["end"]);
        let only: Vec<&str> = (params["context"]["only"].as_array().into_iter().flatten())
            .filter_map(Value::as_str)
            .collect();
        let wanted = |kind: &str| {
            only.is_empty()
                || only
                    .iter()
                    .any(|o| kind == *o || kind.starts_with(&format!("{o}.")))
        };
        let published = self.published.get(&file).map_or(&[][..], Vec::as_slice);
        let mut found = Vec::new();
        if wanted("quickfix") {
            for d in published {
                if d.start as usize <= end && start <= d.end as usize {
                    found.extend(d.fixes.iter().map(|f| convert::action(&text, &uri, d, f)));
                }
            }
        }
        if wanted(convert::FIX_ALL)
            && let Some(all) = convert::fix_all(&text, &uri, published)
        {
            found.push(all);
        }
        Value::Array(found)
    }
}
