//! What the pages of a package show (docs.module-pages): its modules, each with its
//! description and its `pub` declarations, read from the source as `stilt show` reads it, with
//! the facts of the package's API.

use std::collections::HashMap;

use serde_json::{Value, json};
use stilt_db::{Database, Program, SourceFile};
use stilt_hir::hir::{Item as Address, Name};
use stilt_mir::FnRef;
use stilt_syntax::SyntaxKind;
use stilt_syntax::ast::{self, AstNode as _, DocLine};

use crate::report::text;
use stilt_ide::show::skeleton::{patterns, slice, token};

/// A package's pages.
pub(crate) struct Package {
    pub(crate) name: String,
    pub(crate) modules: Vec<Module>,
}

/// A module's page.
pub(crate) struct Module {
    pub(crate) address: String,
    pub(crate) tier: String,
    pub(crate) description: String,
    pub(crate) items: Vec<Item>,
}

/// A declaration on a page, with what goes under it.
pub(crate) struct Item {
    pub(crate) kind: &'static str,
    pub(crate) name: String,
    pub(crate) signature: String,
    pub(crate) facts: Option<Vec<String>>,
    pub(crate) doc: String,
    pub(crate) examples: Vec<String>,
    pub(crate) members: Vec<Item>,
}

type Facts = HashMap<FnRef, Vec<String>>;

/// The pages of the root package of `program`, named `name`, in the order of their addresses.
pub(crate) fn package(db: &Database, program: Program, name: &str) -> Package {
    let files: Vec<SourceFile> = (program.files(db).iter().copied())
        .filter(|&f| stilt_db::package_of(db, program, f) == 0)
        .collect();
    pages(db, program, name, &files, &|module| {
        if module == "main" {
            name.to_owned()
        } else {
            format!("{name}.{module}")
        }
    })
}

/// The pages of the standard library, a package named `std` whose modules' addresses are their
/// names, as `std.fs` (docs.std).
pub(crate) fn standard_library(db: &Database, program: Program) -> Package {
    pages(db, program, "std", program.std(db), &str::to_owned)
}

/// The pages of the modules of `files`, of the package `name`, each at the address that
/// `address` gives its module's name, in the order of their addresses.
fn pages(
    db: &Database,
    program: Program,
    name: &str,
    files: &[SourceFile],
    address: &dyn Fn(&str) -> String,
) -> Package {
    let facts = crate::packages::api::facts(db, program, files);
    let map = stilt_hir::def_map(db, program);
    let mut modules: Vec<Module> = files
        .iter()
        .filter_map(|&file| {
            let module = map.of_file(file).filter(|m| m.valid)?;
            let at = address(&module.name);
            Some(page(db, program, file, (module.name, at), &facts))
        })
        .collect();
    modules.sort_by(|a, b| a.address.cmp(&b.address));
    Package {
        name: name.to_owned(),
        modules,
    }
}

/// The page of the module `module` of the file `file`, at the address `address`.
fn page(
    db: &Database,
    program: Program,
    file: SourceFile,
    (module, address): (Name, String),
    facts: &Facts,
) -> Module {
    let source = text(db, file);
    let tree = stilt_db::parse(db, file).tree();
    let items: Vec<ast::Item> = tree.items().collect();
    let types = (items.iter())
        .filter_map(|i| match i {
            ast::Item::TypeDecl(t) => t.name().map(|n| n.text().clone()),
            _ => None,
        })
        .collect();
    let reader = Reader {
        text: &source,
        module,
        facts,
        types,
    };
    let mut out: Vec<Item> = items.iter().filter_map(|i| reader.item(i)).collect();
    for i in &items {
        if let ast::Item::Impl(block) = i {
            reader.attach(block, &mut out);
        }
    }
    Module {
        address,
        tier: stilt_types::facts::tier(db, program, file).to_string(),
        description: description(&source),
        items: out,
    }
}

/// A module's description: the run of `//` lines that its file starts with, after its header
/// if it writes one, without `//` and one space (docs.module-pages).
fn description(source: &str) -> String {
    let mut lines = source.lines().map(str::trim).peekable();
    if lines.peek().is_some_and(|l| l.starts_with("module ")) {
        lines.next();
    }
    let text: Vec<&str> = lines
        .skip_while(|l| l.is_empty())
        .map_while(|l| l.strip_prefix("//").filter(|_| !l.starts_with("///")))
        .map(|l| l.strip_prefix(' ').unwrap_or(l))
        .collect();
    text.join("\n").trim().to_owned()
}

/// What reads a module's declarations.
struct Reader<'a> {
    text: &'a str,
    module: Name,
    facts: &'a Facts,
    /// The names of the types the module declares, `pub` or not.
    types: Vec<String>,
}

impl Reader<'_> {
    /// A declaration written `pub`, with its signature and doc; `None` for any other item.
    fn item(&self, item: &ast::Item) -> Option<Item> {
        let at = |name: Option<ast::Name>| name.map(|n| n.text()).unwrap_or_default();
        let (kind, name, signature, docs) = match item {
            ast::Item::Fn(f) if f.is_pub() => {
                let end = f.body().map(|b| b.syntax().text_range().start());
                (
                    "fn",
                    at(f.name()),
                    slice(self.text, f.syntax(), end),
                    f.docs(),
                )
            }
            ast::Item::TypeDecl(t) if t.is_pub() => (
                "type",
                at(t.name()),
                slice(self.text, t.syntax(), None),
                t.docs(),
            ),
            ast::Item::Const(c) if c.is_pub() => {
                let end = token(c.syntax(), SyntaxKind::EQ);
                (
                    "const",
                    at(c.name()),
                    slice(self.text, c.syntax(), end),
                    c.docs(),
                )
            }
            ast::Item::Effect(e) if e.is_pub() => (
                "effect",
                at(e.name()),
                slice(self.text, e.syntax(), None),
                e.docs(),
            ),
            ast::Item::Syntax(s) if s.is_pub() => {
                ("macro", at(s.name()), patterns(self.text, s, ""), s.docs())
            }
            ast::Item::Trait(t) if t.is_pub() => return Some(self.trait_item(t)),
            _ => return None,
        };
        let facts = (kind == "fn").then(|| self.fact(&FnRef::Function(self.address(&name))));
        Some(entry((kind, name, signature), docs.as_ref(), facts))
    }

    /// A trait, its first line as its signature and its methods under it.
    fn trait_item(&self, t: &ast::Trait) -> Item {
        let name = t.name().map(|n| n.text()).unwrap_or_default();
        let open = token(t.syntax(), SyntaxKind::L_CURLY);
        let head = slice(self.text, t.syntax(), open);
        let owner = self.address(&name);
        let members = t
            .members()
            .filter_map(|m| {
                let ast::Item::Fn(f) = &m else {
                    return self.member(&m, None);
                };
                let method = f.name().map(|n| n.text()).unwrap_or_default();
                let fact = f.body().map(|_| {
                    self.fact(&FnRef::DefaultMethod(owner.clone(), method.as_str().into()))
                });
                self.member(&m, fact)
            })
            .collect();
        Item {
            members,
            ..entry(("trait", name, head), t.docs().as_ref(), None)
        }
    }

    /// A member of a trait or of an inherent impl, with the facts `facts` gives a function.
    fn member(&self, m: &ast::Item, facts: Option<Vec<String>>) -> Option<Item> {
        let (kind, name, signature, docs) = match m {
            ast::Item::Fn(f) => {
                let end = f.body().map(|b| b.syntax().text_range().start());
                let name = f.name().map(|n| n.text()).unwrap_or_default();
                ("fn", name, slice(self.text, f.syntax(), end), f.docs())
            }
            ast::Item::Const(c) => {
                let end = token(c.syntax(), SyntaxKind::EQ);
                let name = c.name().map(|n| n.text()).unwrap_or_default();
                ("const", name, slice(self.text, c.syntax(), end), c.docs())
            }
            _ => return None,
        };
        Some(entry((kind, name, signature), docs.as_ref(), facts))
    }

    /// Puts an impl block's members, or a trait impl's first line, under the type it is for,
    /// when that type is one of the page's. An inherent impl of a type that the module doesn't
    /// declare, a built-in type of `std.prelude`, puts that type on the page after its
    /// declarations, written as the impl writes it, as `List<T>` (docs.std).
    fn attach(&self, block: &ast::Impl, items: &mut Vec<Item>) {
        let Some(written) = block.self_ty().map(|t| t.syntax().text().to_string()) else {
            return;
        };
        let owner = head(&written);
        if !self.types.contains(&owner)
            && block.trait_ty().is_none()
            && !items.iter().any(|i| i.kind == "type" && i.name == owner)
        {
            items.push(entry(("type", owner.clone(), written), None, None));
        }
        let declared = |i: &Item| i.kind == "type" && i.name == owner;
        let Some(target) = items.iter_mut().find(|i| declared(i)) else {
            return;
        };
        if block.trait_ty().is_some() {
            let open = token(block.syntax(), SyntaxKind::L_CURLY);
            let line = slice(self.text, block.syntax(), open);
            target
                .members
                .push(entry(("impl", owner, line), None, None));
            return;
        }
        let address = self.address(&owner);
        for m in block.members() {
            let public = match &m {
                ast::Item::Fn(f) => f.is_pub(),
                ast::Item::Const(c) => c.is_pub(),
                _ => false,
            };
            let facts = match &m {
                ast::Item::Fn(f) => {
                    let name = f.name().map(|n| n.text()).unwrap_or_default();
                    Some(self.fact(&FnRef::Member(address.clone(), name.as_str().into())))
                }
                _ => None,
            };
            if let Some(item) = public.then(|| self.member(&m, facts)).flatten() {
                target.members.push(item);
            }
        }
    }

    fn address(&self, name: &str) -> Address {
        Address {
            home: self.module,
            name: name.into(),
        }
    }

    fn fact(&self, f: &FnRef) -> Vec<String> {
        self.facts.get(f).cloned().unwrap_or_default()
    }
}

/// The name a type is written with, without its arguments.
fn head(written: &str) -> String {
    let name = written.split('<').next().unwrap_or(written).trim();
    name.rsplit('.').next().unwrap_or(name).to_owned()
}

/// An item with its doc's text and its examples.
fn entry(
    (kind, name, signature): (&'static str, String, String),
    docs: Option<&ast::Docs>,
    facts: Option<Vec<String>>,
) -> Item {
    let mut doc = Vec::new();
    let mut examples = Vec::new();
    for line in docs.map(ast::Docs::lines).unwrap_or_default() {
        match line {
            DocLine::Text(t) => doc.push(t),
            DocLine::Example(e, _) => {
                examples.push(e.syntax().text().to_string().trim().to_owned());
            }
            DocLine::Property(_, _, own) => examples.push(own),
        }
    }
    Item {
        kind,
        name,
        signature,
        facts,
        doc: doc.join("\n").trim().to_owned(),
        examples,
        members: Vec::new(),
    }
}

/// The package's pages as one JSON object (docs.json).
pub(crate) fn json(package: &Package) -> Value {
    json!({
        "package": package.name,
        "modules": package.modules.iter().map(|m| json!({
            "address": m.address,
            "tier": m.tier,
            "description": m.description,
            "items": m.items.iter().map(item_json).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
    })
}

fn item_json(i: &Item) -> Value {
    json!({
        "kind": i.kind,
        "name": i.name,
        "signature": i.signature,
        "facts": i.facts,
        "doc": i.doc,
        "examples": i.examples,
        "members": i.members.iter().map(item_json).collect::<Vec<_>>(),
    })
}
