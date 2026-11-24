//! Where fixes edit a function's signature: its generics, its row, and the rows of its
//! parameters' function types.

use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{SyntaxKind, TextRange, TextSize};

use super::{Resolver, bare};
use crate::hir::{Name, RowSpans, SignatureSpans};

impl Resolver<'_> {
    /// Where fixes edit a function's signature.
    pub(super) fn signature_spans(&self, f: &ast::Fn) -> SignatureSpans {
        let generics = f
            .generic_list()
            .into_iter()
            .flat_map(|list| list.generics())
            .filter_map(|g| {
                let (name, bound) = match g {
                    ast::Generic::TypeParam(p) => (p.name()?.ident()?, p.bounds().last()),
                    ast::Generic::RowParam(p) => (p.name()?.ident()?, None),
                    ast::Generic::ValueParam(p) => (p.name()?.ident()?, None),
                };
                let bounded = bound.is_some();
                let end = bound.map_or(self.at_token(&name).end(), |b| self.at(b.syntax()).end());
                Some((Name::from(name.text()), end, bounded))
            })
            .collect();
        let name_end = self.name(f.name(), f.syntax()).at.end();
        let params_end = f
            .param_list()
            .map_or(name_end, |p| self.at(p.syntax()).end());
        let list = f.param_list();
        let receiver = list
            .as_ref()
            .and_then(ast::ParamList::self_param)
            .map(|_| None);
        let params = receiver
            .into_iter()
            .chain(list.iter().flat_map(ast::ParamList::params).map(|p| {
                match p.ty().as_ref().map(bare) {
                    Some(ast::Type::FnType(t)) => Some(self.fn_type_row(&t)),
                    _ => None,
                }
            }))
            .collect();
        SignatureSpans {
            generics,
            generics_at: name_end,
            row: self.row_place(f.ret_type(), params_end, f.row()),
            params,
            end: TextSize::default(),
        }
    }

    /// Where a row is written in the function type `t`, and the row it writes.
    fn fn_type_row(&self, t: &ast::FnType) -> RowSpans {
        let params_end = t
            .syntax()
            .children()
            .find(|n| n.kind() == SyntaxKind::PARAM_TYPE_LIST)
            .map_or_else(|| self.at(t.syntax()).end(), |n| self.at(&n).end());
        self.row_place(t.ret_type(), params_end, t.row())
    }

    /// Where the row `row` of a function or a function type is written: after its return type
    /// `ret`, or at `params_end` without one. A return type that is a function type with no row
    /// would take a row written after it, so a fix parenthesizes it first
    /// (declarations.function-type-rows).
    fn row_place(
        &self,
        ret: Option<ast::RetType>,
        params_end: TextSize,
        row: Option<ast::Row>,
    ) -> RowSpans {
        let wrap = match ret.as_ref().and_then(ast::RetType::ty) {
            Some(ast::Type::FnType(t)) if t.row().is_none() => Some(self.at(t.syntax()).start()),
            _ => None,
        };
        RowSpans {
            row_at: ret.map_or(params_end, |r| self.at(r.syntax()).end()),
            wrap,
            row: row.map(|r| self.row_spans(&r)),
        }
    }

    /// The span of a row's elements, and whether braces enclose them. Braces around no element
    /// have an empty span, before the closing brace.
    fn row_spans(&self, r: &ast::Row) -> (TextRange, bool) {
        let elements: Vec<_> = r.elements().map(|e| self.at(e.syntax())).collect();
        let close = r
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| t.kind() == SyntaxKind::R_CURLY);
        let span = match (elements.first(), elements.last(), &close) {
            (Some(first), Some(last), _) => first.cover(*last),
            (_, _, Some(close)) => TextRange::empty(self.at_token(close).start()),
            _ => TextRange::empty(self.at(r.syntax()).end()),
        };
        (span, close.is_some())
    }
}
