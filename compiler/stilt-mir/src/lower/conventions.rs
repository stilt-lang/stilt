//! Conventions (`stilt_runtime::abi`): the words in which a call passes a value, its own
//! layout's or the one word that holds it, and the locals that receive them.

use stilt_types::ty::Ty;

use super::words::word;
use super::{Conv, Form, Lower};
use crate::mir::{Local, Operand, Repr};

impl Lower<'_> {
    /// The number of words a value passed in a convention takes in memory. An error of no
    /// known type, from a row variable, is one word.
    pub(crate) fn width(&self, c: &Conv) -> usize {
        match c.form {
            _ if c.ty == Ty::Error => 1,
            Form::Word => 1,
            Form::Layout => self.words_of(&c.ty),
        }
    }

    /// New locals for the words of a value passed in a convention.
    pub(crate) fn conv_temps(&mut self, c: &Conv) -> Vec<Local> {
        if c.ty == Ty::Error {
            return vec![self.b.temp(Repr::Heap)];
        }
        match c.form {
            Form::Word => {
                let repr = self.repr(&c.ty);
                vec![self.b.temp(repr)]
            }
            Form::Layout => self.temps(&c.ty),
        }
    }

    /// The words of a value from the words a convention passes it in.
    pub(crate) fn received(&mut self, words: Vec<Operand>, c: &Conv) -> Vec<Operand> {
        match c.form {
            _ if c.ty == Ty::Error => words,
            Form::Word => self.unbox(word(&words, 0), &c.ty),
            Form::Layout => words,
        }
    }

    /// The words a convention passes a value in, from its words.
    pub(crate) fn passed(&mut self, words: Vec<Operand>, c: &Conv) -> Vec<Operand> {
        match c.form {
            _ if c.ty == Ty::Error => words,
            Form::Word => vec![self.boxed(words, &c.ty)],
            Form::Layout => words,
        }
    }
}
