// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Sequence opcode handlers: Cons, First, Rest, Next, EmptyP, NilP.

use klujur_parser::value::KlujurVal;

use crate::opcode::OpCode;
use crate::utils::type_name;
use crate::vm::{Result, RuntimeError, VM};

impl VM {
    /// Execute a sequence opcode.
    pub(crate) fn execute_sequences(&mut self, op: OpCode) -> Result<()> {
        match op {
            OpCode::Cons => self.execute_cons(),
            OpCode::First => self.execute_first(),
            OpCode::Rest => self.execute_rest(),
            OpCode::Next => self.execute_next(),
            OpCode::NilP => self.execute_nil_p(),
            OpCode::EmptyP => self.execute_empty_p(),
            _ => Err(RuntimeError::Internal(format!(
                "execute_sequences: unexpected opcode {:?}",
                op
            ))),
        }
    }

    fn execute_cons(&mut self) -> Result<()> {
        let rest = self.stack.pop()?;
        let first = self.stack.pop()?;
        let list = match rest {
            KlujurVal::List(l, _) => {
                let mut v = vec![first];
                v.extend(l.iter().cloned());
                KlujurVal::list(v)
            }
            KlujurVal::Nil => KlujurVal::list(vec![first]),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "list or nil".into(),
                    got: type_name(&rest).into(),
                });
            }
        };
        self.stack.push(list);
        Ok(())
    }

    fn execute_first(&mut self) -> Result<()> {
        let coll = self.stack.pop()?;
        let first = match &coll {
            KlujurVal::List(l, _) => l.front().cloned().unwrap_or(KlujurVal::Nil),
            KlujurVal::Vector(v, _) => v.front().cloned().unwrap_or(KlujurVal::Nil),
            KlujurVal::Nil => KlujurVal::Nil,
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "sequence".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(first);
        Ok(())
    }

    fn execute_rest(&mut self) -> Result<()> {
        let coll = self.stack.pop()?;
        let rest = match &coll {
            KlujurVal::List(l, _) => {
                if l.is_empty() {
                    KlujurVal::list(vec![])
                } else {
                    KlujurVal::list(l.iter().skip(1).cloned().collect())
                }
            }
            KlujurVal::Vector(v, _) => {
                if v.is_empty() {
                    KlujurVal::list(vec![])
                } else {
                    KlujurVal::list(v.iter().skip(1).cloned().collect())
                }
            }
            KlujurVal::Nil => KlujurVal::list(vec![]),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "sequence".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(rest);
        Ok(())
    }

    fn execute_next(&mut self) -> Result<()> {
        let coll = self.stack.pop()?;
        let next = match &coll {
            KlujurVal::List(items, _) => {
                if items.len() <= 1 {
                    KlujurVal::Nil
                } else {
                    KlujurVal::list(items.iter().skip(1).cloned().collect())
                }
            }
            KlujurVal::Vector(items, _) => {
                if items.len() <= 1 {
                    KlujurVal::Nil
                } else {
                    KlujurVal::list(items.iter().skip(1).cloned().collect())
                }
            }
            KlujurVal::Nil => KlujurVal::Nil,
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "sequence".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(next);
        Ok(())
    }

    fn execute_nil_p(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        self.stack
            .push(KlujurVal::Bool(matches!(val, KlujurVal::Nil)));
        Ok(())
    }

    fn execute_empty_p(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        let is_empty = match &val {
            KlujurVal::Nil => true,
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => items.is_empty(),
            KlujurVal::Map(map, _) => map.is_empty(),
            KlujurVal::Set(set, _) => set.is_empty(),
            KlujurVal::String(s) => s.is_empty(),
            _ => false,
        };
        self.stack.push(KlujurVal::Bool(is_empty));
        Ok(())
    }
}
