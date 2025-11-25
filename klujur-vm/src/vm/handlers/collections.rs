// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Collection opcode handlers: Get, GetDefault, Assoc, Conj, Count, Nth.

use klujur_parser::value::KlujurVal;

use crate::opcode::OpCode;
use crate::utils::type_name;
use crate::vm::{Result, RuntimeError, VM};

impl VM {
    /// Execute a collection opcode.
    pub(crate) fn execute_collections(&mut self, op: OpCode) -> Result<()> {
        match op {
            OpCode::Get => self.execute_get(None),
            OpCode::GetDefault => {
                let default = self.stack.pop()?;
                self.execute_get(Some(default))
            }
            OpCode::Assoc => self.execute_assoc(),
            OpCode::Conj => self.execute_conj(),
            OpCode::Count => self.execute_count(),
            OpCode::Nth => self.execute_nth(),
            _ => Err(RuntimeError::Internal(format!(
                "execute_collections: unexpected opcode {:?}",
                op
            ))),
        }
    }

    /// Execute Get or GetDefault (unified implementation).
    fn execute_get(&mut self, default: Option<KlujurVal>) -> Result<()> {
        let key = self.stack.pop()?;
        let coll = self.stack.pop()?;
        let default_val = default.unwrap_or(KlujurVal::Nil);

        let result = match &coll {
            KlujurVal::Map(map, _) => map.get(&key).cloned().unwrap_or(default_val),
            KlujurVal::Vector(items, _) => {
                if let KlujurVal::Int(idx) = key {
                    if idx >= 0 && (idx as usize) < items.len() {
                        items[idx as usize].clone()
                    } else {
                        default_val
                    }
                } else {
                    default_val
                }
            }
            KlujurVal::Set(set, _) => {
                if set.contains(&key) {
                    key
                } else {
                    default_val
                }
            }
            KlujurVal::Nil => default_val,
            _ => default_val,
        };
        self.stack.push(result);
        Ok(())
    }

    fn execute_assoc(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        let key = self.stack.pop()?;
        let coll = self.stack.pop()?;
        let result = match coll {
            KlujurVal::Map(mut map, meta) => {
                map.insert(key, val);
                KlujurVal::Map(map, meta)
            }
            KlujurVal::Vector(mut items, meta) => {
                if let KlujurVal::Int(idx) = key {
                    if idx >= 0 && (idx as usize) <= items.len() {
                        if (idx as usize) == items.len() {
                            // Append at end
                            items.push_back(val);
                        } else {
                            // Replace at index
                            items.set(idx as usize, val);
                        }
                        KlujurVal::Vector(items, meta)
                    } else {
                        return Err(RuntimeError::Internal(format!(
                            "Index {} out of bounds for vector of length {}",
                            idx,
                            items.len()
                        )));
                    }
                } else {
                    return Err(RuntimeError::TypeError {
                        expected: "integer".into(),
                        got: type_name(&key).into(),
                    });
                }
            }
            KlujurVal::Nil => {
                // assoc on nil creates a map
                let mut map = im::OrdMap::new();
                map.insert(key, val);
                KlujurVal::Map(map, None)
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "map or vector".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(result);
        Ok(())
    }

    fn execute_conj(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        let coll = self.stack.pop()?;
        let result = match coll {
            KlujurVal::List(mut items, meta) => {
                items.push_front(val);
                KlujurVal::List(items, meta)
            }
            KlujurVal::Vector(mut items, meta) => {
                items.push_back(val);
                KlujurVal::Vector(items, meta)
            }
            KlujurVal::Set(mut set, meta) => {
                set.insert(val);
                KlujurVal::Set(set, meta)
            }
            KlujurVal::Nil => KlujurVal::list(vec![val]),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "collection".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(result);
        Ok(())
    }

    fn execute_count(&mut self) -> Result<()> {
        let coll = self.stack.pop()?;
        let count = match &coll {
            KlujurVal::Nil => 0,
            KlujurVal::List(items, _) | KlujurVal::Vector(items, _) => items.len() as i64,
            KlujurVal::Map(map, _) => map.len() as i64,
            KlujurVal::Set(set, _) => set.len() as i64,
            KlujurVal::String(s) => s.chars().count() as i64,
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "collection".into(),
                    got: type_name(&coll).into(),
                });
            }
        };
        self.stack.push(KlujurVal::Int(count));
        Ok(())
    }

    fn execute_nth(&mut self) -> Result<()> {
        let idx = self.stack.pop()?;
        let coll = self.stack.pop()?;
        let result = match (&coll, &idx) {
            (KlujurVal::Vector(items, _), KlujurVal::Int(i)) => {
                if *i >= 0 && (*i as usize) < items.len() {
                    items[*i as usize].clone()
                } else {
                    return Err(RuntimeError::Internal(format!(
                        "Index {} out of bounds for vector of length {}",
                        i,
                        items.len()
                    )));
                }
            }
            (KlujurVal::List(items, _), KlujurVal::Int(i)) => {
                if *i >= 0 && (*i as usize) < items.len() {
                    items[*i as usize].clone()
                } else {
                    return Err(RuntimeError::Internal(format!(
                        "Index {} out of bounds for list of length {}",
                        i,
                        items.len()
                    )));
                }
            }
            (KlujurVal::String(s), KlujurVal::Int(i)) => {
                if *i >= 0 {
                    s.chars()
                        .nth(*i as usize)
                        .map(KlujurVal::Char)
                        .ok_or_else(|| {
                            RuntimeError::Internal(format!(
                                "Index {} out of bounds for string of length {}",
                                i,
                                s.chars().count()
                            ))
                        })?
                } else {
                    return Err(RuntimeError::Internal(format!("Index {} out of bounds", i)));
                }
            }
            (_, KlujurVal::Int(_)) => {
                return Err(RuntimeError::TypeError {
                    expected: "indexed collection".into(),
                    got: type_name(&coll).into(),
                });
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "integer".into(),
                    got: type_name(&idx).into(),
                });
            }
        };
        self.stack.push(result);
        Ok(())
    }
}
