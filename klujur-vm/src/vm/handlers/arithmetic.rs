// klujur-vm - Bytecode compiler and virtual machine for the Klujur programming language
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Arithmetic opcode handlers: Add, Sub, Mul, Div, Inc, Dec.

use klujur_parser::value::KlujurVal;

use crate::opcode::OpCode;
use crate::utils::type_name;
use crate::vm::{Result, RuntimeError, VM};

impl VM {
    /// Execute an arithmetic opcode.
    pub(crate) fn execute_arithmetic(&mut self, op: OpCode) -> Result<()> {
        match op {
            OpCode::Add => self.binary_num_op(|a, b| a + b, |a, b| a + b, "+"),
            OpCode::Sub => self.binary_num_op(|a, b| a - b, |a, b| a - b, "-"),
            OpCode::Mul => self.binary_num_op(|a, b| a * b, |a, b| a * b, "*"),
            OpCode::Div => self.execute_div(),
            OpCode::Inc => self.execute_inc(),
            OpCode::Dec => self.execute_dec(),
            _ => Err(RuntimeError::Internal(format!(
                "execute_arithmetic: unexpected opcode {:?}",
                op
            ))),
        }
    }

    fn execute_div(&mut self) -> Result<()> {
        let b = self.stack.pop()?;
        let a = self.stack.pop()?;
        match (&a, &b) {
            (KlujurVal::Int(x), KlujurVal::Int(y)) => {
                if *y == 0 {
                    return Err(RuntimeError::DivisionByZero);
                }
                // Clojure semantics: integer division produces a ratio
                self.stack.push(KlujurVal::ratio(*x, *y));
            }
            (KlujurVal::Float(x), KlujurVal::Float(y)) => {
                self.stack.push(KlujurVal::Float(x / y));
            }
            (KlujurVal::Int(x), KlujurVal::Float(y)) => {
                self.stack.push(KlujurVal::Float(*x as f64 / y));
            }
            (KlujurVal::Float(x), KlujurVal::Int(y)) => {
                self.stack.push(KlujurVal::Float(x / *y as f64));
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: format!("{} / {}", type_name(&a), type_name(&b)),
                });
            }
        }
        Ok(())
    }

    fn execute_inc(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        match val {
            KlujurVal::Int(n) => {
                self.stack
                    .push(KlujurVal::Int(n.checked_add(1).ok_or_else(|| {
                        RuntimeError::Internal("Integer overflow in inc".into())
                    })?));
            }
            KlujurVal::Float(n) => {
                self.stack.push(KlujurVal::Float(n + 1.0));
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: type_name(&val).into(),
                });
            }
        }
        Ok(())
    }

    fn execute_dec(&mut self) -> Result<()> {
        let val = self.stack.pop()?;
        match val {
            KlujurVal::Int(n) => {
                self.stack
                    .push(KlujurVal::Int(n.checked_sub(1).ok_or_else(|| {
                        RuntimeError::Internal("Integer overflow in dec".into())
                    })?));
            }
            KlujurVal::Float(n) => {
                self.stack.push(KlujurVal::Float(n - 1.0));
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: type_name(&val).into(),
                });
            }
        }
        Ok(())
    }

    /// Perform a binary numeric operation.
    /// NOTE: Currently only supports Int and Float types. BigInt and Ratio types
    /// will cause the VM to fall back to native function calls via the resolver.
    pub(crate) fn binary_num_op<FI, FF>(
        &mut self,
        int_op: FI,
        float_op: FF,
        name: &str,
    ) -> Result<()>
    where
        FI: Fn(i64, i64) -> i64,
        FF: Fn(f64, f64) -> f64,
    {
        let b = self.stack.pop()?;
        let a = self.stack.pop()?;

        let result = match (&a, &b) {
            (KlujurVal::Int(x), KlujurVal::Int(y)) => KlujurVal::Int(int_op(*x, *y)),
            (KlujurVal::Float(x), KlujurVal::Float(y)) => KlujurVal::Float(float_op(*x, *y)),
            (KlujurVal::Int(x), KlujurVal::Float(y)) => KlujurVal::Float(float_op(*x as f64, *y)),
            (KlujurVal::Float(x), KlujurVal::Int(y)) => KlujurVal::Float(float_op(*x, *y as f64)),
            // For BigInt, Ratio, and BigRatio, fall back to native function calls
            (KlujurVal::BigInt(_), _)
            | (_, KlujurVal::BigInt(_))
            | (KlujurVal::Ratio(_, _), _)
            | (_, KlujurVal::Ratio(_, _))
            | (KlujurVal::BigRatio(_, _), _)
            | (_, KlujurVal::BigRatio(_, _)) => {
                return Err(RuntimeError::TypeError {
                    expected: "Int or Float (BigInt/Ratio not yet supported in VM)".into(),
                    got: format!("{} {} {}", type_name(&a), name, type_name(&b)),
                });
            }
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: format!("{} {} {}", type_name(&a), name, type_name(&b)),
                });
            }
        };

        self.stack.push(result);
        Ok(())
    }

    /// Perform a comparison operation.
    pub(crate) fn comparison_op<FI, FF>(
        &mut self,
        int_op: FI,
        float_op: FF,
        name: &str,
    ) -> Result<()>
    where
        FI: Fn(i64, i64) -> bool,
        FF: Fn(f64, f64) -> bool,
    {
        let b = self.stack.pop()?;
        let a = self.stack.pop()?;

        let result = match (&a, &b) {
            (KlujurVal::Int(x), KlujurVal::Int(y)) => int_op(*x, *y),
            (KlujurVal::Float(x), KlujurVal::Float(y)) => float_op(*x, *y),
            (KlujurVal::Int(x), KlujurVal::Float(y)) => float_op(*x as f64, *y),
            (KlujurVal::Float(x), KlujurVal::Int(y)) => float_op(*x, *y as f64),
            _ => {
                return Err(RuntimeError::TypeError {
                    expected: "number".into(),
                    got: format!("{} {} {}", type_name(&a), name, type_name(&b)),
                });
            }
        };

        self.stack.push(KlujurVal::Bool(result));
        Ok(())
    }
}
