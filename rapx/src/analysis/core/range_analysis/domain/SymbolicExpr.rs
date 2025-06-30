#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
use std::{default, fmt};

use bounds::Bound;
use intervals::*;
use num_traits::{Bounded, Num, Zero};
use rustc_ast::token::TokenKind::Plus;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::*, ty::Ty};
use std::ops::{Add, Mul, Sub};
use z3::ast::Int;

use crate::rap_trace;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownReason {
    CyclicDependency,
}

/// 重新设计的符号表达式树，紧密映射 MIR Rvalue 的语义
#[derive(Debug, Clone)]
pub enum SymbolicExpr<'tcx> {
    /// 函数参数, e.g., arg0, arg1.
    /// 直接对应函数的输入 `Local`。
    Argument(Place<'tcx>),

    /// 常量值。
    /// 对应 `Operand::Constant`。
    Constant(Const<'tcx>),

    // --- 算术与逻辑运算 ---
    /// 二元操作, e.g., `a + b`。
    /// 对应 `Rvalue::BinaryOp` 和 `Rvalue::CheckedBinaryOp`。
    BinaryOp {
        op: BinOp,
        left: Box<SymbolicExpr<'tcx>>,
        right: Box<SymbolicExpr<'tcx>>,
    },

    /// 一元操作, e.g., `-a`。
    /// 对应 `Rvalue::UnaryOp`。
    UnaryOp {
        op: UnOp,
        operand: Box<SymbolicExpr<'tcx>>,
    },

    /// 类型转换。
    /// 对应 `Rvalue::Cast`。
    Cast {
        kind: CastKind,
        operand: Box<SymbolicExpr<'tcx>>,
        target_ty: Ty<'tcx>,
    },

    // --- 内存、指针与地址操作 ---
    /// 创建一个（安全的）引用。
    /// 对应 `Rvalue::Ref`。
    Ref {
        kind: BorrowKind,
        place_expr: Box<SymbolicExpr<'tcx>>,
    },

    /// 创建一个原始指针。
    /// 对应 `Rvalue::RawPtr`。
    AddressOf {
        mutability: RawPtrKind,
        place_expr: Box<SymbolicExpr<'tcx>>,
    },

    /// 解引用，是 `Ref` 和 `AddressOf` 的逆操作。
    /// 这不是直接来自 `Rvalue`，而是来自 `PlaceElem::Deref` 的解析结果。
    Deref(Box<SymbolicExpr<'tcx>>),

    /// 获取一个数组或切片的长度。
    /// 对应 `Rvalue::Len`。
    Len(Box<SymbolicExpr<'tcx>>),

    // --- 聚合类型与字段访问 ---
    /// 创建一个聚合类型的值（结构体、元组、数组等）。
    /// 对应 `Rvalue::Aggregate`。
    Aggregate {
        kind: Box<AggregateKind<'tcx>>,
        fields: Vec<SymbolicExpr<'tcx>>,
    },

    /// 创建一个重复值的数组。
    /// 对应 `Rvalue::Repeat`。
    Repeat {
        value: Box<SymbolicExpr<'tcx>>,
        count: Const<'tcx>,
    },

    /// 字段访问，如 `base.field`。
    /// 来自 `PlaceElem::Field` 的解析结果。

    /// 索引访问，如 `base[index]`。
    /// 来自 `PlaceElem::Index` 的解析结果。
    Index {
        base: Box<SymbolicExpr<'tcx>>,
        index: Box<SymbolicExpr<'tcx>>,
    },

    /// 获取一个枚举的判别式（discriminant）。
    /// 对应 `Rvalue::Discriminant`。
    Discriminant(Box<SymbolicExpr<'tcx>>),

    // --- 其他特殊操作 ---
    /// 无操作数的操作，如 `size_of`。
    /// 对应 `Rvalue::NullaryOp`。
    NullaryOp(NullOp<'tcx>, Ty<'tcx>),

    /// 线程局部变量的引用。
    /// 对应 `Rvalue::ThreadLocalRef`。
    ThreadLocalRef(DefId),

    /// 未知或无法分析的情况。
    Unknown(UnknownReason),
}

impl<'tcx> fmt::Display for SymbolicExpr<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolicExpr::Argument(i) => write!(f, "arg{:?}", i),
            SymbolicExpr::Constant(c) => write!(f, "{}", c),
            SymbolicExpr::BinaryOp { op, left, right } => {
                let op_str = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Rem => "%",
                    BinOp::BitXor => "^",
                    BinOp::BitAnd => "&",
                    BinOp::BitOr => "|",
                    BinOp::Shl => "<<",
                    BinOp::Shr => ">>",
                    BinOp::Eq => "==",
                    BinOp::Lt => "<",
                    BinOp::Le => "<=",
                    BinOp::Ne => "!=",
                    BinOp::Ge => ">=",
                    BinOp::Gt => ">",
                    BinOp::Offset => "offset",
                    BinOp::AddUnchecked => "+",
                    BinOp::AddWithOverflow => "+",
                    BinOp::SubUnchecked => "-",
                    BinOp::SubWithOverflow => "-",
                    BinOp::MulUnchecked => "*",
                    BinOp::MulWithOverflow => "*",
                    BinOp::ShlUnchecked => "<<",
                    BinOp::ShrUnchecked => ">>",
                    BinOp::Cmp => todo!(),
                };
                write!(f, "({} {} {})", left, op_str, right)
            }
            SymbolicExpr::UnaryOp { op, operand } => {
                let op_str = match op {
                    UnOp::Not => "!",
                    UnOp::Neg => "-",
                    UnOp::PtrMetadata => todo!(),
                };
                write!(f, "({}{})", op_str, operand)
            }
            SymbolicExpr::Cast {
                operand, target_ty, ..
            } => write!(f, "({} as {})", operand, target_ty),
            SymbolicExpr::Ref { kind, place_expr } => match kind {
                BorrowKind::Shared => write!(f, "&{}", place_expr),
                BorrowKind::Mut { .. } => write!(f, "&mut {}", place_expr),
                BorrowKind::Fake(..) => write!(f, "&shallow {}", place_expr),
            },
            SymbolicExpr::AddressOf {
                mutability,
                place_expr,
            } => match mutability {
                RawPtrKind::Const => write!(f, "&raw const {}", place_expr),
                RawPtrKind::Mut => write!(f, "&raw mut {}", place_expr),
                RawPtrKind::FakeForPtrMetadata => {
                    write!(f, "&raw FakeForPtrMetadata {}", place_expr)
                }
            },
            SymbolicExpr::Deref(expr) => write!(f, "*({})", expr),
            SymbolicExpr::Len(expr) => write!(f, "len({})", expr),
            SymbolicExpr::Aggregate { kind, fields } => {
                let parts: Vec<String> = fields.iter().map(|e| e.to_string()).collect();
                match **kind {
                    AggregateKind::Tuple => write!(f, "({})", parts.join(", ")),
                    AggregateKind::Array(_) => write!(f, "[{}]", parts.join(", ")),
                    AggregateKind::Adt(def_id, ..) => write!(f, "{:?}{{..}}", def_id),
                    _ => write!(f, "aggr({})", parts.join(", ")),
                }
            }
            SymbolicExpr::Repeat { value, count } => write!(f, "[{}; {}]", value, count),
            SymbolicExpr::Index { base, index } => write!(f, "{}[{}]", base, index),
            SymbolicExpr::Discriminant(expr) => write!(f, "discriminant({})", expr),
            SymbolicExpr::NullaryOp(op, ty) => write!(f, "{:?}({})", op, ty),
            SymbolicExpr::ThreadLocalRef(def_id) => write!(f, "tls_{:?}", def_id),
            SymbolicExpr::Unknown(reason) => write!(f, "{{{:?}}}", reason),
        }
    }
}
