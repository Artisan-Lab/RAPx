#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
use std::{
    collections::HashMap,
    default,
    fmt::{self, *},
};

use bounds::Bound;
use intervals::*;
use num_traits::{Bounded, Num, Zero};
use rustc_ast::token::TokenKind::Plus;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::*, ty::Ty};
use std::ops::{Add, Mul, Sub};

use crate::{
    analysis::core::range_analysis::domain::domain::{ConstConvert, IntervalArithmetic},
    rap_trace,
};
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownReason {
    CyclicDependency,
    CannotParse,
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarorConst<'tcx> {
    Place(Place<'tcx>),
    Constant(Const<'tcx>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolicExpr<'tcx> {
    Argument(Place<'tcx>),
    Constant(Const<'tcx>),
    BinaryOp {
        op: BinOp,
        left: Box<SymbolicExpr<'tcx>>,
        right: Box<SymbolicExpr<'tcx>>,
    },
    UnaryOp {
        op: UnOp,
        operand: Box<SymbolicExpr<'tcx>>,
    },
    Cast {
        kind: CastKind,
        operand: Box<SymbolicExpr<'tcx>>,
        target_ty: Ty<'tcx>,
    },
    Ref {
        kind: BorrowKind,
        place_expr: Box<SymbolicExpr<'tcx>>,
    },
    AddressOf {
        mutability: RawPtrKind,
        place_expr: Box<SymbolicExpr<'tcx>>,
    },
    Deref(Box<SymbolicExpr<'tcx>>),
    Len(Box<SymbolicExpr<'tcx>>),
    Aggregate {
        kind: Box<AggregateKind<'tcx>>,
        fields: Vec<SymbolicExpr<'tcx>>,
    },
    Repeat {
        value: Box<SymbolicExpr<'tcx>>,
        count: Const<'tcx>,
    },
    Index {
        base: Box<SymbolicExpr<'tcx>>,
        index: Box<SymbolicExpr<'tcx>>,
    },
    Ssa(Vec<SymbolicExpr<'tcx>>),
    Essa {
        operand: Box<SymbolicExpr<'tcx>>,
        constraint_operand: VarorConst<'tcx>,
        bin_op: BinOp,
    },
    Discriminant(Box<SymbolicExpr<'tcx>>),
    NullaryOp(NullOp<'tcx>, Ty<'tcx>),
    ThreadLocalRef(DefId),
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
                    BinOp::Cmp => "cmp", // Added Cmp
                };
                write!(f, "({} {} {})", left, op_str, right)
            }
            SymbolicExpr::UnaryOp { op, operand } => {
                let op_str = match op {
                    UnOp::Not => "!",
                    UnOp::Neg => "-",
                    UnOp::PtrMetadata => "ptr_metadata", // Added PtrMetadata
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
            SymbolicExpr::Ssa(operands) => {
                let parts: Vec<String> = operands.iter().map(|e| e.to_string()).collect();
                write!(f, "SSA({})", parts.join(", "))
            }
            SymbolicExpr::Essa {
                operand,
                constraint_operand,
                bin_op,
            } => {
                let op_str = match bin_op {
                    BinOp::Eq => "==",
                    BinOp::Lt => "<",
                    BinOp::Le => "<=",
                    BinOp::Ne => "!=",
                    BinOp::Ge => ">=",
                    BinOp::Gt => ">",
                    _ => "??", // Non-comparison ops in constraint
                };
                write!(
                    f,
                    "ESSA({}, {} {} {})",
                    operand, operand, op_str, constraint_operand
                )
            }
            SymbolicExpr::Discriminant(expr) => write!(f, "discriminant({})", expr),
            SymbolicExpr::NullaryOp(op, ty) => write!(f, "{:?}({})", op, ty),
            SymbolicExpr::ThreadLocalRef(def_id) => write!(f, "tls_{:?}", def_id),
            SymbolicExpr::Unknown(reason) => write!(f, "{{{:?}}}", reason),
        }
    }
}

impl<'tcx> fmt::Display for VarorConst<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarorConst::Place(p) => write!(f, "{:?}", p),
            VarorConst::Constant(c) => write!(f, "{}", c),
        }
    }
}
// pub struct SymbolicExprEvaluator<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
//     /// 环境：将 Place 映射到其当前的 Range<T> 值
//     /// 注意：这里传入的是 HashMap，因为在实际分析中，Place 的值是动态变化的。
//     /// 这个 Evaluator 只是一个静态的计算器，给定一个环境就计算一次。
//     env: &'tcx HashMap<&'tcx Place<'tcx>, Range<T>>,
//     /// 用于类型推断或常量评估的类型上下文，如果需要的话
//     // tcx: TyCtxt<'tcx>, // 如果某些 Const<'tcx> 评估需要 TyCtxt，则取消注释
// }

// impl<'tcx, T> SymbolicExprEvaluator<'tcx, T>
// where
//     T: IntervalArithmetic + ConstConvert + Debug,
// {
//     /// 创建一个新的 SymbolicExprEvaluator 实例
//     pub fn new(env: &'tcx HashMap<&'tcx Place<'tcx>, Range<T>>) -> Self {
//         Self {
//             env,
//             // tcx, // 如果需要，在此处传入
//         }
//     }

//     /// 评估给定的 SymbolicExpr，返回一个 Range<T>
//     pub fn evaluate(&self, expr: &SymbolicExpr<'tcx>) -> Range<T> {
//         match expr {
//             SymbolicExpr::Argument(place) => {
//                 // 函数参数：从环境中查找其区间
//                 self.env.get(place)
//                     .cloned()
//                     .unwrap_or_else(|| {
//                         rap_trace!("Warning: Argument {:?} not found in environment. Assuming full range.", place);
//                         Range::default(T::min_value()) // 默认返回一个未知或全范围区间
//                     })
//             }
//             SymbolicExpr::Constant(c) => {
//                 // 常量：转换为 Range<T>
//                 if let Some(val) = T::from_const(c) {
//                     Range::new(val.clone(), val, range::RangeType)
//                 } else {
//                     rap_trace!("Warning: Cannot convert constant {:?} to type T. Returning full range.", c);
//                     Range::default(T::min_value()) // 无法转换时返回全范围
//                 }
//             }
//             SymbolicExpr::BinaryOp { op, left, right } => {
//                 // 二元操作：递归评估左右操作数，然后执行区间运算
//                 let left_range = self.evaluate(left);
//                 let right_range = self.evaluate(right);

//                 match op {
//                     BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => left_range.add(&right_range),
//                     BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => left_range.sub(&right_range),
//                     BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => left_range.mul(&right_range),
//                     BinOp::Div => left_range.div(&right_range),
//                     BinOp::Rem => left_range.rem(&right_range),
//                     BinOp::BitXor => left_range.bitxor(&right_range),
//                     BinOp::BitAnd => left_range.bitand(&right_range),
//                     BinOp::BitOr => left_range.bitor(&right_range),
//                     BinOp::Shl | BinOp::ShlUnchecked => left_range.shl(&right_range), // 注意：位移操作的右操作数通常是整数
//                     BinOp::Shr | BinOp::ShrUnchecked => left_range.shr(&right_range), // 同上

//                     // 比较操作通常返回布尔值，但在区间分析中，它们用于生成新的区间约束
//                     // 这里简化处理，直接返回全范围，或者根据需要实现更复杂的行为
//                     BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt => {
//                         rap_trace!("Warning: Comparison operator {:?} in symbolic expression. Returning full range as range analysis for comparisons typically involves conditional updates, not direct evaluation to a single range.", op);
//                         Range::default(T::min_value()) // 比较操作通常不直接产生一个数值区间
//                     },
//                     // Offset 通常用于指针算术，其数值行为复杂，返回全范围
//                     BinOp::Offset => {
//                         rap_trace!("Warning: Offset operator in symbolic expression. Returning full range.",);
//                         Range::default(T::min_value())
//                     },
//                     BinOp::Cmp => { // 比较，通常返回 Ordering
//                          rap_trace!("Warning: Cmp operator in symbolic expression. Returning full range.",);
//                         Range::default(T::min_value())
//                     }
//                 }
//             }
//             SymbolicExpr::UnaryOp { op, operand } => {
//                 // 一元操作：递归评估操作数，然后执行区间运算
//                 let operand_range = self.evaluate(operand);
//                 match op {
//                     UnOp::Neg => operand_range.neg(),
//                     UnOp::Not => operand_range.not(), // 逻辑非或位非，取决于T的实现
//                     UnOp::PtrMetadata => {
//                         rap_trace!("Warning: PtrMetadata operator in symbolic expression. Returning full range.",);
//                         Range::default(T::min_value())
//                     }
//                 }
//             }
//             SymbolicExpr::Cast { kind, operand, target_ty } => {
//                 // 类型转换：评估操作数，然后尝试转换区间
//                 let operand_range = self.evaluate(operand);
//                 // 简单的类型转换：保留原区间，但标记为不精确。
//                 // 复杂的数值截断、符号扩展等需要更复杂的逻辑，可能需要 TyCtxt。
//                 // 这里我们假设 T 的 IntervalArithmetic 能够处理不同大小整数的 Min/Max。
//                 rap_trace!("Warning: Cast operator {:?} to {:?} in symbolic expression. Returning original range as is for simplicity, assuming T handles potential overflows/underflows implicitly via its min/max.", kind, target_ty);
//                 // 实际的类型转换需要更多关于类型的信息，这里只是一个保守的估计
//                 // 更精确的实现会根据 target_ty 的位宽和有无符号性来调整区间边界
//                 operand_range
//             }
//             SymbolicExpr::Deref(expr) => {
//                 // 解引用：通常表示访问内存位置。其值范围取决于该内存位置的内容。
//                 // 在没有具体内存模型的情况下，无法计算。
//                 rap_trace!("Warning: Deref operator in symbolic expression. Returning full range.",);
//                 Range::default(T::min_value())
//             }
//             SymbolicExpr::Len(expr) => {
//                 // 长度：通常是一个非负整数。但具体长度未知。
//                 rap_trace!("Warning: Len operator in symbolic expression. Returning positive integer range.",);
//                 Range::new(T::zero(), T::max_value(), range::RangeType) // 至少为0
//             }
//             SymbolicExpr::Index { base, index } => {
//                 // 索引访问：访问数组/切片元素。
//                 // 其值范围取决于数组/切片中所有元素的可能范围，以及索引的范围。
//                 rap_trace!("Warning: Index operator in symbolic expression. Returning full range.",);
//                 Range::default(T::min_value())
//             }
//             // 对于以下复杂或无法直接映射到数值区间的操作，返回全范围 (Unknown)
//             SymbolicExpr::Ref { .. } |
//             SymbolicExpr::AddressOf { .. } |
//             SymbolicExpr::Aggregate { .. } |
//             SymbolicExpr::Repeat { .. } |
//             SymbolicExpr::Discriminant { .. } |
//             SymbolicExpr::NullaryOp { .. } |
//             SymbolicExpr::ThreadLocalRef { .. } => {
//                 rap_trace!("Warning: Complex/unsupported symbolic expression type {:?}. Returning full range.", expr);
//                 Range::default(T::min_value())
//             }
//             SymbolicExpr::Unknown(reason) => {
//                 // 表达式本身就是未知，结果也是未知
//                 rap_trace!("Warning: Symbolic expression is Unknown due to reason {:?}. Propagating Unknown range.", reason);
//                 Range::default(T::min_value())
//             }
//         }
//     }
// }
