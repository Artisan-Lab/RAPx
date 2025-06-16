#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]

use crate::rap_trace;

use super::range::{Range, RangeType};
use num_traits::{Bounded, CheckedAdd, CheckedSub, One, ToPrimitive, Zero};
use rustc_abi::Size;
use rustc_middle::mir::coverage::Op;
use rustc_middle::mir::{
    BasicBlock, BinOp, Const, Local, LocalDecl, Place, Rvalue, Statement, StatementKind,
};
use rustc_middle::ty::ScalarInt;
use rustc_span::sym::no_default_passes;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::ops::{Add, Mul, Sub};
pub trait ConstConvert: Sized {
    fn from_const(c: &Const) -> Option<Self>;
}

impl ConstConvert for u32 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_u32())
        } else {
            None
        }
    }
}
impl ConstConvert for usize {
    fn from_const(c: &Const) -> Option<Self> {
        let size = Size::from_bits(32);
        // let size = Size::from_bits(std::mem::size_of::<usize>() as u64 * 8);
        if let Some(scalar) = c.try_to_bits(size) {
            Some(scalar.to_usize().unwrap())
        } else {
            None
        }
    }
}
impl ConstConvert for i32 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_i32())
        } else {
            None
        }
    }
}

impl ConstConvert for i64 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_i64())
        } else {
            None
        }
    }
}
pub trait IntervalArithmetic:
    PartialOrd
    + Clone
    + Bounded
    + Zero
    + One
    + CheckedAdd
    + CheckedSub
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + fmt::Display
{
}

impl<T> IntervalArithmetic for T where
    T: PartialOrd
        + Clone
        + Bounded
        + Zero
        + One
        + CheckedAdd
        + CheckedSub
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + fmt::Display
{
}
#[derive(Debug, Clone, PartialEq)]
pub enum IntervalType<'tcx, T: IntervalArithmetic> {
    Basic(BasicInterval<T>),
    Symb(SymbInterval<'tcx, T>), // Using 'static for simplicity, adjust lifetime as needed
}
impl<'tcx, T: IntervalArithmetic> fmt::Display for IntervalType<'tcx, T>
where
    T: IntervalArithmetic,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalType::Basic(b) => write!(f, "BasicInterval: {}", b.get_range()),
            IntervalType::Symb(s) => write!(f, "SymbInterval: {}", s.get_range()),
        }
    }
}
pub trait IntervalTypeTrait<T: IntervalArithmetic> {
    // fn get_value_id(&self) -> IntervalId;
    fn get_range(&self) -> &Range<T>;
    fn set_range(&mut self, new_range: Range<T>);
}
impl<'tcx, T: IntervalArithmetic> IntervalTypeTrait<T> for IntervalType<'tcx, T> {
    fn get_range(&self) -> &Range<T> {
        match self {
            IntervalType::Basic(b) => b.get_range(),
            IntervalType::Symb(s) => s.get_range(),
        }
    }

    fn set_range(&mut self, new_range: Range<T>) {
        match self {
            IntervalType::Basic(b) => b.set_range(new_range),
            IntervalType::Symb(s) => s.set_range(new_range),
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct BasicInterval<T: IntervalArithmetic> {
    range: Range<T>,
}

impl<T: IntervalArithmetic> BasicInterval<T> {
    pub fn new(range: Range<T>) -> Self {
        Self { range }
    }
    pub fn default() -> Self {
        Self {
            range: Range::default(T::min_value()),
        }
    }
}

impl<T: IntervalArithmetic> IntervalTypeTrait<T> for BasicInterval<T> {
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::BasicIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
        if self.range.get_lower() > self.range.get_upper() {
            self.range.set_empty();
        }
    }
}

#[derive(Debug, Clone, PartialEq)]

pub struct SymbInterval<'tcx, T: IntervalArithmetic> {
    range: Range<T>,
    symbound: &'tcx Place<'tcx>,
    predicate: BinOp,
}

impl<'tcx, T: IntervalArithmetic> SymbInterval<'tcx, T> {
    pub fn new(range: Range<T>, symbound: &'tcx Place<'tcx>, predicate: BinOp) -> Self {
        Self {
            range: range,
            symbound,
            predicate,
        }
    }

    pub fn get_operation(&self) -> BinOp {
        self.predicate
    }

    pub fn get_bound(&self) -> &'tcx Place<'tcx> {
        self.symbound
    }

    pub fn sym_fix_intersects(
        &self,
        bound: &VarNode<'tcx, T>,
        sink: &VarNode<'tcx, T>,
    ) -> Range<T> {
        let l = bound.get_range().get_lower().clone();
        let u = bound.get_range().get_upper().clone();

        let lower = sink.get_range().get_lower().clone();
        let upper = sink.get_range().get_upper().clone();

        match self.predicate {
            BinOp::Eq => Range::new(l, u, RangeType::Regular),

            BinOp::Le => Range::new(lower, u, RangeType::Regular),

            BinOp::Lt => {
                if u != T::max_value() {
                    let u_minus_1 = u.checked_sub(&T::one()).unwrap_or(u);
                    Range::new(lower, u_minus_1, RangeType::Regular)
                } else {
                    Range::new(lower, u, RangeType::Regular)
                }
            }

            BinOp::Ge => Range::new(l, upper, RangeType::Regular),

            BinOp::Gt => {
                if l != T::min_value() {
                    let l_plus_1 = l.checked_add(&T::one()).unwrap_or(l);
                    Range::new(l_plus_1, upper, RangeType::Regular)
                } else {
                    Range::new(l, upper, RangeType::Regular)
                }
            }

            BinOp::Ne => {
                // 不等的情况不好精确表示，用全范围
                Range::new(T::min_value(), T::max_value(), RangeType::Regular)
            }

            _ => {
                // 其它暂未处理的操作，保守返回全范围
                Range::new(T::min_value(), T::max_value(), RangeType::Regular)
            }
        }
    }
}

impl<'tcx, T: IntervalArithmetic> IntervalTypeTrait<T> for SymbInterval<'tcx, T> {
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::SymbIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
    }
}

// Define the basic operation trait
pub trait Operation<T: IntervalArithmetic> {
    fn get_value_id(&self) -> u32; // Placeholder for an operation identifier
    fn eval(&self) -> Range<T>; // Method to evaluate the result of the operation
    fn print(&self, os: &mut dyn fmt::Write);
}

// #[derive(Debug, Clone)]
// pub struct BasicOp<'tcx, T: IntervalArithmetic> {
//     pub intersect: BasicInterval<T>,
//     pub sink: Place<'tcx>,
//     pub inst: &'tcx Statement<'tcx>,
// }

// impl<'tcx, T: IntervalArithmetic> BasicOp<'tcx, T> {
//     // Constructor for creating a new BasicOp
//     pub fn new(
//         intersect: BasicInterval<T>,
//         sink: Place<'tcx>,
//         inst: &'tcx Statement<'tcx>,
//     ) -> Self {
//         BasicOp {
//             intersect,
//             sink,
//             inst,
//         }
//     }

//     pub fn get_instruction(&self) -> Option<&Statement<'tcx>> {
//         Some(self.inst)
//     }

//     pub fn fix_intersects(&mut self, _v: &VarNode<T>) {}

//     pub fn set_intersect(&mut self, new_intersect: Range<T>) {
//         self.intersect.set_range(new_intersect);
//     }

//     pub fn get_sink(&self) -> Place<'tcx> {
//         self.sink
//     }
//     // Returns the instruction that originated this operation

//     // Returns the target of the operation (sink), mutable version
// }

// // Implement the Operation trait for BasicOp
// impl<'tcx, T: IntervalArithmetic> Operation<T> for BasicOp<'tcx, T> {
//     fn get_value_id(&self) -> u32 {
//         0 // Placeholder implementation
//     }

//     fn eval(&self) -> Range<T> {
//         // Placeholder for evaluating the range
//         Range::default(T::min_value()) // Assuming Range<T> implements Default
//     }

//     fn print(&self, os: &mut dyn fmt::Write) {}
// }
#[derive(Debug)]
pub enum BasicOpKind<'tcx, T: IntervalArithmetic> {
    Unary(UnaryOp<'tcx, T>),
    Binary(BinaryOp<'tcx, T>),
    Essa(EssaOp<'tcx, T>),
    ControlDep(ControlDep<'tcx, T>),
    Phi(PhiOp<'tcx, T>),
    Use(UseOp<'tcx, T>),
}

impl<'tcx, T: IntervalArithmetic> fmt::Display for BasicOpKind<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BasicOpKind::Unary(op) => write!(f, "UnaryOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",op.intersect,op.sink,op.source,op.inst),
            BasicOpKind::Binary(op) => write!(f, "BinaryOp: intersect {} sink:{:?} source1:{:?} source2:{:?} inst:{:?} const_value:{} ",op.intersect,op.sink,op.source1,op.source2,op.inst,op.const_value.clone().unwrap()),
            BasicOpKind::Essa(op) => write!(f, "EssaOp: intersect {} sink:{:?} source:{:?} inst:{:?} unresolved:{:?} ",op.intersect,op.sink,op.source,op.inst,op.unresolved),
            BasicOpKind::ControlDep(op) => write!(f, "ControlDep: intersect {} sink:{:?} source:{:?} inst:{:?}  ",op.intersect,op.sink,op.source,op.inst),
            BasicOpKind::Phi(op) => write!(f, "PhiOp: intersect {} sink:{:?} source:{:?} inst:{:?}  ",op.intersect,op.sink,op.sources,op.inst),
            BasicOpKind::Use(op) => write!(f, "UseOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",op.intersect,op.sink,op.source,op.inst ),
        }
    }
}
impl<'tcx, T: IntervalArithmetic> BasicOpKind<'tcx, T> {
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        match self {
            BasicOpKind::Unary(op) => op.eval(),
            BasicOpKind::Binary(op) => op.eval(vars),
            BasicOpKind::Essa(op) => op.eval(vars),
            BasicOpKind::ControlDep(op) => op.eval(),
            BasicOpKind::Phi(op) => op.eval(vars),
            BasicOpKind::Use(op) => op.eval(vars),
        }
    }
    pub fn get_type_name(&self) -> &'static str {
        match self {
            BasicOpKind::Unary(_) => "Unary",
            BasicOpKind::Binary(_) => "Binary",
            BasicOpKind::Essa(_) => "Essa",
            BasicOpKind::ControlDep(_) => "ControlDep",
            BasicOpKind::Phi(_) => "Phi",
            BasicOpKind::Use(_) => "Use",
        }
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        match self {
            BasicOpKind::Unary(op) => op.sink,
            BasicOpKind::Binary(op) => op.sink,
            BasicOpKind::Essa(op) => op.sink,
            BasicOpKind::ControlDep(op) => op.sink,
            BasicOpKind::Phi(op) => op.sink,
            BasicOpKind::Use(op) => op.sink,
        }
    }
    pub fn get_instruction(&self) -> &'tcx Statement<'tcx> {
        match self {
            BasicOpKind::Unary(op) => op.inst,
            BasicOpKind::Binary(op) => op.inst,
            BasicOpKind::Essa(op) => op.inst,
            BasicOpKind::ControlDep(op) => op.inst,
            BasicOpKind::Phi(op) => op.inst,
            BasicOpKind::Use(op) => op.inst,
        }
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        match self {
            BasicOpKind::Unary(op) => &op.intersect,
            BasicOpKind::Binary(op) => &op.intersect,
            BasicOpKind::Essa(op) => &op.intersect,
            BasicOpKind::ControlDep(op) => &op.intersect,
            BasicOpKind::Phi(op) => &op.intersect,
            BasicOpKind::Use(op) => &op.intersect,
        }
    }
    pub fn op_fix_intersects(&mut self, v: &VarNode<'tcx, T>, sink: &VarNode<'tcx, T>) {
        let intersect = self.get_intersect_mut();

        if let IntervalType::Symb(symbi) = intersect {
            let range = symbi.sym_fix_intersects(v, sink);
            rap_trace!(
                "from {:?} to {:?} fix_intersects: {:} -> {}\n",
                v.get_value().clone(),
                sink.get_value().clone(),
                intersect.clone(),
                range
            );
            self.set_intersect(range);
        }
    }
    pub fn set_intersect(&mut self, new_intersect: Range<T>) {
        match self {
            BasicOpKind::Unary(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Binary(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Essa(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::ControlDep(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Phi(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Use(op) => op.intersect.set_range(new_intersect),
        }
    }
    pub fn get_intersect_mut(&mut self) -> &mut IntervalType<'tcx, T> {
        match self {
            BasicOpKind::Unary(op) => &mut op.intersect,
            BasicOpKind::Binary(op) => &mut op.intersect,
            BasicOpKind::Essa(op) => &mut op.intersect,
            BasicOpKind::ControlDep(op) => &mut op.intersect,
            BasicOpKind::Phi(op) => &mut op.intersect,
            BasicOpKind::Use(op) => &mut op.intersect,
        }
    }
    pub fn get_source(&self) -> &'tcx Place<'tcx> {
        match self {
            BasicOpKind::Unary(op) => op.source,
            BasicOpKind::Binary(op) => op.source1.unwrap(),
            BasicOpKind::Essa(op) => op.source,
            BasicOpKind::ControlDep(op) => op.source,
            BasicOpKind::Phi(op) => op.sources[0],
            BasicOpKind::Use(op) => op.source,
        }
    }
    // pub fn eval(&self) -> Range<T> {
    //     match self {
    //         BasicOpKind::Unary(op) => op.eval(),
    //         BasicOpKind::Binary(op) => op.eval(),
    //         BasicOpKind::Essa(op) => op.eval(),
    //         BasicOpKind::ControlDep(op) => op.eval(),
    //         BasicOpKind::Phi(op) => op.eval(),
    //         BasicOpKind::Use(op) => op.eval(),
    //     }
    // }
}
#[derive(Debug)]
pub struct UseOp<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub opcode: u32,
}

impl<'tcx, T: IntervalArithmetic> UseOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        opcode: u32,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            opcode,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let range = vars[self.source].get_range().clone();
        let mut result = Range::default(T::min_value());
        if range.is_regular() {
            result = range
        } else {
        }
        result
    }
}
#[derive(Debug)]
pub struct UnaryOp<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub opcode: u32,
}

impl<'tcx, T: IntervalArithmetic> UnaryOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        opcode: u32,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            opcode,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::default(T::min_value())
    }
}
#[derive(Debug)]

pub struct EssaOp<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub opcode: u32,
    pub unresolved: bool,
}

impl<'tcx, T: IntervalArithmetic> EssaOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        opcode: u32,
        unresolved: bool,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            opcode,
            unresolved,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let source_range = vars[self.source].get_range().clone();
        let result = source_range.intersectwith(self.intersect.get_range());
        rap_trace!(
            "EssaOp eval: {:?} {} intersectwith {}-> {}\n",
            self.source,
            self.intersect.get_range(),
            source_range,
            result
        );
        result
    }
    pub fn get_source(&self) -> &'tcx Place<'tcx> {
        self.source
    }
    pub fn get_instruction(&self) -> &'tcx Statement<'tcx> {
        self.inst
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        self.sink
    }
    pub fn is_unresolved(&self) -> bool {
        self.unresolved
    }

    pub fn mark_resolved(&mut self) {
        self.unresolved = false;
    }

    pub fn mark_unresolved(&mut self) {
        self.unresolved = true;
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        &self.intersect
    }
}
#[derive(Debug)]

pub struct BinaryOp<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source1: Option<&'tcx Place<'tcx>>,
    pub source2: Option<&'tcx Place<'tcx>>,
    pub const_value: Option<T>,
    pub opcode: u32,
}

impl<'tcx, T: IntervalArithmetic> BinaryOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source1: Option<&'tcx Place<'tcx>>,
        source2: Option<&'tcx Place<'tcx>>,
        opcode: u32,
        const_value: Option<T>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source1,
            source2,
            const_value, // Default value, can be set later
            opcode,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let op1 = vars[self.source1.unwrap()].get_range().clone();
        let mut op2 = Range::default(T::min_value());
        if let Some(const_value) = &self.const_value {
            // If const_value is provided, use it as the second operand
            op2 = Range::new(const_value.clone(), const_value.clone(), RangeType::Regular);
        } else {
            op2 = vars[self.source2.unwrap()].get_range().clone();
        }
        let mut result = Range::default(T::min_value());
        match &self.inst.kind {
            StatementKind::Assign(box (place, rvalue)) => match rvalue {
                Rvalue::BinaryOp(binop, _) => match binop {
                    BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                        result = op1.add(&op2);
                    }

                    BinOp::SubUnchecked | BinOp::SubWithOverflow | BinOp::Sub => {
                        result = op1.sub(&op2);
                    }

                    BinOp::MulUnchecked | BinOp::MulWithOverflow | BinOp::Mul => {
                        result = op1.mul(&op2);
                    }

                    _ => {}
                },
                _ => {}
            },

            _ => {}
        }

        result
    }
}
#[derive(Debug)]

pub struct PhiOp<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub sources: Vec<&'tcx Place<'tcx>>,
    pub opcode: u32,
}

impl<'tcx, T: IntervalArithmetic> PhiOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        opcode: u32,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            sources: vec![],
            opcode,
        }
    }

    pub fn add_source(&mut self, src: &'tcx Place<'tcx>) {
        self.sources.push(src);
    }
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let first = self.sources[0];
        let mut result = vars[first].get_range().clone();
        for &phisource in self.sources.iter() {
            let node = &vars[phisource];
            result = result.unionwith(node.get_range());
            rap_trace!(
                "PhiOp eval:  {} unionwith {} -> {}\n",
                vars[first].get_range().clone(),
                node.get_range(),
                result
            );
        }
        result
    }
}
#[derive(Debug)]

pub struct ControlDep<'tcx, T: IntervalArithmetic> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
}

impl<'tcx, T: IntervalArithmetic> ControlDep<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::default(T::min_value())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct VarNode<'tcx, T: IntervalArithmetic> {
    // The program variable which is represented.
    pub v: &'tcx Place<'tcx>,
    // A Range associated to the variable.
    pub interval: Range<T>,
    // Used by the crop meet operator.
    pub abstract_state: char,
}
impl<'tcx, T: IntervalArithmetic> VarNode<'tcx, T> {
    pub fn new(v: &'tcx Place<'tcx>) -> Self {
        Self {
            v,
            interval: Range::default(T::min_value()),
            abstract_state: '?',
        }
    }

    /// Initializes the value of the node.
    pub fn init(&mut self, outside: bool) {
        let value = self.get_value();

        // if let Some(ci) = value.as_constant_int() {
        //     let tmp = ci.get_value();
        //     if tmp.bits() < MAX_BIT_INT {
        //         self.set_range(Range::new(
        //             tmp.extend_bits(MAX_BIT_INT),
        //             tmp.extend_bits(MAX_BIT_INT),
        //         ));
        //     } else {
        //         self.set_range(Range::new(tmp, tmp));
        //     }
        // } else {
        //     if !outside {
        //         self.set_range(Range::new(MIN, MAX));
        //     } else {
        //         self.set_range(Range::new(MIN, MAX));
        //     }
        // }
    }

    /// Returns the range of the variable represented by this node.
    pub fn get_range(&self) -> &Range<T> {
        &self.interval
    }

    /// Returns the variable represented by this node.
    pub fn get_value(&self) -> &'tcx Place<'tcx> {
        self.v
    }

    /// Changes the status of the variable represented by this node.
    pub fn set_range(&mut self, new_interval: Range<T>) {
        self.interval = new_interval;

        // Check if lower bound is greater than upper bound. If it is,
        // set range to empty.
        // if self.interval.get_lower().sgt(self.interval.get_upper()) {
        //     self.interval.set_empty();
        // }
    }

    /// Pretty print.
    pub fn print(&self, os: &mut dyn std::io::Write) {
        // Implementation of pretty printing using the `os` writer.
    }
    pub fn set_default(&mut self) {
        self.interval.set_default();
    }

    pub fn get_abstract_state(&self) -> char {
        self.abstract_state
    }

    /// The possible states are '0', '+', '-', and '?'.
    pub fn store_abstract_state(&mut self) {
        // Implementation of storing the abstract state.
    }
}
#[derive(Debug)]
pub struct ValueBranchMap<'tcx, T: IntervalArithmetic> {
    v: &'tcx Place<'tcx>,         // The value associated with the branch
    bb_true: &'tcx BasicBlock,    // True side of the branch
    bb_false: &'tcx BasicBlock,   // False side of the branch
    itv_t: IntervalType<'tcx, T>, // Interval for the true side
    itv_f: IntervalType<'tcx, T>,
}
impl<'tcx, T: IntervalArithmetic> ValueBranchMap<'tcx, T> {
    pub fn new(
        v: &'tcx Place<'tcx>,
        bb_false: &'tcx BasicBlock,
        bb_true: &'tcx BasicBlock,
        itv_f: IntervalType<'tcx, T>,
        itv_t: IntervalType<'tcx, T>,
    ) -> Self {
        Self {
            v,
            bb_false,
            bb_true,
            itv_f,
            itv_t,
        }
    }

    /// Get the "false side" of the branch
    pub fn get_bb_false(&self) -> &BasicBlock {
        self.bb_false
    }

    /// Get the "true side" of the branch
    pub fn get_bb_true(&self) -> &BasicBlock {
        self.bb_true
    }

    /// Get the interval associated with the true side of the branch
    pub fn get_itv_t(&self) -> IntervalType<'tcx, T> {
        self.itv_t.clone()
    }

    /// Get the interval associated with the false side of the branch
    pub fn get_itv_f(&self) -> IntervalType<'tcx, T> {
        self.itv_f.clone()
    }

    /// Get the value associated with the branch
    pub fn get_v(&self) -> &'tcx Place<'tcx> {
        self.v
    }

    // pub fn set_itv_t(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_t = itv;
    // }

    // /// Change the interval associated with the false side of the branch
    // pub fn set_itv_f(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_f = itv;
    // }

    // pub fn clear(&mut self) {
    //     self.itv_t = Box::new(EmptyInterval::new());
    //     self.itv_f = Box::new(EmptyInterval::new());
    // }
}

pub type VarNodes<'tcx, T> = HashMap<&'tcx Place<'tcx>, VarNode<'tcx, T>>;
pub type GenOprs<'tcx, T> = Vec<BasicOpKind<'tcx, T>>;
pub type UseMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type SymbMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type DefMap<'tcx> = HashMap<&'tcx Place<'tcx>, usize>;
pub type ValuesBranchMap<'tcx, T> = HashMap<&'tcx Place<'tcx>, ValueBranchMap<'tcx, T>>;
