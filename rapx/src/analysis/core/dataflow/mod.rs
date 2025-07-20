pub mod debug;
pub mod default;
pub mod graph;

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug, Display},
    fs::File,
    io::Write,
    process::Command,
};

use crate::{analysis::Analysis, utils::source::get_fn_name_byid};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};
use rustc_span::Span;

pub type Arg2Ret = IndexVec<Local, bool>;
pub type Arg2RetMap = HashMap<DefId, IndexVec<Local, bool>>;
#[derive(Clone)]
pub struct DataFlowGraph {
    pub nodes: GraphNodes,
    pub edges: GraphEdges,
    pub param_ret_deps: Arg2Ret,
}
pub type DataFlowGraphMap = HashMap<DefId, DataFlowGraph>;

pub struct Arg2RetWrapper(pub Arg2Ret);
pub struct Arg2RetMapWrapper(pub Arg2RetMap);
pub struct DataFlowGraphWrapper(pub DataFlowGraph);
pub struct DataFlowGraphMapWrapper(pub HashMap<DefId, DataFlowGraph>);

pub type EdgeIdx = usize;
pub type GraphNodes = IndexVec<Local, GraphNode>;
pub type GraphEdges = IndexVec<EdgeIdx, GraphEdge>;

#[derive(Clone, Debug)]
pub struct GraphEdge {
    pub src: Local,
    pub dst: Local,
    pub op: EdgeOp,
    pub seq: usize,
}

#[derive(Clone, Debug)]
pub struct GraphNode {
    pub ops: Vec<NodeOp>,
    pub span: Span, //the corresponding code span
    pub seq: usize, //the sequence number, edges with the same seq number are added in the same batch within a statement or terminator
    pub out_edges: Vec<EdgeIdx>,
    pub in_edges: Vec<EdgeIdx>,
}

/// This trait provides features related to dataflow analysis.
pub trait DataFlowAnalysis: Analysis {
    /// The function returns the dataflow graph for the given function id.
    fn get_fn_dataflow(&self, def_id: DefId) -> Option<DataFlowGraph>;

    /// The function returns the dataflow graph for all functions.
    fn get_all_dataflow(&self) -> DataFlowGraphMap;

    /// If there is a dataflow between `local1` and `local2` within the function specified by
    /// `def_id`, the function returns ture; otherwise, it returns false.
    fn has_flow_between(&self, def_id: DefId, local1: Local, local2: Local) -> bool;

    /// The function returns a set of Locals that are equivelent to the given `local`.
    fn collect_equivalent_locals(&self, def_id: DefId, local: Local) -> HashSet<Local>;

    /// The function returns an IndexVec of whether the returned Local depends on the parameter Local.
    fn get_fn_arg2ret(&self, def_id: DefId) -> Arg2Ret;

    /// The function returns the dataflow between the arguments and return value for all functions
    fn get_all_arg2ret(&self) -> Arg2RetMap;
}

impl fmt::Display for Arg2RetWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arg2ret: &Arg2Ret = &self.0;
        for (local, depends) in arg2ret.iter_enumerated() {
            if local.as_u32() > 0 {
                if *depends {
                    writeln!(f, "Argument {:?} ---> Return value _0", local)?;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for Arg2RetMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print dataflow analysis results ===")?;
        for (def_id, arg2ret) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(
                f,
                "Function: {:?}\n{}",
                fn_name,
                Arg2RetWrapper(arg2ret.clone())
            )?;
        }
        Ok(())
    }
}

impl Display for DataFlowGraphWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let graph = &self.0;
        write!(
            f,
            "Graph statistics: {} nodes, {} edges.\n",
            graph.nodes.len(),
            graph.edges.len()
        )?;
        if graph.param_ret_deps.len() > 1 {
            write!(f, "Return value dependencies: \n")?;
        }
        for (node_idx, deps) in graph.param_ret_deps.iter_enumerated() {
            if node_idx.as_u32() > 0 {
                if *deps {
                    write!(f, "Argument {:?} ---> Return value _0.\n", node_idx)?;
                }
            }
        }

        for (node_idx, node) in graph.nodes.iter_enumerated() {
            let node_adj: Vec<Local> = node
                .out_edges
                .iter()
                .map(|edge_idx| graph.edges[*edge_idx].dst)
                .collect();
            if !node_adj.is_empty() {
                write!(f, "Node {:?} -> Node {:?}\n", node_idx, node_adj)?;
            }
        }
        Ok(())
    }
}

impl Debug for DataFlowGraphWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Nodes:")?;
        for node in &self.0.nodes {
            writeln!(f, "  {:?}", node)?;
        }
        writeln!(f, "Edges:")?;
        for edge in &self.0.edges {
            writeln!(f, "  {:?}", edge)?;
        }
        Ok(())
    }
}

impl Display for DataFlowGraphMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "===Print dataflow analysis resuts===")?;
        for (def_id, dfg) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(
                f,
                "Function: {:?}\n{}",
                fn_name,
                DataFlowGraphWrapper(dfg.clone())
            )?;
        }
        Ok(())
    }
}

impl Debug for DataFlowGraphMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (def_id, dfg) in &self.0 {
            writeln!(
                f,
                "DefId: {:?}\n{:?}",
                def_id,
                DataFlowGraphWrapper(dfg.clone())
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum NodeOp {
    //warning: the fields are related to the version of the backend rustc version
    Nop,
    Err,
    Const(String, String),
    //Rvalue
    Use,
    Repeat,
    Ref,
    ThreadLocalRef,
    AddressOf,
    Len,
    Cast,
    BinaryOp,
    CheckedBinaryOp,
    NullaryOp,
    UnaryOp,
    Discriminant,
    Aggregate(AggKind),
    ShallowInitBox,
    CopyForDeref,
    RawPtr,
    //TerminatorKind
    Call(DefId),
    CallOperand, // the first in_edge is the func
}

#[derive(Clone, Debug)]
pub enum EdgeOp {
    Nop,
    //Operand
    Move,
    Copy,
    Const,
    //Mutability
    Immut,
    Mut,
    //Place
    Deref,
    Field(String),
    Downcast(String),
    Index,
    ConstIndex,
    SubSlice,
    SubType,
}

#[derive(Clone, Copy, Debug)]
pub enum AggKind {
    Array,
    Tuple,
    Adt(DefId),
    Closure(DefId),
    Coroutine(DefId),
    RawPtr,
}
