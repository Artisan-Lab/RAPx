use super::dep_edge::DepEdge;
use super::dep_node::DepNode;
use crate::analysis::core::api_dependency::ApiDependencyGraph;
use serde::{
    Serialize,
    ser::{SerializeMap, SerializeSeq},
};
use std::path::Path;

#[derive(Serialize, Debug)]
struct NodeInfo {
    id: usize,
    kind: String,
    path: String,
    args: Vec<String>,
}

#[derive(Serialize, Debug)]
struct EdgeInfo {
    id: usize,
    kind: String,
    from: usize,
    to: usize,
}

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn dump_to_json(&self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let file = std::fs::File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }
}

impl<'tcx> Serialize for ApiDependencyGraph<'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(Some(2))?;
        let mut nodes = Vec::new();
        for index in self.graph.node_indices() {
            let node_info = match self.graph[index] {
                DepNode::Api(fn_did, args) => NodeInfo {
                    id: index.index(),
                    kind: "api".to_owned(),
                    path: self.tcx.def_path_str(fn_did),
                    args: args.iter().map(|arg| arg.to_string()).collect(),
                },
                DepNode::Ty(ty) => NodeInfo {
                    id: index.index(),
                    kind: "type".to_owned(),
                    path: ty.ty().to_string(),
                    args: vec![],
                },
            };
            nodes.push(node_info);
        }
        let mut edges = Vec::new();
        for index in self.graph.edge_indices() {
            let kind = match self.graph[index] {
                DepEdge::Arg(no) => "arg".to_owned(),
                DepEdge::Ret => "ret".to_owned(),
                DepEdge::Transform(kind) => format!("transform({})", kind),
            };
            let (from, to) = self.graph.edge_endpoints(index).unwrap();
            let (from, to) = (from.index(), to.index());
            edges.push(EdgeInfo {
                id: index.index(),
                kind: "arg".to_owned(),
                from,
                to,
            });
        }
        map.serialize_entry("nodes", &nodes)?;
        map.serialize_entry("edges", &edges)?;
        map.end()
    }
}
