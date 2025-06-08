use super::call_graph_helper::CallGraphInfo;
use regex::Regex;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{FnDef, Instance, InstanceKind, TyCtxt, TypingEnv};

pub struct CallGraphVisitor<'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &'tcx mir::Body<'tcx>,
    call_graph_info: &'b mut CallGraphInfo,
}

impl<'b, 'tcx> CallGraphVisitor<'b, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &'tcx mir::Body<'tcx>,
        call_graph_info: &'b mut CallGraphInfo,
    ) -> Self {
        Self {
            tcx: tcx,
            def_id: def_id,
            body: body,
            call_graph_info: call_graph_info,
        }
    }

    pub fn add_in_call_graph(
        &mut self,
        caller_def_path: &String,
        callee_def_id: DefId,
        callee_def_path: &String,
    ) {
        if let Some(caller_id) = self.call_graph_info.get_noed_by_path(caller_def_path) {
            if let Some(callee_id) = self.call_graph_info.get_noed_by_path(callee_def_path) {
                self.call_graph_info
                    .add_funciton_call_edge(caller_id, callee_id);
            } else {
                self.call_graph_info
                    .add_node(callee_def_id, callee_def_path);
                if let Some(callee_id) = self.call_graph_info.get_noed_by_path(callee_def_path) {
                    self.call_graph_info
                        .add_funciton_call_edge(caller_id, callee_id);
                }
            }
        }
    }

    pub fn visit(&mut self) {
        let caller_path_str = self.tcx.def_path_str(self.def_id);
        self.call_graph_info.add_node(self.def_id, &caller_path_str);
        for (_, data) in self.body.basic_blocks.iter().enumerate() {
            let terminator = data.terminator();
            self.visit_terminator(&terminator);
        }
    }

    fn add_to_call_graph(&mut self, callee_def_id: DefId, is_virtual: Option<bool>) {
        let caller_def_path = self.tcx.def_path_str(self.def_id);
        let mut callee_def_path = self.tcx.def_path_str(callee_def_id);
        if let Some(judge) = is_virtual {
            if judge {
                let re = Regex::new(r"(?<dyn>\w+)::(?<func>\w+)").unwrap();
                let Some(caps) = re.captures(&callee_def_path) else {
                    return;
                };
                callee_def_path = format!("(dyn trait) <* as {}>::{}", &caps["dyn"], &caps["func"]);
            }
        }

        // let callee_location = self.tcx.def_span(callee_def_id);
        if callee_def_id == self.def_id {
            // Recursion
            println!("Warning! Find a recursion function which may cause stackoverflow!")
        }
        self.add_in_call_graph(&caller_def_path, callee_def_id, &callee_def_path);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>) {
        if let mir::TerminatorKind::Call { func, .. } = &terminator.kind {
            if let mir::Operand::Constant(constant) = func {
                if let FnDef(callee_def_id, callee_substs) = constant.const_.ty().kind() {
                    let ty_env = TypingEnv::post_analysis(self.tcx, self.def_id);
                    if let Ok(Some(instance)) =
                        Instance::try_resolve(self.tcx, ty_env, *callee_def_id, callee_substs)
                    {
                        let mut is_virtual = false;
                        // Try to analysis the specific type of callee.
                        let instance_def_id = match instance.def {
                            InstanceKind::Item(def_id) => Some(def_id),
                            InstanceKind::Intrinsic(def_id) => Some(def_id),
                            InstanceKind::VTableShim(def_id) => Some(def_id),
                            InstanceKind::ReifyShim(def_id, _) => Some(def_id),
                            InstanceKind::FnPtrShim(def_id, _) => Some(def_id),
                            InstanceKind::Virtual(def_id, _) => {
                                is_virtual = true;
                                Some(def_id)
                            }
                            InstanceKind::ClosureOnceShim { call_once, .. } => Some(call_once),
                            InstanceKind::ConstructCoroutineInClosureShim {
                                coroutine_closure_def_id,
                                ..
                            } => Some(coroutine_closure_def_id),
                            InstanceKind::ThreadLocalShim(def_id) => Some(def_id),
                            InstanceKind::DropGlue(def_id, _) => Some(def_id),
                            InstanceKind::FnPtrAddrShim(def_id, _) => Some(def_id),
                            InstanceKind::AsyncDropGlueCtorShim(def_id, _) => Some(def_id),
                            InstanceKind::CloneShim(def_id, _) => {
                                if !self.tcx.is_closure_like(def_id) {
                                    // Not a closure
                                    Some(def_id)
                                } else {
                                    None
                                }
                            }
                            _ => todo!(),
                        };
                        if let Some(instance_def_id) = instance_def_id {
                            self.add_to_call_graph(instance_def_id, Some(is_virtual));
                        }
                    } else {
                        // Although failing to get specific type, callee is still useful.
                        self.add_to_call_graph(*callee_def_id, None);
                    }
                }
            }
        }
    }
}
