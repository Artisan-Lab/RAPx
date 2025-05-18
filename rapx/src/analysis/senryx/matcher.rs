use crate::{analysis::utils::fn_info::get_sp_json, rap_warn};
use rustc_middle::mir::Const;
use rustc_middle::mir::Operand;
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq)]
pub struct Sp {
    pub sp_name: String,
    pub sank_set: HashSet<usize>,
}

impl std::hash::Hash for Sp {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.sp_name.hash(state);
    }
}

#[derive(Debug)]
pub struct UnsafeApi {
    pub api_name: String,
    pub sps: Vec<HashSet<Sp>>,
}

pub fn parse_unsafe_api(func_name: &str) -> Option<UnsafeApi> {
    let json_data = get_sp_json();
    let function_info = json_data.get(func_name)?;

    let params = function_info.as_object().map(|obj| {
        obj.iter()
            .filter_map(|(param_idx, props)| {
                let param_num: usize = param_idx.parse().ok()?;
                let sp_set = props.as_array().map(|arr| {
                    arr.iter()
                        .filter_map(|v| v.as_str())
                        .filter_map(|s| {
                            // split sp_name and sank set
                            let (name, nums) = match s.split_once(':') {
                                Some((n, ns)) => (n, ns.split(',')),
                                None => (s, "".split(',')),
                            };

                            // parse sank set num
                            let sank_set = nums.filter_map(|n| n.trim().parse().ok()).collect();

                            Some(Sp {
                                sp_name: name.to_string(),
                                sank_set,
                            })
                        })
                        .collect::<HashSet<_>>()
                })?;
                Some((param_num, sp_set))
            })
            .collect::<HashMap<_, _>>()
    })?;

    let mut sorted_params: Vec<_> = params.into_iter().collect();
    sorted_params.sort_by_key(|(k, _)| *k);

    Some(UnsafeApi {
        api_name: func_name.to_string(),
        sps: sorted_params.into_iter().map(|(_, v)| v).collect(),
    })
}

// (is const, value)
pub fn get_arg_place(arg: &Operand) -> (bool, usize) {
    match arg {
        Operand::Move(place) | Operand::Copy(place) => return (false, place.local.as_usize()),
        Operand::Constant(constant) => {
            let mut val = 0;
            match constant.const_ {
                Const::Ty(_ty, _const_value) => {
                    rap_warn!("const ty found!");
                }
                Const::Unevaluated(_unevaluated, _ty) => {}
                Const::Val(const_value, _ty) => {
                    if let Some(scalar) = const_value.try_to_scalar_int() {
                        val = scalar.to_uint(scalar.size()) as usize;
                    }
                }
            }
            return (true, val);
        }
    }
}
