use rustc_middle::mir::Operand;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

use crate::analysis::utils::fn_info::get_sp_json;

use super::{
    contracts::{
        abstract_state::PathInfo,
        checker::{Checker, SliceFromRawPartsChecker},
        contract::check_contract,
    },
    visitor::CheckResult,
};

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

pub fn match_unsafe_api_and_check_contracts<'tcx, T>(
    func_name: &str,
    args: &Box<[Spanned<Operand>]>,
    abstate: &PathInfo<'tcx>,
    span: Span,
    _ty: T,
) -> Option<CheckResult<'tcx>> {
    let checker: Option<Box<dyn Checker>> = match func_name {
        "core::slice::raw::from_raw_parts" | "core::slice::raw::from_raw_parts_mut" => {
            Some(Box::new(SliceFromRawPartsChecker::<T>::new()))
        }
        _ => None,
    };

    // println!("{:?}",parse_unsafe_api(func_name));
    if let Some(c) = checker {
        return Some(process_checker(&*c, args, abstate, func_name, span));
    }
    None
}

fn process_checker<'tcx>(
    checker: &dyn Checker<'tcx>,
    args: &Box<[Spanned<Operand>]>,
    abstate: &PathInfo<'tcx>,
    func_name: &str,
    span: Span,
) -> CheckResult<'tcx> {
    let mut check_result = CheckResult::new(func_name, span);
    for (idx, contracts_vec) in checker.variable_contracts().iter() {
        for contract in contracts_vec {
            let arg_place = get_arg_place(&args[*idx].node);
            if arg_place == 0 {
                continue;
            }
            if let Some(abstate_item) = abstate.state_map.get(&arg_place) {
                if !check_contract(contract, &abstate_item.clone()) {
                    check_result.failed_contracts.push((*idx, contract.clone()));
                } else {
                    check_result.passed_contracts.push((*idx, contract.clone()));
                }
            }
        }
    }
    check_result
}

pub fn get_arg_place(arg: &Operand) -> usize {
    match arg {
        Operand::Move(place) => place.local.as_usize(),
        Operand::Copy(place) => place.local.as_usize(),
        _ => 0,
    }
}
