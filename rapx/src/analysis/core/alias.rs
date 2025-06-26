pub mod mop;
use super::super::Analysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use std::{collections::HashSet, fmt};

pub trait AliasAnalysis<T>: Analysis {
    fn get_fn_alias(&mut self, def_id: DefId) -> T;
    fn get_all_fn_alias(&mut self) -> FxHashMap<DefId, T>;
}

/// To store the alias relationships among arguments and return values.
///
/// Each function may have multiple return instructions, leading to different RetAlias.
#[derive(Debug, Clone)]
pub struct AAResult {
    arg_size: usize,
    alias_set: HashSet<AAFact>,
}

impl AAResult {
    pub fn new(arg_size: usize) -> AAResult {
        Self {
            arg_size,
            alias_set: HashSet::new(),
        }
    }

    pub fn arg_size(&self) -> usize {
        self.arg_size
    }

    pub fn aliases(&self) -> &HashSet<AAFact> {
        &self.alias_set
    }

    pub fn add_alias(&mut self, alias: AAFact) {
        self.alias_set.insert(alias);
    }

    pub fn len(&self) -> usize {
        self.alias_set.len()
    }
}

impl fmt::Display for AAResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.aliases()
                .iter()
                .map(|alias| format!("{}", alias))
                .collect::<Vec<String>>()
                .join(",")
        )
    }
}

/// AAFact is used to store the alias relationships between two places.
/// The result is field-sensitive.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct AAFact {
    pub lhs_no: usize,
    pub lhs_fields: Vec<usize>,
    pub rhs_no: usize,
    pub rhs_fields: Vec<usize>,
}

impl AAFact {
    pub fn new(lhs_no: usize, rhs_no: usize) -> AAFact {
        AAFact {
            lhs_no,
            lhs_fields: Vec::<usize>::new(),
            rhs_no,
            rhs_fields: Vec::<usize>::new(),
        }
    }

    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs_no, &mut self.rhs_no);
        std::mem::swap(&mut self.lhs_fields, &mut self.rhs_fields);
    }
}

fn aa_place_desc_str(no: usize, fields: &[usize], field_sensitive: bool) -> String {
    let mut result = String::new();
    result.push_str(&no.to_string());
    if !field_sensitive {
        return result;
    }
    for num in fields.iter() {
        result.push('.');
        result.push_str(&num.to_string());
    }
    result
}

impl fmt::Display for AAFact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({},{})",
            aa_place_desc_str(self.lhs_no, &self.lhs_fields, true),
            aa_place_desc_str(self.rhs_no, &self.rhs_fields, true)
        )
    }
}
