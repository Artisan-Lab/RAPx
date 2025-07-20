pub mod default;
use crate::utils::source::get_fn_name_byid;

use super::super::Analysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::def_id::LOCAL_CRATE;
use std::{collections::HashSet, fmt};

/// The data structure to store aliases for a set of functions.
pub type AAResultMap = FxHashMap<DefId, AAResult>;

/// This is a wrapper struct for displaying AAResultMap.
pub struct AAResultMapWrapper(pub AAResultMap);

/// This trait provides features related to alias analysis.
pub trait AliasAnalysis: Analysis {
    /// Return the aliases among the function arguments and return value of a specific function.
    fn get_fn_alias(&self, def_id: DefId) -> Option<AAResult>;
    /// Return the aliases among the function arguments and return value for all functions.
    fn get_all_fn_alias(&self) -> AAResultMap;
    /// Return the aliases among the function arguments and return value for functions of the local
    /// crate.
    fn get_local_fn_alias(&self) -> AAResultMap {
        self.get_all_fn_alias()
            .iter()
            .filter(|(def_id, _)| def_id.krate == LOCAL_CRATE)
            .map(|(k, v)| (*k, v.clone()))
            .collect()
    }
}

/// To store the alias relationships among arguments and return values.
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

    pub fn sort_alias_index(&mut self) {
        let alias_set = std::mem::take(&mut self.alias_set);
        let mut new_alias_set = HashSet::with_capacity(alias_set.len());

        for mut ra in alias_set.into_iter() {
            if ra.lhs_no() >= ra.rhs_no() {
                ra.swap();
            }
            new_alias_set.insert(ra);
        }
        self.alias_set = new_alias_set;
    }
}

impl fmt::Display for AAResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.aliases().is_empty() {
            write!(f, "null")?;
        } else {
            let joined = self
                .aliases()
                .iter()
                .map(|fact| format!("{}", fact))
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, "{joined}")?;
        }
        Ok(())
    }
}

impl fmt::Display for AAResultMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print alias analysis resuts ===")?;
        for (def_id, result) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Alias of {:?}: {}", fn_name, result)?;
        }
        Ok(())
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

    /// Swap the two elements of an alias pair, i.e., left to right, and right to left.
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.lhs_no, &mut self.rhs_no);
        std::mem::swap(&mut self.lhs_fields, &mut self.rhs_fields);
    }

    pub fn lhs_no(&self) -> usize {
        self.lhs_no
    }

    pub fn rhs_no(&self) -> usize {
        self.rhs_no
    }

    pub fn lhs_fields(&self) -> &[usize] {
        &self.lhs_fields
    }

    pub fn rhs_fields(&self) -> &[usize] {
        &self.rhs_fields
    }
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
