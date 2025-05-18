use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_span::Span;

use crate::rap_warn;
use crate::utils::log::are_spans_in_same_file;
use rustc_span::symbol::Symbol;

use annotate_snippets::Level;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;

use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};

pub struct BugRecords {
    pub df_bugs: FxHashMap<usize, Span>,
    pub df_bugs_unwind: FxHashMap<usize, Span>,
    pub uaf_bugs: FxHashSet<Span>,
    pub dp_bugs: FxHashSet<Span>,
    pub dp_bugs_unwind: FxHashSet<Span>,
}

impl BugRecords {
    pub fn new() -> BugRecords {
        BugRecords {
            df_bugs: FxHashMap::default(),
            df_bugs_unwind: FxHashMap::default(),
            uaf_bugs: FxHashSet::default(),
            dp_bugs: FxHashSet::default(),
            dp_bugs_unwind: FxHashSet::default(),
        }
    }

    pub fn is_bug_free(&self) -> bool {
        self.df_bugs.is_empty()
            && self.uaf_bugs.is_empty()
            && self.dp_bugs.is_empty()
            && self.dp_bugs_unwind.is_empty()
    }

    pub fn df_bugs_output(&self, fn_name: Symbol, span: Span) {
        if !self.df_bugs.is_empty() {
            rap_warn!("Double free detected in function {:}", fn_name);
            let code_source = span_to_source_code(span);
            let filename = span_to_filename(span);
            let mut snippet = Snippet::source(&code_source)
                .line_start(span_to_line_number(span))
                .origin(&filename)
                .fold(false);
            for i in self.df_bugs.iter() {
                //todo: remove this condition
                if are_spans_in_same_file(span, *i.1) {
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, *i.1))
                            .label("Double free detected."),
                    );
                }
            }
            let message = Level::Warning
                .title("Double free detected.")
                .snippet(snippet);
            let renderer = Renderer::styled();
            println!("{}", renderer.render(message));
        }
    }

    pub fn uaf_bugs_output(&self, fn_name: Symbol, span: Span) {
        if !self.uaf_bugs.is_empty() {
            rap_warn!("Use after free detected in function {:?}", fn_name);
            let code_source = span_to_source_code(span);
            let filename = span_to_filename(span);
            let mut snippet = Snippet::source(&code_source)
                .line_start(span_to_line_number(span))
                .origin(&filename)
                .fold(true);
            for i in self.uaf_bugs.iter() {
                //todo: remove this condition
                if are_spans_in_same_file(span, *i) {
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, *i))
                            .label("Use after free detected."),
                    );
                }
            }
            let message = Level::Warning
                .title("Use after free detected.")
                .snippet(snippet);
            let renderer = Renderer::styled();
            println!("{}", renderer.render(message));
        }
    }

    pub fn dp_bug_output(&self, fn_name: Symbol, span: Span) {
        let code_source = span_to_source_code(span);
        let filename = span_to_filename(span);
        if !self.dp_bugs.is_empty() {
            rap_warn!("Dangling pointer detected in function {:?}", fn_name);
            let mut snippet = Snippet::source(&code_source)
                .line_start(span_to_line_number(span))
                .origin(&filename)
                .fold(false);
            for i in self.dp_bugs.iter() {
                //todo: remove this condition
                if are_spans_in_same_file(span, *i) {
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, *i))
                            .label("Dangling pointer detected."),
                    );
                }
            }
            let message = Level::Warning
                .title("Dangling pointer detected.")
                .snippet(snippet);
            let renderer = Renderer::styled();
            println!("{}", renderer.render(message));
        }
        if !self.dp_bugs_unwind.is_empty() {
            rap_warn!(
                "Dangling pointer detected in function {:?} during unwinding.",
                fn_name
            );
            let mut snippet = Snippet::source(&code_source)
                .line_start(span_to_line_number(span))
                .origin(&filename)
                .fold(false);
            for i in self.dp_bugs_unwind.iter() {
                //todo: remove this condition
                if are_spans_in_same_file(span, *i) {
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, *i))
                            .label("Dangling pointer detected during unwinding."),
                    );
                }
            }
            let message = Level::Warning
                .title("Dangling pointer detected during unwinding.")
                .snippet(snippet);
            let renderer = Renderer::styled();
            println!("{}", renderer.render(message));
        }
    }
}
