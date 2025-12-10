use annotate_snippets::{Level, Renderer, Snippet};
use rustc_data_structures::fx::FxHashMap;
use rustc_span::{Span, symbol::Symbol};

use crate::utils::log::{
    are_spans_in_same_file, get_basic_block_span, get_variable_name, relative_pos_range,
    span_to_filename, span_to_line_number, span_to_source_code,
};
use rustc_middle::mir::Body;

#[derive(Debug)]
pub struct TyBug {
    pub drop_bb: usize,
    pub drop_id: usize,
    pub trigger_bb: usize,
    pub trigger_id: usize,
    pub span: Span,
    pub confidence: usize,
}

/*
 * For each bug in the HashMap, the key is local of the value.
 */
pub struct BugRecords {
    pub df_bugs: FxHashMap<usize, TyBug>,
    pub df_bugs_unwind: FxHashMap<usize, TyBug>,
    pub uaf_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs_unwind: FxHashMap<usize, TyBug>,
}

impl BugRecords {
    pub fn new() -> BugRecords {
        BugRecords {
            df_bugs: FxHashMap::default(),
            df_bugs_unwind: FxHashMap::default(),
            uaf_bugs: FxHashMap::default(),
            dp_bugs: FxHashMap::default(),
            dp_bugs_unwind: FxHashMap::default(),
        }
    }

    pub fn is_bug_free(&self) -> bool {
        self.df_bugs.is_empty()
            && self.df_bugs_unwind.is_empty()
            && self.uaf_bugs.is_empty()
            && self.dp_bugs.is_empty()
            && self.dp_bugs_unwind.is_empty()
    }

    pub fn df_bugs_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        // Double Free (Normal)
        self.emit_bug_reports(
            body, &self.df_bugs, fn_name, span,
            "Double free detected",
            "Double free detected.",
            |bug, drop_name, trigger_name, drop_bb_str, trigger_bb_str| {
                format!(
                    "Double free (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is dropped at {}.",
                    bug.confidence,
                    span_to_filename(bug.span),
                    span_to_line_number(bug.span),
                    drop_name, trigger_name,
                    drop_name, drop_bb_str,
                    trigger_name, trigger_bb_str
                )
            }
        );

        // Double Free (Unwind)
        self.emit_bug_reports(
            body, &self.df_bugs_unwind, fn_name, span,
            "Double free detected",
            "Double free detected during unwinding.",
            |bug, drop_name, trigger_name, drop_bb_str, trigger_bb_str| {
                format!(
                    "Double free (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is dropped at {}.",
                    bug.confidence,
                    span_to_filename(bug.span),
                    span_to_line_number(bug.span),
                    drop_name, trigger_name,
                    drop_name, drop_bb_str,
                    trigger_name, trigger_bb_str
                )
            }
        );
    }

    pub fn uaf_bugs_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        self.emit_bug_reports(
            body, &self.uaf_bugs, fn_name, span,
            "Use-after-free detected",
            "Use-after-free detected.",
            |bug, drop_name, trigger_name, drop_bb_str, trigger_bb_str| {
                format!(
                    "Use-after-free (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} is used at {}.",
                    bug.confidence,
                    span_to_filename(bug.span),
                    span_to_line_number(bug.span),
                    drop_name, trigger_name,
                    drop_name, drop_bb_str,
                    trigger_name, trigger_bb_str
                )
            }
        );
    }

    pub fn dp_bug_output<'tcx>(&self, body: &Body<'tcx>, fn_name: Symbol, span: Span) {
        // Dangling Pointer (Normal)
        self.emit_bug_reports(
            body, &self.dp_bugs, fn_name, span,
            "Dangling pointer detected",
            "Dangling pointer detected.",
            |bug, drop_name, trigger_name, drop_bb_str, _trigger_bb_str| {
                format!(
                    "Dangling pointer (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} became dangling.",
                    bug.confidence,
                    span_to_filename(bug.span),
                    span_to_line_number(bug.span),
                    drop_name, trigger_name,
                    drop_name, drop_bb_str,
                    trigger_name,
                )
            }
        );

        // Dangling Pointer (Unwind)
        self.emit_bug_reports(
            body, &self.dp_bugs_unwind, fn_name, span,
            "Dangling pointer detected during unwinding",
            "Dangling pointer detected during unwinding.",
            |bug, drop_name, trigger_name, drop_bb_str, _trigger_bb_str| {
                format!(
                    "Dangling pointer (confidence {}%): Location in file {} line {}.\n    | MIR detail: Value {} and {} are alias.\n    | MIR detail: {} is dropped at {}; {} became dangling.",
                    bug.confidence,
                    span_to_filename(bug.span),
                    span_to_line_number(bug.span),
                    drop_name, trigger_name,
                    drop_name, drop_bb_str,
                    trigger_name,
                )
            }
        );
    }

    fn emit_bug_reports<'tcx, F>(
        &self,
        body: &Body<'tcx>,
        bugs: &FxHashMap<usize, TyBug>,
        fn_name: Symbol,
        span: Span,
        log_msg: &str,
        title: &str,
        detail_formatter: F,
    ) where
        F: Fn(&TyBug, &str, &str, &str, &str) -> String,
    {
        if bugs.is_empty() {
            return;
        }

        rap_warn!("{} in function {:?}", log_msg, fn_name);

        let code_source = span_to_source_code(span);
        let filename = span_to_filename(span);
        let renderer = Renderer::styled();

        for bug in bugs.values() {
            if are_spans_in_same_file(span, bug.span) {
                let format_debug_info = |id: usize| -> String {
                    let local = rustc_middle::mir::Local::from_usize(id);
                    let name_opt = get_variable_name(body, id); // 假设这个函数在你当前作用域可用
                    let decl_span = body.local_decls[local].source_info.span;
                    let location = format!(
                        "{}:{}",
                        span_to_filename(decl_span),
                        span_to_line_number(decl_span)
                    );
                    match name_opt {
                        Some(name) => format!("_{}({}, {})", id, name, location),
                        None => format!("_{}(_, {})", id, location),
                    }
                };

                let format_bb_info = |bb_id: usize| -> String {
                    let bb_span = get_basic_block_span(body, bb_id);
                    let location = format!(
                        "{}:{}",
                        span_to_filename(bb_span),
                        span_to_line_number(bb_span)
                    );
                    format!("BB{}({})", bb_id, location)
                };

                let drop_name = format_debug_info(bug.drop_id);
                let trigger_name = format_debug_info(bug.trigger_id);

                let drop_bb_str = format_bb_info(bug.drop_bb);
                let trigger_bb_str = format_bb_info(bug.trigger_bb);

                let detail = detail_formatter(
                    bug,
                    &drop_name,
                    &trigger_name,
                    &drop_bb_str,
                    &trigger_bb_str,
                );

                let mut snippet = Snippet::source(&code_source)
                    .line_start(span_to_line_number(span))
                    .origin(&filename)
                    .fold(false);

                snippet = snippet.annotation(
                    Level::Warning
                        .span(relative_pos_range(span, bug.span))
                        .label(&detail),
                );

                let message = Level::Warning.title(title).snippet(snippet);

                println!("{}", renderer.render(message));
            }
        }
    }
}
