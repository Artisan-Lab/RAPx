#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use rapx::{rap_info, rap_trace, utils::log::init_log, RapCallback, RAP_DEFAULT_ARGS};
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use std::env;

fn run_complier(args: &mut Vec<String>, callback: &mut RapCallback) {
    // Finally, add the default flags all the way in the beginning, but after the binary name.
    args.splice(1..1, RAP_DEFAULT_ARGS.iter().map(ToString::to_string));

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());

    rustc_driver::run_compiler(args, callback);
    rap_trace!("The arg for compilation is {:?}", args);
}

fn main() {
    // Parse the arguments from env.
    let mut args = vec![];
    let mut compiler = RapCallback::default();
    for arg in env::args() {
        match arg.as_str() {
            "-F" | "-F0" | "-F1" | "-F2" | "-uaf" => compiler.enable_safedrop(arg),
            "-M" | "-mleak" => compiler.enable_rcanary(),
            "-I" | "-infer" => compiler.enable_infer(),
            "-V" | "-verify" => compiler.enable_verify(),
            "-O" | "-opt" => compiler.enable_opt(1),
            "-opt=all" => compiler.enable_opt(2),
            "-opt=report" => compiler.enable_opt(0),
            "-alias" | "-alias0" | "-alias1" | "-alias2" => compiler.enable_alias(arg),
            "-ownedheap" => compiler.enable_ownedheap(),
            "-adg" => compiler.enable_api_dep(), // api dependency graph
            "-callgraph" => compiler.enable_callgraph(),
            "-dataflow" => compiler.enable_dataflow(1),
            "-ssa" => compiler.enable_ssa_transform(),
            "-range" => compiler.enable_range_analysis(1),
            "-range=print_mir" => compiler.enable_range_analysis(2),
            "-dataflow=debug" => compiler.enable_dataflow(2),
            "-audit" => compiler.enable_unsafety_isolation(1),
            "-doc" => compiler.enable_unsafety_isolation(2),
            "-upg" => compiler.enable_unsafety_isolation(3),
            "-ucons" => compiler.enable_unsafety_isolation(4),
            "-mir" => compiler.enable_show_mir(),
            _ => args.push(arg),
        }
    }
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));
    rap_info!("Start analysis with RAP.");
    rap_trace!("rap received arguments{:#?}", env::args());
    rap_trace!("arguments to rustc: {:?}", &args);

    run_complier(&mut args, &mut compiler);
}
