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
    let raw_args: Vec<String> = env::args().collect();
    let mut i = 0;
    while i < raw_args.len() {
        let arg = &raw_args[i];
        match arg.as_str() {
            "-alias" | "-alias0" | "-alias1" | "-alias2" => {
                compiler.enable_alias(arg.to_string());
            }
            "-adg" => {
                compiler.enable_api_dependency(); // api dependency graph
            }
            "-callgraph" => {
                compiler.enable_callgraph();
            }
            "-dataflow" => {
                compiler.enable_dataflow(1);
            }
            "-dataflow=debug" => {
                compiler.enable_dataflow(2);
            }
            "-ownedheap" => {
                compiler.enable_ownedheap();
            }
            "-range" => {
                compiler.enable_range_analysis(1);
            }
            "-range=print_mir" => {
                compiler.enable_range_analysis(2);
            }
            "-pathcond" => {
                compiler.enable_range_analysis(3);
            }
            "-test" => {
                compiler.enable_test();
            }
            "-F" | "-F0" | "-F1" | "-F2" | "-uaf" => {
                compiler.enable_safedrop(arg.to_string());
            }
            "-I" | "-infer" => {
                compiler.enable_infer();
            }
            "-M" | "-mleak" => {
                compiler.enable_rcanary();
            }
            "-V" | "-verify" => {
                compiler.enable_verify();
            }
            "-O" | "-opt" => {
                compiler.enable_opt(1);
            }
            "-opt=all" => {
                compiler.enable_opt(2);
            }
            "-opt=report" => {
                compiler.enable_opt(0);
            }
            "-ssa" => {
                compiler.enable_ssa_transform();
            }
            "-audit" => {
                compiler.enable_unsafety_isolation(1);
            }
            "-doc" => {
                compiler.enable_unsafety_isolation(2);
            }
            "-upg" => {
                compiler.enable_unsafety_isolation(3);
            }
            "-ucons" => {
                compiler.enable_unsafety_isolation(4);
            }
            "-mir" => {
                compiler.enable_show_mir();
            }
            "-verify-std" => {
                let mut func_to_be_verified = vec![];
                // Collect function names until next option or end
                i += 1; // Move to the next argument
                while i < raw_args.len() && !raw_args[i].starts_with('-') {
                    func_to_be_verified.push(raw_args[i].clone());
                    i += 1;
                }
                compiler.enable_verify_std(func_to_be_verified);
                continue; // Skip the increment at the end
            }
            _ => {
                args.push(arg.clone());
            }
        }
        i += 1;
    }
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));
    rap_info!("Start analysis with RAPx.");
    rap_trace!("rap received arguments{:#?}", env::args());
    rap_trace!("arguments to rustc: {:?}", &args);

    run_complier(&mut args, &mut compiler);
}
