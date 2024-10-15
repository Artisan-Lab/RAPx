#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use rap::rap_debug;
use rap::utils::log::Verbosity;
use rap::{compile_time_sysroot, RapCallback, RAP_DEFAULT_ARGS};
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use std::env;

fn run_complier(args: &mut Vec<String>, callback: &mut RapCallback) -> i32 {
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }
    // Finally, add the default flags all the way in the beginning, but after the binary name.
    args.splice(1..1, RAP_DEFAULT_ARGS.iter().map(ToString::to_string));

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());

    let run_compiler = rustc_driver::RunCompiler::new(&args, callback);
    let exit_code = rustc_driver::catch_with_exit_code(move || run_compiler.run());
    rap_debug!("The arg for compilation is {:?}", args);

    exit_code
}

fn main() {
    // Parse the arguments from env.
    let mut debug = false;
    let mut args = vec![];
    let mut compiler = RapCallback::default();
    for arg in env::args() {
        match arg.as_str() {
            "-F" | "-uaf" => compiler.enable_safedrop(),
            "-M" | "-mleak" => compiler.enable_rcanary(),
            "-alias=mop" => compiler.enable_mop(),
            "-dataflow" => compiler.enable_dataflow(1),
            "-dataflow=debug" => compiler.enable_dataflow(2),
            "-UI" | "-uig" => compiler.enable_unsafety_isolation(1),
            "-doc" => compiler.enable_unsafety_isolation(2),
            "-upg" => compiler.enable_unsafety_isolation(3),
            "-ucons" => compiler.enable_unsafety_isolation(4),
            "-senryx" => compiler.enable_senryx(),
            "-callgraph" => compiler.enable_callgraph(),
            "-mir" => compiler.enable_show_mir(),
            "-debug" => debug = true,
            "-adt" => {}
            "-z3" => {}
            "-meta" => {}
            _ => args.push(arg),
        }
    }
    if debug == true {
        Verbosity::init_log(Verbosity::Debug).expect("Failed to init debugging log");
    } else {
        Verbosity::init_log(Verbosity::Info).expect("Failed to init info log");
    }
    rap_debug!("rap received arguments{:#?}", env::args());
    rap_debug!("arguments to rustc: {:?}", &args);

    let exit_code = run_complier(&mut args, &mut compiler);
    std::process::exit(exit_code)
}
