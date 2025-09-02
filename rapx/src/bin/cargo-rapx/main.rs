/*
    This is a cargo program to start RAP.
    The file references the cargo file for Miri: https://github.com/rust-lang/miri/blob/master/cargo-miri/src/main.rs
*/
#![feature(rustc_private)]

#[macro_use]
extern crate rapx;

use rapx::utils::log::{init_log, rap_error_and_exit};

mod args;
mod help;

mod utils;
use crate::utils::*;

mod cargo_check;

fn phase_cargo_rap() {
    rap_trace!("Start cargo-rapx.");

    // here we skip two args: cargo rapx
    let Some(arg) = args::get_arg(2) else {
        rap_error!("Expect command: e.g., `cargo rapx -help`.");
        return;
    };
    match arg {
        "-version" | "-v" | "--version" => {
            println!("{}", help::RAPX_VERSION);
            return;
        }
        "-help" | "-h" | "--help" => {
            println!("{}", help::RAPX_HELP);
            return;
        }
        _ => {}
    }

    cargo_check::run();
}

fn phase_rustc_wrapper() {
    rap_trace!("Launch cargo-rapx again triggered by cargo check.");

    let is_direct = args::is_current_compile_crate();
    // rapx only checks local crates
    if is_direct && args::filter_crate_type() {
        run_rap();
        return;
    }

    // for dependencies and some special crate types, run rustc as usual
    run_rustc();
}

fn main() {
    /* This function will be enteredd twice:
       1. When we run `cargo rapx ...`, cargo dispatches the execution to cargo-rapx.
      In this step, we set RUSTC_WRAPPER to cargo-rapx, and execute `cargo check ...` command;
       2. Cargo check actually triggers `path/cargo-rapx path/rustc` according to RUSTC_WRAPPER.
          Because RUSTC_WRAPPER is defined, Cargo calls the command: `$RUSTC_WRAPPER path/rustc ...`
    */

    // Init the log_system
    init_log().expect("Failed to init log.");

    match args::get_arg(1).unwrap() {
        s if s.ends_with("rapx") => phase_cargo_rap(),
        s if s.ends_with("rustc") => phase_rustc_wrapper(),
        _ => rap_error_and_exit(
            "rapx must be called with either `rap` or `rustc` as first argument.",
        ),
    }
}
