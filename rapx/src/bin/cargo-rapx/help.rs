pub const RAPX_HELP: &str = r#"
Usage:
    cargo rapx [rapx options] -- [cargo check options]

RAPx Options:

Application:
    -F or -uaf      use-after-free/double free detection.
    -M or -mleak    memory leakage detection.
    -O or -opt      automatically detect code optimization chances.
    -I or -infer    (under development) infer the safety properties required by unsafe APIs.
    -V or -verify   (under development) verify if the safety requirements of unsafe API are satisfied.

Analysis:
    -alias          perform alias analysis (meet-over-paths by default)
    -adg            generate API dependency graphs
    -audit          (under development) generate unsafe code audit units
    -callgraph      generate callgraphs
    -dataflow       generate dataflow graphs
    -heap           analyze if the type holds a piece of memory on heap
    -range          perform range analysis

General command: 
    -help:     show help information
    -version:  show the version of RAPx

NOTE: multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx -F -M`
will perform two kinds of detection in a row.

e.g.
1. detect use-after-free and memory leak for a riscv target:
   cargo rapx -F -M -- --target riscv64gc-unknown-none-elf
2. detect use-after-free and memory leak for tests:
   cargo rapx -F -M -- --tests
3. detect use-after-free and memory leak for all members:
   cargo rapx -F -M -- --workspace

Environment Variables (Values are case insensitive):
    RAP_LOG          verbosity of logging: trace, debug, info, warn
                     trace: print all the detailed RAP execution traces.
                     debug: display intermidiate analysis results.
                     warn: show bugs detected only.

    RAP_CLEAN        run cargo clean before check: true, false
                     * true is the default value except that false is set

    RAP_RECURSIVE    scope of packages to check: none, shallow, deep
                     * none or the variable not set: check for current folder
                     * shallow: check for current workpace members
                     * deep: check for all workspaces from current folder
                      
                     NOTE: for shallow or deep, rapx will enter each member
                     folder to do the check.
"#;

pub const RAPX_VERSION: &str = r#"
rapx version 0.21
released at 2025-05-16
developped by artisan-lab @ Fudan university 
"#;
