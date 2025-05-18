# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/rapx_logo.png)
RAPx is a static Rust analysis platform developed by researchers at [Artisan-Lab](https://hxuhack.github.io), Fudan University. The project aims to provide a foundation for Rust programmers to develop or use advanced static analysis features beyond those offered by the rustc compiler. For further details, please refer to the [RAPx-Book](https://artisan-lab.github.io/RAPx-Book).

The project is still under heavy development. 

## Quick Start

Install `nightly-2025-02-01` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2025-02-01 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2025-02-01 install rapx --git https://github.com/Artisan-Lab/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2025-02-01 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2025-02-01
```

Check out supported options with `-help`:

```shell
cargo rapx -help

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
    -alias          perform alias analysis (meet-over-paths)
    -adg            generate API dependency graphs
    -callgraph      generate callgraphs
    -dataflow       (not supported yet) generate dataflow graphs
    -heap           analyze if the type holds a piece of memory on heap
    -audit          (under development) generate unsafe code audit units
```

If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`. 

RAPx supports the following environment variables (values are case insensitive):

| var             | default when absent | one of these values | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAP_LOG`       | info                | debug, info, warn   | verbosity of logging         |
| `RAP_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAP_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |

For `RAP_RECURSIVE`:
* none: check for current folder
* shallow: check for current workpace members
* deep: check for all workspaces from current folder
 
NOTE: rapx will enter each member folder to do the check.


