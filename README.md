# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/logo.png)
RAPx (Rust Analysis Platform with Extensions) [![license](https://img.shields.io/github/license/Artisan-Lab/RAPx)](./LICENSE-MPL) is an advanced static analysis platform for Rust, developed by researchers at [Artisan-Lab](https://hxuhack.github.io), Fudan University. It provides an extensible framework for building and integrating powerful analysis capabilities that go beyond those available in the standard rustc compiler, empowering developers to reason about safety, robustness, and performance at a deeper level.

RAPx is available on crates.io. [![crates.io](https://img.shields.io/crates/v/rapx.svg)](https://crates.io/crates/rapx)

## Features
# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/feature.png)
RAPx is structured into two layers: a core layer offering essential program analysis algorithms (e.g., alias and dataflow analysis), and an application layer implementing specific tasks such as bug detection. This separation of concerns promotes modular development and fosters collaboration between algorithm and application developers.

The project is still under heavy development. For further details, please refer to the [RAPx-Book](https://artisan-lab.github.io/RAPx-Book).

## Quick Start

Install `nightly-2025-06-02` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2025-06-02 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2025-06-02 install rapx --git https://github.com/Artisan-Lab/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2025-06-02 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2025-06-02
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
    -alias          perform alias analysis (meet-over-paths by default)
    -adg            generate API dependency graphs
    -audit          (under development) generate unsafe code audit units
    -callgraph      generate callgraphs
    -dataflow       generate dataflow graphs
    -ownedheap      analyze if the type holds a piece of memory on heap
    -range          perform range analysis
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


