# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/rapx_logo.png)
RAPx is a static Rust analysis platform developed by researchers at [Artisan-Lab](https://hxuhack.github.io), Fudan University. The project aims to provide a foundation for Rust programmers to develop or use advanced static analysis features beyond those offered by the rustc compiler. For further details, please refer to the [RAPx-Book](https://artisan-lab.github.io/RAPx-Book).

The project is still under heavy development. 

## Quick Start

Install `nightly-2024-10-12` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2024-10-12 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2024-10-12 install rapx --git https://github.com/Artisan-Lab/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `cargo-rapx` with [toolchain override shorthand syntax].

[toolchain override shorthand syntax]: https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand

```shell
cargo rapx [rapx options] -- [cargo check options]

where `-- [cargo check options]` is optional, and if specified, they are passed to cargo check.
```

Alternatively, you can switch to the pinned toolchain ahead of time:

```rust
# set up rapx's toolchain as default
rustup default nightly-2024-10-12

# run cargo rapx without +toolchain syntax any more
cargo rapx [rapx options] -- [cargo check options]
```

Check out supported options with `-help`:

```shell
cargo rapx -help 
```
or by manually specifying the toolchain version.
```shell
cargo +nightly-2024-10-12 rapx -help 
```

Environment variables (Values are case insensitive):

| var             | default when absent | one of these values | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAP_LOG`       | info                | debug, info, warn   | verbosity of logging         |
| `RAP_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAP_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |

For `RAP_RECURSIVE`:
* none: check for current folder
* shallow: check for current workpace members
* deep: check for all workspaces from current folder
 
NOTE: for shallow or deep, rapx will enter each member folder to do the check.

### Alias Analysis
The following command analyzes each function and output the aliases.
```
RAP_LOG=debug cargo rapx -alias=mop
```
If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`.

### API-dependency Graph
The following command generates the API-dependency graph, which is useful for code synthesis, e.g., generating fuzz drivers.
```
cargo rapx -api-dep
```
The generated dot file can be visualized via graphviz.
```
dot -Tpng api_graph.dot -o output.png
```

### Use-After-Free Detection
Detect bugs such as use-after-free and double free in Rust crates caused by unsafe code.
```shell
cargo rapx -F
```

### Memory Leakage Detection 
Detect memory leakage bugs caused by apis like [ManuallyDrop](https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html) and [into_raw()](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.into_raw).

```shell
cargo rapx -M
```

