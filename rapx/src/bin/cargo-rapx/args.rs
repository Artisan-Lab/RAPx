use std::{
    env,
    path::{Path, PathBuf},
    sync::LazyLock,
};

struct Arguments {
    /// a collection of `std::env::args()`
    args: Vec<String>,
    /// options as first half before -- in args
    args_group1: Vec<String>,
    /// options as second half after -- in args
    args_group2: Vec<String>,
    current_exe_path: PathBuf,
    rap_clean: bool,
}

impl Arguments {
    // Get value from `name=val` or `name val`.
    fn get_arg_flag_value(&self, name: &str) -> Option<&str> {
        let mut args = self.args_group1.iter();

        while let Some(arg) = args.next() {
            if !arg.starts_with(name) {
                continue;
            }
            // Strip leading `name`.
            let suffix = &arg[name.len()..];
            if suffix.is_empty() {
                // This argument is exactly `name`; the next one is the value.
                return args.next().map(|x| x.as_str());
            } else if let Some(arg) = suffix.strip_prefix('=') {
                // This argument is `name=value`; get the value.
                // Strip leading `=`.
                return Some(arg);
            }
        }

        None
    }

    fn new() -> Self {
        fn rap_clean() -> bool {
            match env::var("RAP_CLEAN")
                .ok()
                .map(|s| s.trim().to_ascii_lowercase())
                .as_deref()
            {
                Some("false") => false,
                _ => true, // clean is the preferred behavior
            }
        }

        let args: Vec<_> = env::args().collect();
        let path = env::current_exe().expect("Current executable path invalid.");
        rap_trace!("Current exe: {path:?}\tReceived args: {args:?}");
        let [args_group1, args_group2] = split_args_by_double_dash(&args);

        Arguments {
            args,
            args_group1,
            args_group2,
            current_exe_path: path,
            rap_clean: rap_clean(),
        }
    }

    // In rustc phase:
    // Determines if we are being invoked to build crate for local crate.
    // Cargo passes the file name as a relative address when building the local crate,
    fn is_current_compile_crate(&self) -> bool {
        let mut args = self.args_group1.iter();
        let entry_path = match args.find(|s| s.ends_with(".rs")) {
            Some(path) => Path::new(path),
            None => return false,
        };
        entry_path.is_relative()
            || entry_path.ends_with("lib/rustlib/src/rust/library/std/src/lib.rs")
            || entry_path.ends_with("lib/rustlib/src/rust/library/core/src/lib.rs")
            || entry_path.ends_with("lib/rustlib/src/rust/library/alloc/src/lib.rs")
    }
}

pub fn rap_clean() -> bool {
    ARGS.rap_clean
}

fn split_args_by_double_dash(args: &[String]) -> [Vec<String>; 2] {
    let mut args_iter = args.iter().skip(2);
    
    let mut rap_args = Vec::new();
    let mut cargo_args = Vec::new();
    
    // Process args before "--" separator (if it exists)
    let mut found_separator = false;
    while let Some(arg) = args_iter.next() {
        if arg == "--" {
            found_separator = true;
            break;
        }
        
        // Check if this is a cargo-specific flag that should be forwarded to cargo
        // Cargo unstable flags start with -Z
        if arg.starts_with("-Z") {
            cargo_args.push(arg.to_owned());
            // If -Z is followed by a separate value (not -Z<value>), also take the next arg
            if arg == "-Z" {
                if let Some(next_arg) = args_iter.next() {
                    cargo_args.push(next_arg.to_owned());
                }
            }
        } else {
            rap_args.push(arg.to_owned());
        }
    }
    
    // If we found "--", everything after it goes to cargo_args
    if found_separator {
        cargo_args.extend(args_iter.map(|arg| arg.to_owned()));
    }
    
    rap_trace!("split_args_by_double_dash: rap_args={rap_args:?}, cargo_args={cargo_args:?}");
    
    [rap_args, cargo_args]
}

static ARGS: LazyLock<Arguments> = LazyLock::new(Arguments::new);

pub fn get_arg_flag_value(name: &str) -> Option<&'static str> {
    ARGS.get_arg_flag_value(name)
}

/// `cargo rapx [rapx options] -- [cargo check options]`
///
/// Options before the first `--` are arguments forwarding to rapx.
/// Stuff all after the first `--` are arguments forwarding to cargo check.
pub fn rap_and_cargo_args() -> [&'static [String]; 2] {
    [&ARGS.args_group1, &ARGS.args_group2]
}

/// If a crate being compiled is local in rustc phase.
pub fn is_current_compile_crate() -> bool {
    ARGS.is_current_compile_crate()
}

/// Returns true for crate types to be checked;
/// returns false for some special crate types that can't be handled by rapx.
/// For example, checking proc-macro crates or build.rs can cause linking errors in rapx.
pub fn filter_crate_type() -> bool {
    if let Some(s) = get_arg_flag_value("--crate-type") {
        return match s {
            "proc-macro" => false,
            "bin" if get_arg_flag_value("--crate-name") == Some("build_script_build") => false,
            _ => true,
        };
    }
    // NOTE: tests don't have --crate-type, they are handled with --test by rustc.
    true
}

pub fn get_arg(pos: usize) -> Option<&'static str> {
    ARGS.args.get(pos).map(|x| x.as_str())
}

pub fn skip2() -> &'static [String] {
    ARGS.args.get(2..).unwrap_or(&[])
}

pub fn current_exe_path() -> &'static Path {
    &ARGS.current_exe_path
}

/// NOTE: for simplicify in rapx argument forwarding, only `-timeout=` is correctly handled,
/// even though both flavors are accepted here.
pub fn timeout() -> Option<u64> {
    ARGS.get_arg_flag_value("-timeout")?.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_args_z_flag_alone() {
        // Test: -Z flag with value attached (-Z<value>)
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "-Zbuild-std=panic_abort,core,std".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F"]);
        assert_eq!(cargo_args, vec!["-Zbuild-std=panic_abort,core,std"]);
    }

    #[test]
    fn test_split_args_z_flag_separate() {
        // Test: -Z flag with separate value (-Z <value>)
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "-Z".to_string(),
            "build-std=panic_abort,core,std".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F"]);
        assert_eq!(cargo_args, vec!["-Z", "build-std=panic_abort,core,std"]);
    }

    #[test]
    fn test_split_args_with_double_dash() {
        // Test: Arguments with -- separator
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "--".to_string(),
            "-Zbuild-std=core".to_string(),
            "--release".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F"]);
        assert_eq!(cargo_args, vec!["-Zbuild-std=core", "--release"]);
    }

    #[test]
    fn test_split_args_z_before_and_after_dash() {
        // Test: -Z flag before -- and other args after --
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "-Zbuild-std=core".to_string(),
            "--".to_string(),
            "--release".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F"]);
        assert_eq!(cargo_args, vec!["-Zbuild-std=core", "--release"]);
    }

    #[test]
    fn test_split_args_multiple_z_flags() {
        // Test: Multiple -Z flags
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "-Zbuild-std=core".to_string(),
            "-Zunstable-options".to_string(),
            "-M".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F", "-M"]);
        assert_eq!(
            cargo_args,
            vec!["-Zbuild-std=core", "-Zunstable-options"]
        );
    }

    #[test]
    fn test_split_args_no_z_flags() {
        // Test: No -Z flags, only rapx args
        let args = vec![
            "cargo".to_string(),
            "rapx".to_string(),
            "-F".to_string(),
            "-M".to_string(),
            "-O".to_string(),
        ];
        let [rap_args, cargo_args] = split_args_by_double_dash(&args);
        assert_eq!(rap_args, vec!["-F", "-M", "-O"]);
        assert!(cargo_args.is_empty());
    }
}
