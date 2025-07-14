use std::path::Path;
use std::process::Command;

#[inline(always)]
fn running_tests_with_arg(dir: &str, arg: &str) -> String {
    let raw_path = "./tests/".to_owned() + dir;
    let project_path = Path::new(&raw_path);

    let output = Command::new("cargo")
        .arg("rapx")
        .arg(arg)
        .current_dir(project_path)
        .output()
        .expect("Failed to execute cargo rapx");

    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn test_dangling_min() {
    let output = running_tests_with_arg("uaf/dangling_min", "-F");
    assert_eq!(
        output.contains("Dangling pointer detected in function \"create_vec\""),
        true
    );
}

#[test]
fn test_df_min() {
    let output = running_tests_with_arg("uaf/df_min", "-F");
    assert_eq!(
        output.contains("Double free detected in function main"),
        true
    );
}

#[test]
fn test_dp_lengthy() {
    let output = running_tests_with_arg("uaf/dp_lengthy", "-F");
    assert_eq!(
        output.contains("Dangling pointer detected in function \"call\""),
        true
    );
}

#[test]
fn test_uaf_drop() {
    let output = running_tests_with_arg("uaf/uaf_drop", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_drop2() {
    let output = running_tests_with_arg("uaf/uaf_drop2", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_drop_in_place() {
    let output = running_tests_with_arg("uaf/uaf_drop_in_place", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_lifetime() {
    let output = running_tests_with_arg("uaf/uaf_lifetime", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_small() {
    let output = running_tests_with_arg("uaf/uaf_small", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"main\""),
        true
    );
}

#[test]
fn test_uaf_swithint() {
    let output = running_tests_with_arg("uaf/uaf_swithint", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"evil_test\""),
        true
    );
}

#[test]
fn test_uaf_swithint_diffbranch() {
    let output = running_tests_with_arg("uaf/uaf_swithint_diffbranch", "-F");
    assert_eq!(
        output.contains("Use after free detected in function \"evil_test\""),
        false
    );
}

#[test]
fn test_alias_not_alias_iter() {
    let output = running_tests_with_arg("alias/not_alias_iter", "-alias");
    assert_eq!(output.contains("foo\": null"), true);
}

#[test]
fn test_alias_field() {
    let output = running_tests_with_arg("alias/alias_field", "-alias");
    assert_eq!(
        output.contains("\"foo\": (0,1.1), (0,1.0)")
            || output.contains("\"foo\": (0,1.0), (0,1.1)"),
        true
    );
}

#[test]
fn test_alias_lib_no_caller() {
    let output = running_tests_with_arg("alias/alias_lib_no_caller", "-alias");
    assert_eq!(output.contains("new\": (0,1.0)"), true);
}

#[test]
fn test_alias_scc() {
    let output = running_tests_with_arg("alias/alias_scc", "-alias");
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_switch() {
    let output = running_tests_with_arg("alias/alias_switch", "-alias");
    assert_eq!(output.contains("foo\": (0,1)"), true);
}

#[test]
fn test_alias_copy_on_deref() {
    let output = running_tests_with_arg("alias/alias_copy_for_deref", "-alias");
    assert_eq!(output.contains("new\": (0,1.0)"), true);
}

#[test]
fn test_alias_indirect() {
    let output = running_tests_with_arg("alias/alias_indirect", "-alias");
    assert_eq!(output.contains("iter_prop\": (0,1.0)"), true);
}

#[test]
fn test_leak_ctor() {
    let output = running_tests_with_arg("leak/leak_ctor", "-M");
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        false
    );
}

#[test]
fn test_leak_orphan() {
    let output = running_tests_with_arg("leak/leak_orphan", "-M");
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        true
    );
}

#[test]
fn test_leak_proxy() {
    let output = running_tests_with_arg("leak/leak_proxy", "-M");
    assert_eq!(
        output.contains("Memory Leak detected in function main"),
        true
    );
}

#[test]
fn test_heap_cell() {
    let output = running_tests_with_arg("ownedheap/heap_cell", "-ownedheap");
    assert_eq!(
        output.contains("Cell\": False, <1>")
            && output.contains("RefCell\": False, <1>")
            && output.contains("UnsafeCell\": False, <1>")
            && output.contains("Rc\": True, <1,1>")
            && output.contains("Arc\": True, <1,1>")
            && output.contains("UniqueRc\": True, <1,1>"),
        true
    );
}

#[test]
fn test_heap_collections() {
    let output = running_tests_with_arg("ownedheap/heap_collections", "-ownedheap");
    assert_eq!(
        output.contains("Unique\": True, <0>")
            && output.contains("Box\": True, <0,1>")
            && output.contains("Vec\": True, <0,1>")
            && output.contains("String\": True, <>")
            && output.contains("LinkedList\": True, <1,1>")
            && output.contains("HashMap\": True, <0,0,1>")
            && output.contains("BTreeMap\": True, <0,0,1>")
            && output.contains("HashSet\": True, <0,1>")
            && output.contains("BTreeSet\": True, <0,1>"),
        true
    );
}

#[test]
fn test_heap_nested() {
    let output: String = running_tests_with_arg("ownedheap/heap_nested", "-ownedheap");
    assert_eq!(
        output.contains("X\": False, <1>")
            && output.contains("Y\": False, <1>")
            && output.contains("Example\": True, <1,1,0,1>"),
        true
    );
}

#[test]
fn test_heap_proxy() {
    let output = running_tests_with_arg("ownedheap/heap_proxy", "-ownedheap");
    assert_eq!(
        output.contains("Proxy1\": False, <0>")
            && output.contains("Proxy2\": True, <0>")
            && output.contains("Proxy3\": False, <0,0>")
            && output.contains("Proxy4\": False, <1>")
            && output.contains("Proxy5\": True, <0>"),
        true
    );
}

#[test]
fn test_test_cons_merge() {
    let output = running_tests_with_arg("safety_check/test_cons_merge", "-verify");
    assert_eq!(output.contains("NonNull"), true);
}

#[test]
fn test_aligned() {
    let output = running_tests_with_arg("safety_check/align", "-verify");
    assert_eq!(output.contains("Aligned"), true);
}

#[test]
fn test_init() {
    let output = running_tests_with_arg("safety_check/init", "-verify");
    assert_eq!(output.contains("Init"), true);
}

#[test]
fn test_cis() {
    let output = running_tests_with_arg("safety_check/verify_case1", "-verify");
    assert_eq!(output.contains("ValidPtr"), true);
}

#[test]
fn test_ssa_transform() {
    let output = running_tests_with_arg("ssa/ssa_transform", "-ssa");
    assert_eq!(output.contains("ssa lvalue check true"), true);
}
#[test]
fn test_range_analysis() {
    let output = running_tests_with_arg("range/range_1", "-range");

    let expected_ranges = vec![
        "_1 => Regular [0, 0]",
        " _2 => Regular [Min, Max]",
        "_4 => Regular [0, 100]",
        "_6 => Regular [0, 99]",
        "_11 => Regular [1, 99]",
        "_12 => Regular [0, 98]",
        "_34 => Regular [1, 100]",
    ];

    for expected in expected_ranges {
        assert!(
            output.contains(expected),
            "Missing expected range: '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}
#[test]

fn test_interprocedual_range_analysis() {
    let output = running_tests_with_arg("range/range_2", "-range");

    let expected_ranges = vec![
        "_1 => Regular [42, 42]",
        "_2 => Regular [Min, Max]",
        "_4 => Regular [52, 52]",
        "_5 => Regular [100, 100]",
    ];

    for expected in expected_ranges {
        assert!(
            output.contains(expected),
            "Missing expected range: '{}'\nFull output:\n{}",
            expected,
            output
        );
    }
}
