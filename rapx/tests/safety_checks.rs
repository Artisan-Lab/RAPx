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
fn test_alias_field() {
    let output = running_tests_with_arg("alias/alias_field", "-alias");
    assert_eq!(
        output.contains("Alias found in Some(\"::foo\"): {(0,1.1),(0,1.0)}")
            || output.contains("Alias found in Some(\"::foo\"): {(0,1.0),(0,1.1)}"),
        true
    );
}

#[test]
fn test_alias_scc() {
    let output = running_tests_with_arg("alias/alias_scc", "-alias");
    assert_eq!(
        output.contains("Alias found in Some(\"::foo\"): {(0,1)}"),
        true
    );
}

#[test]
fn test_alias_switch() {
    let output = running_tests_with_arg("alias/alias_switch", "-alias");
    assert_eq!(
        output.contains("Alias found in Some(\"::foo\"): {(0,1)}"),
        true
    );
}

#[test]
fn test_alias_copy_on_deref() {
    let output = running_tests_with_arg("alias/alias_copy_for_deref", "-alias");
    assert_eq!(
        output.contains("Alias found in Some(\"::{impl#0}::new\"): {(0,1.0)}"),
        true
    );
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

#[inline(always)]
fn heap_result(name: &str, res: &str) -> String {
    let s = String::from(name);
    let color_isolation = if cfg!(target_os = "linux") {
        "\u{1b}[0m \u{1b}[38;5;148m".to_string()
    } else if cfg!(target_os = "macos") {
        " ".to_string()
    } else {
        " ".to_string()
    };
    s + &color_isolation + res
}

#[test]
fn test_heap_cell() {
    let output = running_tests_with_arg("heap/heap_cell", "-heap");
    assert_eq!(
        output.contains(&heap_result("std::cell::Cell<T/#0>", "(0, [1])"))
            && output.contains(&heap_result("std::cell::RefCell<T/#0>", "(0, [1])"))
            && output.contains(&heap_result("std::cell::UnsafeCell<T/#0>", "(0, [1])"))
            && output.contains(&heap_result(
                "std::cell::LazyCell<T/#0, F/#1>",
                "(0, [1,1])"
            ))
            && output.contains(&heap_result("std::rc::Rc<T/#0, A/#1>", "(1, [1,1])"))
            && output.contains(&heap_result("std::sync::Arc<T/#0, A/#1>", "(1, [1,1])"))
            && output.contains(&heap_result("std::rc::UniqueRc<T/#0, A/#1>", "(1, [1,1])"))
            && output.contains(&heap_result("std::rc::Weak<T/#0, A/#1>", "(0, [1,1])"))
            && output.contains(&heap_result("std::sync::Weak<T/#0, A/#1>", "(0, [1,1])")),
        true
    );
}

#[test]
fn test_heap_collections() {
    let output = running_tests_with_arg("heap/heap_collections", "-heap");
    assert_eq!(
        output.contains(&heap_result("std::ptr::Unique<T/#0>", "(1, [0])"))
            && output.contains(&heap_result("std::boxed::Box<T/#0, A/#1>", "(1, [0,1])"))
            && output.contains(&heap_result("std::vec::Vec<T/#0, A/#1>", "(1, [0,1])"))
            && output.contains(&heap_result("std::string::String", "(1, [])"))
            && output.contains(&heap_result(
                "std::collections::VecDeque<T/#0, A/#1>",
                "(1, [0,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::LinkedList<T/#0, A/#1>",
                "(1, [1,1])"
            ))
            && output.contains(&heap_result(
                "hashbrown::raw::RawTable<T/#0, A/#1>",
                "(1, [0,1])"
            ))
            && output.contains(&heap_result(
                "hashbrown::map::HashMap<K/#0, V/#1, S/#2, A/#3>",
                "(1, [0,0,1,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::HashMap<K/#0, V/#1, S/#2>",
                "(1, [0,0,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::BTreeMap<K/#0, V/#1, A/#2>",
                "(1, [0,0,1])"
            ))
            && output.contains(&heap_result(
                "hashbrown::set::HashSet<T/#0, S/#1, A/#2>",
                "(1, [0,1,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::HashSet<T/#0, S/#1>",
                "(1, [0,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::BTreeSet<T/#0, A/#1>",
                "(1, [0,1])"
            ))
            && output.contains(&heap_result(
                "std::collections::BinaryHeap<T/#0, A/#1>",
                "(1, [0,1])"
            )),
        true
    );
}

#[test]
fn test_heap_nested() {
    let output: String = running_tests_with_arg("heap/heap_nested", "-heap");
    assert_eq!(
        output.contains(&heap_result("X<A/#0>", "(0, [1])"))
            && output.contains(&heap_result("Y<B/#0>", "(0, [1])"))
            && output.contains(&heap_result(
                "Example<A/#0, B/#1, T/#2, S/#3>",
                "(1, [1,1,0,1])"
            )),
        true
    );
}

#[test]
fn test_heap_proxy() {
    let output = running_tests_with_arg("heap/heap_proxy", "-heap");
    assert_eq!(
        output.contains(&heap_result("Proxy1<T/#0>", "(0, [0])"))
            && output.contains(&heap_result("Proxy2<T/#0>", "(1, [0])"))
            && output.contains(&heap_result("Proxy3<'a/#0, T/#1>", "(0, [0,0])"))
            && output.contains(&heap_result("Proxy4<T/#0>", "(0, [1])"))
            && output.contains(&heap_result("Proxy5<T/#0>", "(1, [0])")),
        true
    );
}

#[test]
fn test_audit_case1() {
    let output = running_tests_with_arg("others/support/safety_check/audit_case1", "-I");
    assert_eq!(output.contains("Lack safety annotations"), true);
}

#[test]
fn test_verify() {
    let output = running_tests_with_arg(
        "others/support/safety_check/slice_from_raw_parts",
        "-verify",
    );
    assert_eq!(output.contains("unaligned"), true);
}
