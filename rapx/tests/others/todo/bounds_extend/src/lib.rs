fn foo(buf1: &mut Vec<u8>, buf2: &[u8]) {
    buf1.extend_from_slice(&buf2);
}
