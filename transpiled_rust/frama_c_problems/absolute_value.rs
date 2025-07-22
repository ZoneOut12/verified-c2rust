fn abs(val: i32) -> i32 {
    if val < 0 {
        -val
    } else {
        val
    }
}

fn foo(a: i32) {
    let b: i32 = abs(-42);
    let c: i32 = abs(42);
    let d: i32 = abs(a);
}