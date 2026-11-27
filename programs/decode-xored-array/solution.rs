pub fn decode(encoded: &[i64], first: i64) -> Vec<i64> {
    let n = encoded.len();
    let mut arr: Vec<i64> = Vec::new();
    arr.push(first);
    let mut i: usize = 0;
    while i < n {
        let prev = arr[i];
        arr.push(prev ^ encoded[i]);
        i += 1;
    }
    arr
}
