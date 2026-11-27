pub fn find_array(pref: &[i64]) -> Vec<i64> {
    let n = pref.len();
    let mut arr: Vec<i64> = Vec::new();

    if n == 0 {
        return arr;
    }

    arr.push(pref[0]);

    let mut i: usize = 1;
    while i < n {
        arr.push(pref[i - 1] ^ pref[i]);
        i += 1;
    }

    arr
}
