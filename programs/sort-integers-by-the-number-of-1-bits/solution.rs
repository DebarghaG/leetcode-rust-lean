pub fn sort_by_bits(arr: &[i64]) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len() {
        v.push(arr[i]);
        i += 1;
    }

    let n = v.len();
    let mut i: usize = 1;
    while i < n {
        let key = v[i];
        let mut j = i;
        while j > 0 && comes_before(key, v[j - 1]) {
            v[j] = v[j - 1];
            j -= 1;
        }
        v[j] = key;
        i += 1;
    }

    v
}

fn comes_before(a: i64, b: i64) -> bool {
    let ba = popcount(a);
    let bb = popcount(b);
    if ba < bb {
        true
    } else if ba > bb {
        false
    } else {
        a < b
    }
}

fn popcount(mut x: i64) -> i64 {
    let mut count: i64 = 0;
    while x > 0 {
        count += x % 2;
        x = x / 2;
    }
    count
}
