fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    if a < 0 {
        -a
    } else {
        a
    }
}

pub fn interchangeable_rectangles(rectangles: &[Vec<i64>]) -> i64 {
    let n = rectangles.len();
    if n <= 1 {
        return 0;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let w = rectangles[i][0];
        let h = rectangles[i][1];
        let g = gcd(w, h);
        let rw = w / g;
        let rh = h / g;
        let key = rw * 100001 + rh;
        keys.push(key);
        i += 1;
    }

    keys.sort();

    let mut ans: i64 = 0;
    let mut start: usize = 0;
    while start < n {
        let mut end = start + 1;
        while end < n && keys[end] == keys[start] {
            end += 1;
        }
        let count = (end - start) as i64;
        ans += count * (count - 1) / 2;
        start = end;
    }

    ans
}
