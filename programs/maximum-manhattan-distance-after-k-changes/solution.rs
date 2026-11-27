pub fn max_distance(s: &[u8], k: i64) -> i64 {
    let n: usize = s.len();
    let mut x: i64 = 0;
    let mut y: i64 = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;
    let mut steps: i64 = 0;

    while i < n {
        let c: u8 = s[i];

        if c == b'N' {
            y += 1;
        } else if c == b'S' {
            y -= 1;
        } else if c == b'E' {
            x += 1;
        } else if c == b'W' {
            x -= 1;
        }

        let ax: i64 = if x < 0 { -x } else { x };
        let ay: i64 = if y < 0 { -y } else { y };

        steps += 1;

        let mut candidate: i64 = ax + ay + 2 * k;
        if candidate > steps {
            candidate = steps;
        }

        if candidate > ans {
            ans = candidate;
        }

        i += 1;
    }

    ans
}
