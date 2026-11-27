pub fn max_points_inside_square(points: &[Vec<i64>], s: &[u8]) -> i64 {
    let n = points.len();
    let inf: i64 = 2_000_000_000;

    let mut first: Vec<i64> = Vec::new();
    let mut second: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < 26 {
        first.push(inf);
        second.push(inf);
        k += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let x = points[i][0];
        let y = points[i][1];

        let ax = if x < 0 { -x } else { x };
        let ay = if y < 0 { -y } else { y };
        let d = if ax > ay { ax } else { ay };

        let c: usize = (s[i] - b'a') as usize;

        if d < first[c] {
            second[c] = first[c];
            first[c] = d;
        } else {
            if d < second[c] {
                second[c] = d;
            }
        }

        i += 1;
    }

    let mut bound = inf;
    let mut cidx: usize = 0;
    while cidx < 26 {
        if second[cidx] < bound {
            bound = second[cidx];
        }
        cidx += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        let x = points[i][0];
        let y = points[i][1];

        let ax = if x < 0 { -x } else { x };
        let ay = if y < 0 { -y } else { y };
        let d = if ax > ay { ax } else { ay };

        if d < bound {
            ans += 1;
        }

        i += 1;
    }

    ans
}
