pub fn number_of_substrings(s: &[u8]) -> i64 {
    let n_usize: usize = s.len();
    let n: i64 = n_usize as i64;

    let mut zeros: Vec<i64> = Vec::new();
    let mut i_usize: usize = 0;
    while i_usize < n_usize {
        if s[i_usize] == b'0' {
            zeros.push(i_usize as i64);
        }
        i_usize += 1;
    }
    let m: usize = zeros.len();

    // Count all substrings containing no zero.
    let mut ans: i64 = 0;
    let mut run: i64 = 0;
    i_usize = 0;
    while i_usize < n_usize {
        if s[i_usize] == b'1' {
            run += 1;
        } else {
            ans += run * (run + 1) / 2;
            run = 0;
        }
        i_usize += 1;
    }
    ans += run * (run + 1) / 2;

    // If a substring has z zeros, it can be dominant only when z*z + z <= n.
    let mut max_z: i64 = 0;
    let mut z: i64 = 1;
    while z * z + z <= n {
        max_z = z;
        z += 1;
    }

    z = 1;
    while z <= max_z {
        let zu: usize = z as usize;
        if zu <= m {
            let zz: i64 = z * z;
            let mut idx: usize = 0;

            while idx + zu <= m {
                let first: i64 = zeros[idx];
                let last: i64 = zeros[idx + zu - 1];
                let prev: i64 = if idx == 0 { -1 } else { zeros[idx - 1] };

                let next_idx: usize = idx + zu;
                let next: i64 = if next_idx < m { zeros[next_idx] } else { n };

                let a: i64 = first - prev - 1;
                let b: i64 = next - last - 1;
                let inside_ones: i64 = (last - first + 1) - z;
                let need: i64 = zz - inside_ones;

                if need <= 0 {
                    ans += (a + 1) * (b + 1);
                } else {
                    let mut x: i64 = 0;
                    while x <= a {
                        let req_y: i64 = need - x;
                        if req_y <= 0 {
                            ans += b + 1;
                        } else if req_y <= b {
                            ans += b - req_y + 1;
                        }
                        x += 1;
                    }
                }

                idx += 1;
            }
        }
        z += 1;
    }

    ans
}
