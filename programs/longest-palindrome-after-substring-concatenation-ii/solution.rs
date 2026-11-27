fn reverse_bytes(x: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = x.len();
    while i > 0 {
        i -= 1;
        out.push(x[i]);
    }
    out
}

fn palindrome_start(a: &[u8]) -> Vec<usize> {
    let n = a.len();
    let mut res: Vec<usize> = Vec::new();
    let mut i = 0;
    while i <= n {
        res.push(0);
        i += 1;
    }

    let mut c = 0;
    while c < n {
        let mut l = c;
        let mut r = c;
        let mut active = true;
        while active {
            let len = r - l + 1;
            if len > res[l] {
                res[l] = len;
            }
            if l == 0 || r + 1 >= n {
                active = false;
            } else {
                l -= 1;
                r += 1;
                if a[l] != a[r] {
                    active = false;
                }
            }
        }
        c += 1;
    }

    let mut c2 = 1;
    while c2 < n {
        let mut l = c2 - 1;
        let mut r = c2;
        let mut active = a[l] == a[r];
        while active {
            let len = r - l + 1;
            if len > res[l] {
                res[l] = len;
            }
            if l == 0 || r + 1 >= n {
                active = false;
            } else {
                l -= 1;
                r += 1;
                if a[l] != a[r] {
                    active = false;
                }
            }
        }
        c2 += 1;
    }

    res
}

fn palindrome_end(a: &[u8]) -> Vec<usize> {
    let n = a.len();
    let mut res: Vec<usize> = Vec::new();
    let mut i = 0;
    while i <= n {
        res.push(0);
        i += 1;
    }

    let mut c = 0;
    while c < n {
        let mut l = c;
        let mut r = c;
        let mut active = true;
        while active {
            let len = r - l + 1;
            let idx = r + 1;
            if len > res[idx] {
                res[idx] = len;
            }
            if l == 0 || r + 1 >= n {
                active = false;
            } else {
                l -= 1;
                r += 1;
                if a[l] != a[r] {
                    active = false;
                }
            }
        }
        c += 1;
    }

    let mut c2 = 1;
    while c2 < n {
        let mut l = c2 - 1;
        let mut r = c2;
        let mut active = a[l] == a[r];
        while active {
            let len = r - l + 1;
            let idx = r + 1;
            if len > res[idx] {
                res[idx] = len;
            }
            if l == 0 || r + 1 >= n {
                active = false;
            } else {
                l -= 1;
                r += 1;
                if a[l] != a[r] {
                    active = false;
                }
            }
        }
        c2 += 1;
    }

    res
}

fn longest_prefix_matches(a: &[u8], b: &[u8]) -> Vec<usize> {
    let n = a.len();
    let m = b.len();
    let mut res: Vec<usize> = Vec::new();
    let mut i0 = 0;
    while i0 < n {
        res.push(0);
        i0 += 1;
    }

    if n == 0 || m == 0 {
        return res;
    }

    let mut next: Vec<usize> = Vec::new();
    let mut j0 = 0;
    while j0 <= m {
        next.push(0);
        j0 += 1;
    }

    let mut cur: Vec<usize> = Vec::new();
    j0 = 0;
    while j0 <= m {
        cur.push(0);
        j0 += 1;
    }

    let mut ii = n;
    while ii > 0 {
        ii -= 1;

        let mut best: usize = 0;
        let mut jj = m;
        while jj > 0 {
            jj -= 1;

            if a[ii] == b[jj] {
                let val = next[jj + 1] + 1;
                cur[jj] = val;
                if val > best {
                    best = val;
                }
            } else {
                cur[jj] = 0;
            }
        }

        cur[m] = 0;
        res[ii] = best;

        let mut k = 0;
        while k <= m {
            next[k] = cur[k];
            k += 1;
        }
    }

    res
}

pub fn longest_palindrome(s: &[u8], t: &[u8]) -> i64 {
    let n = s.len();
    let m = t.len();

    let rev_t = reverse_bytes(t);
    let start_s = palindrome_start(s);
    let k_s = longest_prefix_matches(s, &rev_t);

    let mut ans: usize = 0;

    let mut p = 0;
    while p < n {
        let max_q = p + k_s[p];
        let mut q = p;
        while q <= max_q {
            let cand = 2 * (q - p) + start_s[q];
            if cand > ans {
                ans = cand;
            }
            q += 1;
        }
        p += 1;
    }

    let rev_s = reverse_bytes(s);
    let end_t = palindrome_end(t);
    let k_t = longest_prefix_matches(t, &rev_s);

    let mut q2 = 0;
    while q2 <= m {
        let mut dlen = 0;
        if q2 < m {
            dlen = k_t[q2];
        }

        let cand = end_t[q2] + 2 * dlen;
        if cand > ans {
            ans = cand;
        }

        q2 += 1;
    }

    let mut out: i64 = 0;
    let mut z: usize = 0;
    while z < ans {
        out += 1;
        z += 1;
    }

    out
}
