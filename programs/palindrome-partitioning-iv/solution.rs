pub fn check_partitioning(s: &[u8]) -> bool {
    let n = s.len();

    let total = n * n;
    let mut is_pal: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        is_pal.push(false);
        k += 1;
    }

    let mut length: usize = 1;
    while length <= n {
        let mut i: usize = 0;
        while i + length <= n {
            let j = i + length - 1;
            if s[i] == s[j] {
                if length <= 2 {
                    is_pal[i * n + j] = true;
                } else if is_pal[(i + 1) * n + (j - 1)] {
                    is_pal[i * n + j] = true;
                }
            }
            i += 1;
        }
        length += 1;
    }

    let mut found = false;
    let mut i: usize = 0;
    while i + 2 < n && !found {
        if is_pal[i] {
            let mut j: usize = i + 1;
            while j + 1 < n && !found {
                if is_pal[(i + 1) * n + j] && is_pal[(j + 1) * n + (n - 1)] {
                    found = true;
                }
                j += 1;
            }
        }
        i += 1;
    }

    found
}
