fn is_pal(s: &[u8], mask: usize) -> bool {
    let n = s.len();
    let mut left: usize = 0;
    let mut right: usize = n;

    while left < right {
        while left < n && ((mask >> left) & 1usize) == 0usize {
            left += 1;
        }
        while right > 0 && ((mask >> (right - 1)) & 1usize) == 0usize {
            right -= 1;
        }

        if left + 1 >= right {
            return true;
        }

        if s[left] != s[right - 1] {
            return false;
        }

        left += 1;
        right -= 1;
    }

    true
}

pub fn max_product(s: &[u8]) -> i64 {
    let n = s.len();
    let total: usize = 1usize << n;

    let mut pal: Vec<bool> = Vec::new();
    let mut lens: Vec<i64> = Vec::new();

    let mut mask: usize = 0;
    while mask < total {
        let mut cnt: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            if ((mask >> i) & 1usize) == 1usize {
                cnt += 1;
            }
            i += 1;
        }

        lens.push(cnt);
        pal.push(is_pal(s, mask));

        mask += 1;
    }

    let mut best: i64 = 0;
    let mut a: usize = 0;

    while a < total {
        if pal[a] {
            let comp: usize = (total - 1usize) ^ a;
            let mut b: usize = comp;

            loop {
                if pal[b] {
                    let prod: i64 = lens[a] * lens[b];
                    if prod > best {
                        best = prod;
                    }
                }

                if b == 0 {
                    break;
                }

                b = (b - 1usize) & comp;
            }
        }

        a += 1;
    }

    best
}
