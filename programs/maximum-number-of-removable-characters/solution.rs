pub fn maximum_removals(s: &[u8], p: &[u8], removable: &[i64]) -> i64 {
    let mut lo: usize = 0;
    let mut hi: usize = removable.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo + 1) / 2;
        if can_remove(s, p, removable, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo as i64
}

fn can_remove(s: &[u8], p: &[u8], removable: &[i64], k: usize) -> bool {
    let mut removed: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < s.len() {
        removed.push(false);
        i += 1;
    }

    i = 0;
    while i < k {
        let idx: usize = removable[i] as usize;
        removed[idx] = true;
        i += 1;
    }

    let mut si: usize = 0;
    let mut pi: usize = 0;

    while si < s.len() && pi < p.len() {
        if !removed[si] && s[si] == p[pi] {
            pi += 1;
        }
        si += 1;
    }

    pi == p.len()
}
