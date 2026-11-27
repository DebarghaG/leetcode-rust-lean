const MOD: i64 = 1000000007;

fn letter_index(b: u8) -> usize {
    if b == b'a' { return 0; }
    if b == b'b' { return 1; }
    if b == b'c' { return 2; }
    if b == b'd' { return 3; }
    if b == b'e' { return 4; }
    if b == b'f' { return 5; }
    if b == b'g' { return 6; }
    if b == b'h' { return 7; }
    if b == b'i' { return 8; }
    if b == b'j' { return 9; }
    if b == b'k' { return 10; }
    if b == b'l' { return 11; }
    if b == b'm' { return 12; }
    if b == b'n' { return 13; }
    if b == b'o' { return 14; }
    if b == b'p' { return 15; }
    if b == b'q' { return 16; }
    if b == b'r' { return 17; }
    if b == b's' { return 18; }
    if b == b't' { return 19; }
    if b == b'u' { return 20; }
    if b == b'v' { return 21; }
    if b == b'w' { return 22; }
    if b == b'x' { return 23; }
    if b == b'y' { return 24; }
    25
}

fn count_letter(s: &[u8], target: usize) -> i64 {
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < s.len() {
        let idx: usize = letter_index(s[i]);
        if idx == target {
            count += 1;
        }
        i += 1;
    }
    count
}

fn build_base(nums: &[i64], n: usize) -> Vec<Vec<i64>> {
    let mut base: Vec<Vec<i64>> = Vec::new();
    let mut r: usize = 0;
    while r < n {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < n {
            let mut lim: i64 = 0;
            if c < nums.len() {
                lim = nums[c];
            }

            // Count how many of the consecutive letters after c (wrapping)
            // equal r.  The first letter produced is (c + 1) mod 26.
            let mut val: i64 = 0;
            let mut rpos: usize = c;
            let mut k: i64 = 1;
            while k <= lim {
                rpos += 1;
                if rpos == n {
                    rpos = 0;
                }
                if rpos == r {
                    val += 1;
                }
                k += 1;
            }

            row.push(val % MOD);
            c += 1;
        }
        base.push(row);
        r += 1;
    }
    base
}

fn identity(n: usize) -> Vec<Vec<i64>> {
    let mut m: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            if i == j {
                row.push(1);
            } else {
                row.push(0);
            }
            j += 1;
        }
        m.push(row);
        i += 1;
    }
    m
}

fn mat_mul(a: &[Vec<i64>], b: &[Vec<i64>], n: usize) -> Vec<Vec<i64>> {
    let mut result: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut sum: i64 = 0;
            let mut k: usize = 0;
            while k < n {
                sum = (sum + a[i][k] * b[k][j]) % MOD;
                k += 1;
            }
            row.push(sum);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}

fn mat_vec_mul(a: &[Vec<i64>], v: &[i64], n: usize) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut sum: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            sum = (sum + a[i][j] * v[j]) % MOD;
            j += 1;
        }
        out.push(sum);
        i += 1;
    }
    out
}

pub fn length_after_transformations(s: &[u8], t: i64, nums: &[i64]) -> i64 {
    let n: usize = 26;

    let mut base: Vec<Vec<i64>> = build_base(nums, n);
    let mut power: Vec<Vec<i64>> = identity(n);

    let mut exp: i64 = t;
    while exp > 0 {
        if exp % 2 == 1 {
            let new_power: Vec<Vec<i64>> = mat_mul(&power, &base, n);
            power = new_power;
        }
        exp = exp / 2;
        let new_base: Vec<Vec<i64>> = mat_mul(&base, &base, n);
        base = new_base;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < n {
        counts.push(count_letter(s, c) % MOD);
        c += 1;
    }

    let final_counts: Vec<i64> = mat_vec_mul(&power, &counts, n);

    let mut ans: i64 = 0;
    let mut r: usize = 0;
    while r < n {
        ans = (ans + final_counts[r]) % MOD;
        r += 1;
    }

    ans
}
