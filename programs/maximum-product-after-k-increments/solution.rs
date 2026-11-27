const MOD: i64 = 1000000007;

fn pow_mod(mut base: i64, mut exp: i64) -> i64 {
    base = base % MOD;
    let mut result: i64 = 1;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % MOD;
        }
        base = (base * base) % MOD;
        exp = exp / 2;
    }
    result
}

pub fn maximum_product(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(nums[idx]);
        idx += 1;
    }
    a.sort();

    let mut remaining = k;
    let mut i: usize = 0;

    while i + 1 < n {
        let gap = a[i + 1] - a[i];
        let count = (i + 1) as i64;
        let cost = gap * count;

        if remaining >= cost {
            remaining -= cost;
            i += 1;
        } else {
            break;
        }
    }

    let low_count: i64 = (i + 1) as i64;
    let extra = remaining / low_count;
    let rem = remaining % low_count;

    let base_value = a[i] + extra;
    let base_mod = base_value % MOD;

    let mut ans: i64 = 1;

    let count_base = low_count - rem;
    ans = (ans * pow_mod(base_mod, count_base)) % MOD;
    ans = (ans * pow_mod((base_value + 1) % MOD, rem)) % MOD;

    let mut j = i + 1;
    while j < n {
        ans = (ans * (a[j] % MOD)) % MOD;
        j += 1;
    }

    ans
}
