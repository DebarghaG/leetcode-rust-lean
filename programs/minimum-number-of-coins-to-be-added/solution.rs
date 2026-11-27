pub fn minimum_added_coins(coins: &[i64], target: i64) -> i64 {
    let n: usize = (target as usize) + 1;
    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        freq.push(0);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < coins.len() {
        let c: i64 = coins[j];
        if c > 0 {
            if c <= target {
                let idx: usize = c as usize;
                freq[idx] = freq[idx] + 1;
            }
        }
        j = j + 1;
    }

    let mut covered: i64 = 0;
    let mut added: i64 = 0;
    let mut value: i64 = 1;

    while value <= target && covered < target {
        let idx: usize = value as usize;

        while freq[idx] > 0 && covered < target {
            if value <= covered + 1 {
                covered = covered + value;
                freq[idx] = freq[idx] - 1;
            } else {
                added = added + 1;
                covered = covered + covered + 1;
            }
        }

        value = value + 1;
    }

    while covered < target {
        added = added + 1;
        covered = covered + covered + 1;
    }

    added
}
