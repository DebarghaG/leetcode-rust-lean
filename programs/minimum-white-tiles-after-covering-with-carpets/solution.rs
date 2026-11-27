pub fn minimum_white_tiles(floor: &[u8], numCarpets: i64, carpetLen: i64) -> i64 {
    let n: usize = floor.len();
    let mut k: usize = numCarpets as usize;
    if k > n {
        k = n;
    }
    let l: usize = carpetLen as usize;

    let width: usize = k + 1;
    let total: usize = (n + 1) * width;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < total {
        dp.push(0);
        idx += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        let white: i64 = if floor[i - 1] == b'1' { 1 } else { 0 };

        // Using zero carpets on the first i tiles.
        dp[i * width] = dp[(i - 1) * width] + white;

        let mut j: usize = 1;
        while j <= k {
            // Do not cover the i-th tile with a new carpet.
            let mut best: i64 = dp[(i - 1) * width + j] + white;

            // Use one carpet to cover the last l tiles, if possible.
            if i >= l {
                let candidate: i64 = dp[(i - l) * width + (j - 1)];
                if candidate < best {
                    best = candidate;
                }
            } else {
                // One carpet can cover the entire current prefix.
                best = 0;
            }

            dp[i * width + j] = best;
            j += 1;
        }

        i += 1;
    }

    dp[n * width + k]
}
