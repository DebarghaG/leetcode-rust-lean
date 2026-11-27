pub fn maximum_bags(capacity: &[i64], rocks: &[i64], additionalRocks: i64) -> i64 {
    let n = capacity.len();
    let mut deficits: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        deficits.push(capacity[i] - rocks[i]);
        i += 1;
    }

    deficits.sort();

    let mut ans: i64 = 0;
    let mut remaining: i64 = additionalRocks;
    let mut j: usize = 0;

    while j < n {
        let need = deficits[j];
        if need <= remaining {
            remaining -= need;
            ans += 1;
            j += 1;
        } else {
            j = n;
        }
    }

    ans
}
