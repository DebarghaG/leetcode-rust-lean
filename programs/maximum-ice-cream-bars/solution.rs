pub fn max_ice_cream(costs: &[i64], coins: i64) -> i64 {
    let n = costs.len();
    if n == 0 {
        return 0;
    }

    let mut arr: Vec<i64> = Vec::new();
    let mut max_cost: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c = costs[i];
        arr.push(c);
        if c > max_cost {
            max_cost = c;
        }
        i += 1;
    }

    // LSD radix sort in base 10. This is a counting-sort-based method
    // using only a small fixed-size count array of length 10 per pass.
    let mut exp: i64 = 1;
    while exp <= max_cost {
        let mut counts: Vec<i64> = Vec::new();
        let mut d: usize = 0;
        while d < 10 {
            counts.push(0);
            d += 1;
        }

        i = 0;
        while i < n {
            let digit: i64 = (arr[i] / exp) % 10;
            let idx: usize = digit as usize;
            counts[idx] = counts[idx] + 1;
            i += 1;
        }

        let mut pos: Vec<i64> = Vec::new();
        let mut total: i64 = 0;
        d = 0;
        while d < 10 {
            pos.push(total);
            total = total + counts[d];
            d += 1;
        }

        let mut temp: Vec<i64> = Vec::new();
        i = 0;
        while i < n {
            temp.push(0);
            i += 1;
        }

        i = 0;
        while i < n {
            let digit: i64 = (arr[i] / exp) % 10;
            let idx: usize = digit as usize;
            let p: usize = pos[idx] as usize;
            temp[p] = arr[i];
            pos[idx] = pos[idx] + 1;
            i += 1;
        }

        i = 0;
        while i < n {
            arr[i] = temp[i];
            i += 1;
        }

        exp = exp * 10;
    }

    let mut remaining: i64 = coins;
    let mut bought: i64 = 0;
    i = 0;

    while i < n {
        let c = arr[i];
        if c <= remaining {
            remaining = remaining - c;
            bought = bought + 1;
        } else {
            return bought;
        }
        i += 1;
    }

    bought
}
