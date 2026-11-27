pub fn num_rescue_boats(people: &[i64], limit: i64) -> i64 {
    let lim = limit as usize;

    let mut counts: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= lim {
        counts.push(0);
        i += 1;
    }

    let mut p = 0usize;
    while p < people.len() {
        let w = people[p] as usize;
        counts[w] += 1;
        p += 1;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut w = 1usize;
    while w <= lim {
        let mut c = counts[w];
        while c > 0 {
            sorted.push(w as i64);
            c -= 1;
        }
        w += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = sorted.len();
    let mut boats: i64 = 0;

    while left < right {
        let hi = right - 1;
        if left < hi && sorted[left] + sorted[hi] <= limit {
            left += 1;
        }
        right = hi;
        boats += 1;
    }

    boats
}
