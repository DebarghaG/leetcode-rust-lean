pub fn full_bloom_flowers(flowers: &[Vec<i64>], people: &[i64]) -> Vec<i64> {
    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < flowers.len() {
        let row = &flowers[i];
        starts.push(row[0]);
        ends.push(row[1]);
        i += 1;
    }

    starts.sort();
    ends.sort();

    let mut answer: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < people.len() {
        let p = people[j];
        let started = count_leq(&starts, p);
        let ended_before = count_lt(&ends, p);
        answer.push(started - ended_before);
        j += 1;
    }

    answer
}

fn count_leq(xs: &[i64], x: i64) -> i64 {
    let mut lo = 0usize;
    let mut hi = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] <= x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo as i64
}

fn count_lt(xs: &[i64], x: i64) -> i64 {
    let mut lo = 0usize;
    let mut hi = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo as i64
}
