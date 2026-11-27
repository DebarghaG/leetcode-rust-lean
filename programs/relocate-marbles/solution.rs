pub fn relocate_marbles(nums: &[i64], moveFrom: &[i64], moveTo: &[i64]) -> Vec<i64> {
    let mut coords: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < nums.len() {
        coords.push(nums[i]);
        i += 1;
    }

    i = 0;
    while i < moveTo.len() {
        coords.push(moveTo[i]);
        i += 1;
    }

    i = 0;
    while i < moveFrom.len() {
        coords.push(moveFrom[i]);
        i += 1;
    }

    coords.sort();

    let mut uniq: Vec<i64> = Vec::new();
    i = 0;
    while i < coords.len() {
        if i == 0 || coords[i] != coords[i - 1] {
            uniq.push(coords[i]);
        }
        i += 1;
    }

    let n = uniq.len();
    let mut occupied: Vec<bool> = Vec::new();
    i = 0;
    while i < n {
        occupied.push(false);
        i += 1;
    }

    i = 0;
    while i < nums.len() {
        let idx = lower_bound(&uniq, nums[i]);
        occupied[idx] = true;
        i += 1;
    }

    i = 0;
    while i < moveFrom.len() {
        let from = moveFrom[i];
        let to = moveTo[i];

        if from != to {
            let from_idx = lower_bound(&uniq, from);
            let to_idx = lower_bound(&uniq, to);

            occupied[from_idx] = false;
            occupied[to_idx] = true;
        }

        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if occupied[i] {
            result.push(uniq[i]);
        }
        i += 1;
    }

    result
}

fn lower_bound(xs: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;

        if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}
