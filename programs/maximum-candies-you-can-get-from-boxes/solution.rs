pub fn max_candies(
    status: &[i64],
    candies: &[i64],
    keys: &[Vec<i64>],
    containedBoxes: &[Vec<i64>],
    initialBoxes: &[i64],
) -> i64 {
    let n = status.len();

    let mut have: Vec<bool> = Vec::new();
    let mut used: Vec<bool> = Vec::new();
    let mut can_open: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        have.push(false);
        used.push(false);
        can_open.push(status[i] == 1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    i = 0;
    while i < initialBoxes.len() {
        let b = initialBoxes[i] as usize;
        have[b] = true;
        if can_open[b] && !used[b] {
            used[b] = true;
            queue.push(b as i64);
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut head: usize = 0;

    while head < queue.len() {
        let b = queue[head] as usize;
        head += 1;

        ans += candies[b];

        let mut j: usize = 0;
        while j < keys[b].len() {
            let k = keys[b][j] as usize;
            can_open[k] = true;
            if have[k] && !used[k] {
                used[k] = true;
                queue.push(k as i64);
            }
            j += 1;
        }

        j = 0;
        while j < containedBoxes[b].len() {
            let c = containedBoxes[b][j] as usize;
            have[c] = true;
            if can_open[c] && !used[c] {
                used[c] = true;
                queue.push(c as i64);
            }
            j += 1;
        }
    }

    ans
}
