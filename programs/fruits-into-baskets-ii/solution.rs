pub fn num_of_unplaced_fruits(fruits: &[i64], baskets: &[i64]) -> i64 {
    let n = fruits.len();

    let mut used: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        used.push(false);
        k += 1;
    }

    let mut unplaced: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut found: bool = false;
        let mut j: usize = 0;

        while j < n && !found {
            if !used[j] && baskets[j] >= fruits[i] {
                used[j] = true;
                found = true;
            }
            j += 1;
        }

        if !found {
            unplaced += 1;
        }

        i += 1;
    }

    unplaced
}
