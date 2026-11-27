pub fn number_of_weak_characters(properties: &[Vec<i64>]) -> i64 {
    let n: usize = properties.len();

    let mut max_attack: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if properties[i][0] > max_attack {
            max_attack = properties[i][0];
        }
        i += 1;
    }

    let mut buckets: Vec<Vec<i64>> = Vec::new();
    let mut a: i64 = 0;
    while a <= max_attack {
        buckets.push(Vec::new());
        a += 1;
    }

    i = 0;
    while i < n {
        let attack: i64 = properties[i][0];
        let defense: i64 = properties[i][1];
        let idx: usize = attack as usize;
        buckets[idx].push(defense);
        i += 1;
    }

    let mut weak: i64 = 0;
    let mut max_def: i64 = -1;

    let mut atk: usize = buckets.len();
    while atk > 0 {
        atk -= 1;
        let bucket = &buckets[atk];

        let mut group_max: i64 = -1;
        let mut j: usize = 0;
        while j < bucket.len() {
            let defense: i64 = bucket[j];
            if defense < max_def {
                weak += 1;
            }
            if defense > group_max {
                group_max = defense;
            }
            j += 1;
        }

        if group_max > max_def {
            max_def = group_max;
        }
    }

    weak
}
