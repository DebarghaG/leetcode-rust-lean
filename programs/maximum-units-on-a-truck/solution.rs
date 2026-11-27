pub fn maximum_units(boxTypes: &[Vec<i64>], truckSize: i64) -> i64 {
    let n = boxTypes.len();

    let mut max_unit: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let row = &boxTypes[i];
        let unit = row[1];
        if unit > max_unit {
            max_unit = unit;
        }
        i += 1;
    }

    let bucket_len = (max_unit + 1) as usize;
    let mut buckets: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < bucket_len {
        buckets.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let row = &boxTypes[i];
        let boxes = row[0];
        let unit = row[1];
        let idx = unit as usize;
        buckets[idx] = buckets[idx] + boxes;
        i += 1;
    }

    let mut remaining = truckSize;
    let mut total: i64 = 0;
    let mut u = max_unit;

    while u >= 1 {
        if remaining == 0 {
            break;
        }
        let idx = u as usize;
        let available = buckets[idx];
        let take = if available < remaining {
            available
        } else {
            remaining
        };
        total = total + take * u;
        remaining = remaining - take;
        u -= 1;
    }

    total
}
