pub fn merge_triplets(triplets: &[Vec<i64>], target: &[i64]) -> bool {
    let mut best0: i64 = 0;
    let mut best1: i64 = 0;
    let mut best2: i64 = 0;

    let n = triplets.len();
    let mut i = 0;
    while i < n {
        let row = &triplets[i];
        let a = row[0];
        let b = row[1];
        let c = row[2];

        if a <= target[0] && b <= target[1] && c <= target[2] {
            if a > best0 {
                best0 = a;
            }
            if b > best1 {
                best1 = b;
            }
            if c > best2 {
                best2 = c;
            }
        }

        i += 1;
    }

    best0 == target[0] && best1 == target[1] && best2 == target[2]
}
