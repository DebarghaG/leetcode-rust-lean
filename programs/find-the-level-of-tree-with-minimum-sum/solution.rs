pub fn minimum_level(root: &Tree) -> i64 {
    let mut sums: Vec<i64> = Vec::new();
    accumulate_level_sums(root, 0, &mut sums);

    let n: usize = sums.len();
    if n == 0 {
        return 0;
    }

    let mut best_sum: i64 = sums[0];
    let mut best_level: i64 = 1;

    let mut i: usize = 1;
    let mut level: i64 = 2;
    while i < n {
        let s: i64 = sums[i];
        if s < best_sum {
            best_sum = s;
            best_level = level;
        }
        i = i + 1;
        level = level + 1;
    }

    best_level
}

fn accumulate_level_sums(tree: &Tree, depth: usize, sums: &mut Vec<i64>) {
    match tree {
        Tree::Null => {}
        Tree::Node(value, left, right) => {
            if depth < sums.len() {
                let cur: i64 = sums[depth];
                sums[depth] = cur + *value;
            } else {
                sums.push(*value);
            }
            accumulate_level_sums(left, depth + 1, sums);
            accumulate_level_sums(right, depth + 1, sums);
        }
    }
}
