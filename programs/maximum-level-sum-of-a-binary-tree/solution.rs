pub fn max_level_sum(root: &Tree) -> i64 {
    let h = tree_height(root);
    if h == 0 {
        return 0;
    }

    let mut sums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < h {
        sums.push(0);
        i += 1;
    }

    let sums = fill_level_sums(root, 1, sums);

    let mut best_sum: i64 = sums[0];
    let mut best_level: i64 = 1;
    let mut idx: usize = 1;
    let mut level: i64 = 2;

    while idx < sums.len() {
        if sums[idx] > best_sum {
            best_sum = sums[idx];
            best_level = level;
        }
        idx += 1;
        level += 1;
    }

    best_level
}

fn tree_height(t: &Tree) -> usize {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let hl = tree_height(&**left);
            let hr = tree_height(&**right);
            if hl > hr {
                hl + 1
            } else {
                hr + 1
            }
        }
    }
}

fn fill_level_sums(t: &Tree, level: usize, mut sums: Vec<i64>) -> Vec<i64> {
    match t {
        Tree::Null => sums,
        Tree::Node(value, left, right) => {
            sums[level - 1] += *value;
            let sums = fill_level_sums(&**left, level + 1, sums);
            fill_level_sums(&**right, level + 1, sums)
        }
    }
}
