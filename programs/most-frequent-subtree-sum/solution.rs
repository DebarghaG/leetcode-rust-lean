fn collect_subtree_sums(t: &Tree, out: &mut Vec<i64>) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let left_sum = collect_subtree_sums(&**l, out);
            let right_sum = collect_subtree_sums(&**r, out);
            let total = *v + left_sum + right_sum;
            out.push(total);
            total
        }
    }
}

pub fn find_frequent_tree_sum(root: &Tree) -> Vec<i64> {
    let mut all_sums: Vec<i64> = Vec::new();
    collect_subtree_sums(root, &mut all_sums);

    let mut distinct_sums: Vec<i64> = Vec::new();
    let mut frequencies: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < all_sums.len() {
        let value = all_sums[i];

        let mut j: usize = 0;
        let mut found = false;
        while j < distinct_sums.len() && !found {
            if distinct_sums[j] == value {
                frequencies[j] = frequencies[j] + 1;
                found = true;
            }
            j = j + 1;
        }

        if !found {
            distinct_sums.push(value);
            frequencies.push(1);
        }

        i = i + 1;
    }

    let mut max_freq: i64 = 0;
    let mut a: usize = 0;
    while a < frequencies.len() {
        if frequencies[a] > max_freq {
            max_freq = frequencies[a];
        }
        a = a + 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < distinct_sums.len() {
        if frequencies[b] == max_freq {
            result.push(distinct_sums[b]);
        }
        b = b + 1;
    }

    result
}
