fn collect_level_sums(t: &Tree, depth: usize, sums: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            if depth == sums.len() {
                sums.push(0);
            }
            sums[depth] = sums[depth] + *v;
            collect_level_sums(&**l, depth + 1, sums);
            collect_level_sums(&**r, depth + 1, sums);
        }
    }
}

pub fn kth_largest_level_sum(root: &Tree, k: i64) -> i64 {
    let mut sums: Vec<i64> = Vec::new();
    collect_level_sums(root, 0, &mut sums);

    let n = sums.len();
    if k > n as i64 {
        return -1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j + 1 < n - i {
            if sums[j] < sums[j + 1] {
                let tmp = sums[j];
                sums[j] = sums[j + 1];
                sums[j + 1] = tmp;
            }
            j += 1;
        }
        i += 1;
    }

    sums[(k - 1) as usize]
}
