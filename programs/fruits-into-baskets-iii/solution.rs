pub fn num_of_unplaced_fruits(fruits: &[i64], baskets: &[i64]) -> i64 {
    let n: usize = baskets.len();

    let mut size: usize = 1;
    while size < n {
        size = size * 2;
    }

    let total: usize = size * 2;
    let mut tree: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        tree.push(0);
        i = i + 1;
    }

    i = 0;
    while i < n {
        tree[size + i] = baskets[i];
        i = i + 1;
    }

    let mut p: usize = size;
    while p > 1 {
        p = p - 1;
        let left_value: i64 = tree[p * 2];
        let right_value: i64 = tree[p * 2 + 1];
        if left_value > right_value {
            tree[p] = left_value;
        } else {
            tree[p] = right_value;
        }
    }

    let mut unplaced: i64 = 0;
    let mut f: usize = 0;
    while f < fruits.len() {
        let quantity: i64 = fruits[f];

        if tree[1] < quantity {
            unplaced = unplaced + 1;
        } else {
            let mut idx: usize = 1;
            while idx < size {
                let left: usize = idx * 2;
                if tree[left] >= quantity {
                    idx = left;
                } else {
                    idx = left + 1;
                }
            }

            tree[idx] = 0;

            let mut parent: usize = idx / 2;
            while parent > 0 {
                let left: usize = parent * 2;
                let left_value: i64 = tree[left];
                let right_value: i64 = tree[left + 1];

                if left_value > right_value {
                    tree[parent] = left_value;
                } else {
                    tree[parent] = right_value;
                }

                parent = parent / 2;
            }
        }

        f = f + 1;
    }

    unplaced
}
