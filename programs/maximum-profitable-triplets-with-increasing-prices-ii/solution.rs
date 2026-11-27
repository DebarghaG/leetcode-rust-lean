fn seg_query(tree: &[i64], size: usize, mut l: usize, mut r: usize) -> i64 {
    let mut ans: i64 = 0;
    l += size;
    r += size;

    while l < r {
        if l % 2 == 1 {
            if tree[l] > ans {
                ans = tree[l];
            }
            l += 1;
        }
        if r % 2 == 1 {
            r -= 1;
            if tree[r] > ans {
                ans = tree[r];
            }
        }
        l /= 2;
        r /= 2;
    }

    ans
}

fn seg_update(tree: &mut Vec<i64>, size: usize, pos: usize, val: i64) {
    let mut i = size + pos;

    if val > tree[i] {
        tree[i] = val;
    }

    i /= 2;
    while i > 0 {
        let left_i = i * 2;
        let right_i = left_i + 1;

        let mut best = tree[left_i];
        if tree[right_i] > best {
            best = tree[right_i];
        }

        tree[i] = best;
        i /= 2;
    }
}

pub fn max_profit(prices: &[i64], profits: &[i64]) -> i64 {
    let n = prices.len();
    if n < 3 {
        return -1;
    }

    let mut max_price: i64 = 0;
    let mut i = 0;
    while i < n {
        if prices[i] > max_price {
            max_price = prices[i];
        }
        i += 1;
    }

    let max_p = max_price as usize;

    let mut size: usize = 1;
    while size <= max_p {
        size *= 2;
    }

    let tree_len = size * 2;

    let mut left_tree: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < tree_len {
        left_tree.push(0);
        z += 1;
    }

    let mut right_tree: Vec<i64> = Vec::new();
    z = 0;
    while z < tree_len {
        right_tree.push(0);
        z += 1;
    }

    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();
    z = 0;
    while z < n {
        left.push(0);
        right.push(0);
        z += 1;
    }

    let mut j = 0;
    while j < n {
        let p = prices[j] as usize;

        if p > 1 {
            left[j] = seg_query(&left_tree, size, 1, p);
        }

        seg_update(&mut left_tree, size, p, profits[j]);
        j += 1;
    }

    let mut j = n;
    while j > 0 {
        j -= 1;
        let p = prices[j] as usize;

        right[j] = seg_query(&right_tree, size, p + 1, max_p + 1);
        seg_update(&mut right_tree, size, p, profits[j]);
    }

    let mut ans: i64 = -1;
    let mut j = 0;
    while j < n {
        if left[j] > 0 {
            if right[j] > 0 {
                let total = left[j] + profits[j] + right[j];
                if total > ans {
                    ans = total;
                }
            }
        }
        j += 1;
    }

    ans
}
