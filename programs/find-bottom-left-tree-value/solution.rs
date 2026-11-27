fn walk(t: &Tree, depth: i64, depths: &mut Vec<i64>, vals: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            depths.push(depth);
            vals.push(*v);
            walk(&**l, depth + 1, depths, vals);
            walk(&**r, depth + 1, depths, vals);
        }
    }
}

pub fn find_bottom_left_value(root: &Tree) -> i64 {
    let mut depths: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();
    walk(root, 0, &mut depths, &mut vals);

    let n = depths.len();

    let mut maxd: i64 = -1;
    let mut i: usize = 0;
    while i < n {
        if depths[i] > maxd {
            maxd = depths[i];
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut found: bool = false;
    let mut j: usize = 0;
    while j < n {
        if depths[j] == maxd {
            if !found {
                ans = vals[j];
                found = true;
            }
        }
        j += 1;
    }

    ans
}
