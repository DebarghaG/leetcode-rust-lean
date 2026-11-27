fn collect(t: &Tree, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            out.push(*v);
            collect(l, out);
            collect(r, out);
        }
    }
}

pub fn find_target(root: &Tree, k: i64) -> bool {
    let mut vals: Vec<i64> = Vec::new();
    collect(root, &mut vals);
    let n = vals.len();

    if n < 2 {
        return false;
    }

    // Sort to be robust even if the input is not a perfect BST ordering.
    vals.sort();

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    while i < j {
        let s = vals[i] + vals[j];
        if s == k {
            return true;
        }
        if s < k {
            i += 1;
        } else {
            j -= 1;
        }
    }

    false
}
