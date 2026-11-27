fn inorder(t: &Tree, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, left, right) => {
            inorder(&**left, out);
            out.push(*v);
            inorder(&**right, out);
        }
    }
}

pub fn find_mode(root: &Tree) -> Vec<i64> {
    let mut vals: Vec<i64> = Vec::new();
    inorder(root, &mut vals);

    let n = vals.len();
    let mut modes: Vec<i64> = Vec::new();

    if n == 0 {
        return modes;
    }

    let mut prev = vals[0];
    let mut count: i64 = 0;
    let mut max_count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let cur = vals[i];

        if cur == prev {
            count += 1;
        } else {
            prev = cur;
            count = 1;
        }

        if count > max_count {
            max_count = count;
            modes = Vec::new();
            modes.push(cur);
        } else if count == max_count {
            modes.push(cur);
        }

        i += 1;
    }

    modes
}
