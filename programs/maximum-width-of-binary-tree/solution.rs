fn flatten_tree(t: &Tree, left: &mut Vec<i64>, right: &mut Vec<i64>) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(_value, l, r) => {
            let left_idx: i64 = flatten_tree(&**l, left, right);
            let right_idx: i64 = flatten_tree(&**r, left, right);

            let idx: i64 = left.len() as i64;
            left.push(left_idx);
            right.push(right_idx);
            idx
        }
    }
}

pub fn width_of_binary_tree(root: &Tree) -> i64 {
    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();

    let root_idx: i64 = flatten_tree(root, &mut left, &mut right);
    if root_idx < 0 {
        return 0;
    }

    let mut cur_nodes: Vec<i64> = Vec::new();
    let mut cur_pos: Vec<i64> = Vec::new();

    cur_nodes.push(root_idx);
    cur_pos.push(0);

    let mut best: i64 = 0;

    while cur_nodes.len() > 0 {
        let base: i64 = cur_pos[0];
        let last_pos: i64 = cur_pos[cur_pos.len() - 1];
        let width: i64 = last_pos - base + 1;

        if width > best {
            best = width;
        }

        let mut next_nodes: Vec<i64> = Vec::new();
        let mut next_pos: Vec<i64> = Vec::new();

        let mut i: usize = 0;
        while i < cur_nodes.len() {
            let node: i64 = cur_nodes[i];
            let pos: i64 = cur_pos[i] - base;

            if node >= 0 {
                let idx: usize = node as usize;

                if idx < left.len() && idx < right.len() {
                    let li: i64 = left[idx];
                    if li >= 0 {
                        next_nodes.push(li);
                        next_pos.push(2 * pos);
                    }

                    let ri: i64 = right[idx];
                    if ri >= 0 {
                        next_nodes.push(ri);
                        next_pos.push(2 * pos + 1);
                    }
                }
            }

            i += 1;
        }

        cur_nodes = next_nodes;
        cur_pos = next_pos;
    }

    best
}
