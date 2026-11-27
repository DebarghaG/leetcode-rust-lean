fn inorder(t: &Tree, out: Vec<i64>) -> Vec<i64> {
    match t {
        Tree::Null => out,
        Tree::Node(v, l, r) => {
            let mut out = inorder(&**l, out);
            out.push(*v);
            inorder(&**r, out)
        }
    }
}

fn build_balanced(vals: &[i64]) -> Tree {
    let n = vals.len();
    if n == 0 {
        return Tree::Null;
    }

    let mut los: Vec<i64> = Vec::new();
    let mut his: Vec<i64> = Vec::new();
    let mut states: Vec<i64> = Vec::new();
    let mut built: Vec<Tree> = Vec::new();

    los.push(0);
    his.push((n as i64) - 1);
    states.push(0);

    while los.len() > 0 {
        let idx = los.len() - 1;
        let lo = los[idx];
        let hi = his[idx];

        if lo > hi {
            los.pop();
            his.pop();
            states.pop();
            built.push(Tree::Null);
            continue;
        }

        if states[idx] == 0 {
            states[idx] = 1;
            let mid = (lo + hi) / 2;

            los.push(mid + 1);
            his.push(hi);
            states.push(0);

            los.push(lo);
            his.push(mid - 1);
            states.push(0);
        } else {
            let mid = (lo + hi) / 2;

            let right = match built.pop() {
                Some(x) => x,
                None => Tree::Null,
            };
            let left = match built.pop() {
                Some(x) => x,
                None => Tree::Null,
            };

            los.pop();
            his.pop();
            states.pop();

            built.push(Tree::Node(
                vals[mid as usize],
                Box::new(left),
                Box::new(right),
            ));
        }
    }

    match built.pop() {
        Some(x) => x,
        None => Tree::Null,
    }
}

pub fn balance_bst(root: &Tree) -> Tree {
    let vals = inorder(root, Vec::new());
    build_balanced(&vals)
}
