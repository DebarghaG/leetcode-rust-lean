fn pop_tree(stack: &mut Vec<Tree>) -> Tree {
    match stack.pop() {
        Some(t) => t,
        None => Tree::Null,
    }
}

pub fn create_binary_tree(descriptions: &[Vec<i64>]) -> Tree {
    let m = descriptions.len();
    if m == 0 {
        return Tree::Null;
    }

    let mut max_val: i64 = 0;
    let mut i = 0;
    while i < m {
        let p = descriptions[i][0];
        let c = descriptions[i][1];
        if p > max_val {
            max_val = p;
        }
        if c > max_val {
            max_val = c;
        }
        i += 1;
    }

    let n = (max_val as usize) + 1;
    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();
    let mut has_parent: Vec<bool> = Vec::new();

    i = 0;
    while i < n {
        left.push(-1);
        right.push(-1);
        has_parent.push(false);
        i += 1;
    }

    i = 0;
    while i < m {
        let p = descriptions[i][0] as usize;
        let c = descriptions[i][1] as usize;
        let is_left = descriptions[i][2];

        if is_left == 1 {
            left[p] = c as i64;
        } else {
            right[p] = c as i64;
        }
        has_parent[c] = true;
        i += 1;
    }

    let mut root: usize = 0;
    i = 0;
    while i < m {
        let p = descriptions[i][0] as usize;
        if !has_parent[p] {
            root = p;
        }
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    let mut tree_stack: Vec<Tree> = Vec::new();
    stack.push(root as i64);

    while stack.len() > 0 {
        let x = stack[stack.len() - 1];
        let _ = stack.pop();

        if x >= 0 {
            let v = x as usize;
            stack.push(-x - 1);

            let ri = right[v];
            let li = left[v];

            if ri != -1 {
                stack.push(ri);
            }
            if li != -1 {
                stack.push(li);
            }
        } else {
            let v = (-x - 1) as usize;

            let mut right_tree = Tree::Null;
            if right[v] != -1 {
                right_tree = pop_tree(&mut tree_stack);
            }

            let mut left_tree = Tree::Null;
            if left[v] != -1 {
                left_tree = pop_tree(&mut tree_stack);
            }

            let node = Tree::Node(v as i64, Box::new(left_tree), Box::new(right_tree));
            tree_stack.push(node);
        }
    }

    pop_tree(&mut tree_stack)
}
