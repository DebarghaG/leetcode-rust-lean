pub fn build_tree(inorder: &[i64], postorder: &[i64]) -> Tree {
    let n = inorder.len();
    if n == 0 {
        return Tree::Null;
    }

    // pos[v + 3000] = index of value v in inorder.
    let mut pos: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 6001 {
        pos.push(-1);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = inorder[i];
        let key = (v + 3000) as usize;
        pos[key] = i as i64;
        i += 1;
    }

    // Explicit stack for iterative postorder-style construction.
    // kind 0 = process an inorder/postorder segment
    // kind 1 = combine two completed children with the stored root value
    let mut stack_kind: Vec<i64> = Vec::new();
    let mut stack_a: Vec<i64> = Vec::new();
    let mut stack_b: Vec<i64> = Vec::new();
    let mut stack_c: Vec<i64> = Vec::new();
    let mut stack_d: Vec<i64> = Vec::new();
    let mut stack_val: Vec<i64> = Vec::new();

    let mut values: Vec<Tree> = Vec::new();

    stack_kind.push(0);
    stack_a.push(0);
    stack_b.push(n as i64);
    stack_c.push(0);
    stack_d.push(n as i64);
    stack_val.push(0);

    while stack_kind.len() > 0 {
        let top = stack_kind.len() - 1;
        let sk = stack_kind[top];
        let a = stack_a[top];
        let b = stack_b[top];
        let c = stack_c[top];
        let d = stack_d[top];
        let val = stack_val[top];

        stack_kind.pop();
        stack_a.pop();
        stack_b.pop();
        stack_c.pop();
        stack_d.pop();
        stack_val.pop();

        if sk == 0 {
            let in_l = a as usize;
            let in_r = b as usize;
            let post_l = c as usize;
            let post_r = d as usize;
            let len = in_r - in_l;

            if len == 0 {
                values.push(Tree::Null);
            } else {
                let root_val = postorder[post_r - 1];
                let key = (root_val + 3000) as usize;
                let idx = pos[key] as usize;

                let left_len = idx - in_l;

                // Push combine task.
                stack_kind.push(1);
                stack_a.push(0);
                stack_b.push(0);
                stack_c.push(0);
                stack_d.push(0);
                stack_val.push(root_val);

                // Push right child task.
                stack_kind.push(0);
                stack_a.push((idx + 1) as i64);
                stack_b.push(in_r as i64);
                stack_c.push((post_l + left_len) as i64);
                stack_d.push((post_r - 1) as i64);
                stack_val.push(0);

                // Push left child task.
                stack_kind.push(0);
                stack_a.push(in_l as i64);
                stack_b.push(idx as i64);
                stack_c.push(post_l as i64);
                stack_d.push((post_l + left_len) as i64);
                stack_val.push(0);
            }
        } else {
            let right = match values.pop() {
                Some(t) => t,
                None => Tree::Null,
            };
            let left = match values.pop() {
                Some(t) => t,
                None => Tree::Null,
            };

            values.push(Tree::Node(val, Box::new(left), Box::new(right)));
        }
    }

    match values.pop() {
        Some(t) => t,
        None => Tree::Null,
    }
}
