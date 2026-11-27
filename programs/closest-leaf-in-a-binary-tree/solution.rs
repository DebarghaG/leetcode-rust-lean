fn child_value(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, _, _) => *v,
    }
}

fn fill(t: &Tree, parent: i64, arr: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            let val = *v;
            let b = (val as usize) * 3;
            let lv = child_value(&**l);
            let rv = child_value(&**r);
            arr[b] = parent;
            arr[b + 1] = lv;
            arr[b + 2] = rv;
            fill(&**l, val, arr);
            fill(&**r, val, arr);
        }
    }
}

pub fn find_closest_leaf(root: &Tree, k: i64) -> i64 {
    let n: usize = 1001;

    // Packed array: for node value v, base = 3*v holds
    //   arr[base]   = parent value (0 means none)
    //   arr[base+1] = left child value (0 means none)
    //   arr[base+2] = right child value (0 means none)
    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n * 3 {
        arr.push(0);
        i += 1;
    }

    fill(root, 0, &mut arr);

    let mut visited: Vec<bool> = Vec::new();
    i = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    queue.push(k);
    visited[k as usize] = true;

    let mut head: usize = 0;
    while head < queue.len() {
        let cur = queue[head];
        head += 1;

        let ci = cur as usize;
        let lb = ci * 3;
        let pc = arr[lb];
        let lc = arr[lb + 1];
        let rc = arr[lb + 2];

        if lc == 0 && rc == 0 {
            return cur;
        }

        if pc != 0 && !visited[pc as usize] {
            visited[pc as usize] = true;
            queue.push(pc);
        }
        if lc != 0 && !visited[lc as usize] {
            visited[lc as usize] = true;
            queue.push(lc);
        }
        if rc != 0 && !visited[rc as usize] {
            visited[rc as usize] = true;
            queue.push(rc);
        }
    }

    k
}
