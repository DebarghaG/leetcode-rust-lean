pub fn validate_binary_tree_nodes(n: i64, leftChild: &[i64], rightChild: &[i64]) -> bool {
    if n <= 0 {
        return false;
    }
    let nn: usize = n as usize;
    if leftChild.len() != nn || rightChild.len() != nn {
        return false;
    }

    // indegree[i] = number of parents pointing at node i.
    // parent[i]   = the unique parent of node i (-1 if root / none).
    let mut indegree: Vec<i64> = Vec::new();
    let mut parent: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < nn {
        indegree.push(0);
        parent.push(-1);
        a = a + 1;
    }

    // Build indegree and parent arrays.  Detect out-of-range children.
    let mut edges_ok: bool = true;

    let mut c: usize = 0;
    while c < nn {
        let l: i64 = leftChild[c];
        if l >= 0 && l < n {
            let li: usize = l as usize;
            indegree[li] = indegree[li] + 1;
            parent[li] = c as i64;
        } else if l != -1 {
            edges_ok = false;
        }

        let r: i64 = rightChild[c];
        if r >= 0 && r < n {
            let ri: usize = r as usize;
            indegree[ri] = indegree[ri] + 1;
            parent[ri] = c as i64;
        } else if r != -1 {
            edges_ok = false;
        }

        c = c + 1;
    }

    // Every non-root node must have indegree exactly 1; count roots.
    let mut indeg_ok: bool = true;
    let mut root_count: i64 = 0;
    let mut d: usize = 0;
    while d < nn {
        if indegree[d] > 1 {
            indeg_ok = false;
        }
        if indegree[d] == 0 {
            root_count = root_count + 1;
        }
        d = d + 1;
    }

    // Cycle detection on the functional "parent" graph.
    // A chain of more than nn steps without reaching -1 means a cycle.
    let mut has_cycle: bool = false;
    let mut s: usize = 0;
    while s < nn && !has_cycle {
        let mut cur: i64 = s as i64;
        let mut step: usize = 0;
        while step < nn && cur != -1 {
            cur = parent[cur as usize];
            step = step + 1;
        }
        if cur != -1 {
            has_cycle = true;
        }
        s = s + 1;
    }

    // Valid binary tree iff:
    //  - no out-of-range edges,
    //  - no node with more than one parent,
    //  - exactly one root,
    //  - no cycle.
    edges_ok && indeg_ok && root_count == 1 && !has_cycle
}
