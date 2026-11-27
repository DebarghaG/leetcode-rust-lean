pub fn remaining_methods(n: i64, k: i64, invocations: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = n as usize;

    // Build adjacency list of invocations.
    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e = 0;
    while e < invocations.len() {
        let a = invocations[e][0];
        let b = invocations[e][1];
        let ai = a as usize;
        adj[ai].push(b);
        e += 1;
    }

    // Find all methods reachable from k.
    let mut suspicious: Vec<bool> = Vec::new();
    let mut j = 0;
    while j < n_usize {
        suspicious.push(false);
        j += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    queue.push(k);
    suspicious[k as usize] = true;

    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head];
        let ui = u as usize;
        head += 1;

        let mut idx = 0;
        while idx < adj[ui].len() {
            let v = adj[ui][idx];
            let vi = v as usize;
            if !suspicious[vi] {
                suspicious[vi] = true;
                queue.push(v);
            }
            idx += 1;
        }
    }

    // If any non-suspicious method invokes a suspicious method, we cannot remove any method.
    let mut check = 0;
    while check < invocations.len() {
        let a = invocations[check][0];
        let b = invocations[check][1];
        if !suspicious[a as usize] && suspicious[b as usize] {
            let mut all: Vec<i64> = Vec::new();
            let mut x = 0;
            while x < n_usize {
                all.push(x as i64);
                x += 1;
            }
            return all;
        }
        check += 1;
    }

    // Otherwise, return all non-suspicious methods.
    let mut result: Vec<i64> = Vec::new();
    let mut x = 0;
    while x < n_usize {
        if !suspicious[x] {
            result.push(x as i64);
        }
        x += 1;
    }
    result
}
