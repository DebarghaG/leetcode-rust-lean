pub fn reverse_k_group(head: &List, k: i64) -> List {
    // Collect the node values in reverse order using structural recursion
    // (no loop-carried reference rebinding, no match/break inside a loop).
    let rev: Vec<i64> = collect_reversed(head);
    let n: usize = rev.len();

    // Turn the reversed collection back into forward order.
    let mut vals: Vec<i64> = Vec::new();
    let mut idx: usize = n;
    while idx > 0 {
        idx = idx - 1;
        vals.push(rev[idx]);
    }

    // k as a usize, clamped to at least 1.
    let mut kk: usize = 1;
    if k > 0 {
        kk = k as usize;
    }

    // Build the group-reversed sequence (index reads + push only).
    let mut out_vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i + kk <= n {
        let mut j: usize = i + kk;
        while j > i {
            j = j - 1;
            out_vals.push(vals[j]);
        }
        i = i + kk;
    }
    // Leftover nodes stay in order.
    while i < n {
        out_vals.push(vals[i]);
        i = i + 1;
    }

    // Rebuild the linked list from the tail up.
    let m: usize = out_vals.len();
    let mut out: List = List::Nil;
    let mut p: usize = m;
    while p > 0 {
        p = p - 1;
        let val: i64 = out_vals[p];
        out = List::Cons(val, Box::new(out));
    }

    out
}

fn collect_reversed(l: &List) -> Vec<i64> {
    match l {
        List::Nil => {
            let r: Vec<i64> = Vec::new();
            r
        }
        List::Cons(v, next) => {
            let mut res: Vec<i64> = collect_reversed(&**next);
            res.push(*v);
            res
        }
    }
}
