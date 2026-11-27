// Recursively walk the linked list (allowed: recursion on the enum) and
// push values into a Vec. No loop here, and the recursive call is not
// inside any loop.
fn collect(l: &List, out: &mut Vec<i64>) {
    match l {
        List::Nil => {}
        List::Cons(v, next) => {
            out.push(*v);
            collect(&**next, out);
        }
    }
}

// Build a List back from a Vec from the tail up via recursion on the index
// (no loop that calls recursively).
fn build(vals: &Vec<i64>, i: usize) -> List {
    if i >= vals.len() {
        List::Nil
    } else {
        let rest = build(vals, i + 1);
        List::Cons(vals[i], Box::new(rest))
    }
}

pub fn partition(head: &List, x: i64) -> List {
    // 1) Collect values in original order.
    let mut vals: Vec<i64> = Vec::new();
    collect(head, &mut vals);

    // 2) Split into two partitions preserving relative order.
    let mut less: Vec<i64> = Vec::new();
    let mut ge: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < vals.len() {
        if vals[i] < x {
            less.push(vals[i]);
        } else {
            ge.push(vals[i]);
        }
        i += 1;
    }

    // 3) Concatenate less-partition then greater-or-equal partition.
    let mut result: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < less.len() {
        result.push(less[j]);
        j += 1;
    }

    let mut k: usize = 0;
    while k < ge.len() {
        result.push(ge[k]);
        k += 1;
    }

    // 4) Rebuild the linked list from tail to head.
    build(&result, 0)
}
