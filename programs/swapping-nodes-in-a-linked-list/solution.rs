fn list_length(l: &List) -> usize {
    match l {
        List::Nil => 0,
        List::Cons(_, next) => 1 + list_length(next),
    }
}

// Structural recursion over the list: `l` strictly shrinks on each call,
// `counter` just tracks the original position. `target` is a valid index.
fn value_at(l: &List, counter: usize, target: usize) -> i64 {
    match l {
        List::Nil => 0,
        List::Cons(v, next) => {
            if counter == target {
                *v
            } else {
                value_at(next, counter + 1, target)
            }
        }
    }
}

// Rebuild the list top-down (structural recursion on `l`), replacing the
// value at position `i` with `vj` and at position `j` with `vi`.
fn build_swapped(l: &List, idx: usize, i: usize, j: usize, vi: i64, vj: i64) -> List {
    match l {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            let newv = if idx == i {
                vj
            } else if idx == j {
                vi
            } else {
                *v
            };
            List::Cons(newv, Box::new(build_swapped(next, idx + 1, i, j, vi, vj)))
        }
    }
}

pub fn swap_nodes(head: &List, k: i64) -> List {
    let n = list_length(head);
    let kk = k as usize;
    // 0-indexed positions of the kth-from-start and kth-from-end nodes.
    let i = kk - 1;
    let j = n - kk;

    let vi = value_at(head, 0, i);
    let vj = value_at(head, 0, j);

    build_swapped(head, 0, i, j, vi, vj)
}
