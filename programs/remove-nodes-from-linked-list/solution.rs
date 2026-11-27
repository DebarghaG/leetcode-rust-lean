// The previous version matched on `&rest` and mutated outer locals inside the
// arm, which the Aeneas context-matcher could not handle.  Here we match the
// recursively built suffix BY VALUE and consume it directly in each branch.

pub fn remove_nodes(head: &List) -> List {
    match head {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            // Filtered suffix (nodes to the right, already processed).
            let rest = remove_nodes(&**next);
            match rest {
                // No node to the right: this node is never removed.
                List::Nil => List::Cons(*v, Box::new(List::Nil)),
                // The head `m` of the filtered suffix is the maximum of the
                // original suffix, so it decides whether `v` survives.
                List::Cons(m, rest_next) => {
                    if *v < m {
                        // A strictly greater node exists to the right.
                        List::Cons(m, rest_next)
                    } else {
                        // No greater node to the right: keep this one.
                        List::Cons(*v, Box::new(List::Cons(m, rest_next)))
                    }
                }
            }
        }
    }
}
