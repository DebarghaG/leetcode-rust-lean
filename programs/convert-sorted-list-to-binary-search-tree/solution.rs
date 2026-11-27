pub fn sorted_list_to_bst(head: &List) -> Tree {
    let mut values: Vec<i64> = Vec::new();
    let mut cur = head;

    loop {
        match cur {
            List::Nil => break,
            List::Cons(v, next) => {
                values.push(*v);
                cur = &**next;
            }
        }
    }

    let n = values.len();
    build(&values, 0, n)
}

fn build(xs: &[i64], lo: usize, hi: usize) -> Tree {
    if lo >= hi {
        return Tree::Null;
    }

    let mid = lo + (hi - lo - 1) / 2;
    let left = build(xs, lo, mid);
    let right = build(xs, mid + 1, hi);

    Tree::Node(xs[mid], Box::new(left), Box::new(right))
}
