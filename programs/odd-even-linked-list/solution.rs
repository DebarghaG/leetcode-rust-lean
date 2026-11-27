fn to_rev_vec(l: &List) -> Vec<i64> {
    match l {
        List::Nil => Vec::new(),
        List::Cons(x, next) => {
            let mut res = to_rev_vec(next);
            res.push(*x);
            res
        }
    }
}

fn build_from(v: &Vec<i64>, i: usize) -> List {
    if i >= v.len() {
        List::Nil
    } else {
        let rest = build_from(v, i + 1);
        List::Cons(v[i], Box::new(rest))
    }
}

pub fn odd_even_list(head: &List) -> List {
    // Collect values in reverse order (efficient single push per node).
    let rev = to_rev_vec(head);
    let n = rev.len();

    // Reverse again to obtain forward order.
    let mut vals: Vec<i64> = Vec::new();
    let mut i = n;
    while i > 0 {
        i -= 1;
        vals.push(rev[i]);
    }

    // First all even-indexed positions (the "odd" group), then odd-indexed.
    let mut order: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        if j % 2 == 0 {
            order.push(vals[j]);
        }
        j += 1;
    }

    let mut k = 0;
    while k < n {
        if k % 2 == 1 {
            order.push(vals[k]);
        }
        k += 1;
    }

    build_from(&order, 0)
}
