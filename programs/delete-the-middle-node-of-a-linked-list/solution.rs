fn is_nil(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}

pub fn delete_middle(head: &List) -> List {
    let mut vals: Vec<i64> = Vec::new();
    let mut cur: &List = head;

    while !is_nil(cur) {
        match cur {
            List::Nil => {}
            List::Cons(v, next) => {
                vals.push(*v);
                cur = &**next;
            }
        }
    }

    let n: usize = vals.len();
    let mid: usize = n / 2;

    let mut res: List = List::Nil;
    let mut i: usize = n;

    while i > 0 {
        i = i - 1;
        if i != mid {
            res = List::Cons(vals[i], Box::new(res));
        }
    }

    res
}
