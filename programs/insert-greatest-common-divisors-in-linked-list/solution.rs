fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn insert_gcd_list(head: &List) -> List {
    match head {
        List::Nil => List::Nil,
        List::Cons(v, next) => {
            let transformed_tail = insert_gcd_list(next);

            match &**next {
                List::Nil => List::Cons(*v, Box::new(transformed_tail)),
                List::Cons(w, _) => {
                    let g = gcd(*v, *w);
                    List::Cons(
                        *v,
                        Box::new(List::Cons(g, Box::new(transformed_tail))),
                    )
                }
            }
        }
    }
}

pub fn insert_greatest_common_divisors(head: &List) -> List {
    insert_gcd_list(head)
}
