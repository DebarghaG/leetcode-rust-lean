fn convert(l: &List, acc: i64) -> i64 {
    match l {
        List::Nil => acc,
        List::Cons(v, next) => convert(&**next, acc * 2 + *v),
    }
}

pub fn get_decimal_value(head: &List) -> i64 {
    convert(head, 0)
}
