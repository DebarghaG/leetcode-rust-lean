pub fn double_it(head: &List) -> List {
    let mut digits: Vec<i64> = Vec::new();
    let mut cur: &List = head;
    let mut done: bool = false;

    while !done {
        match cur {
            List::Nil => {
                done = true;
            }
            List::Cons(v, next) => {
                digits.push(*v);
                cur = &**next;
            }
        }
    }

    let n = digits.len();
    let mut out_digits: Vec<i64> = Vec::new();
    let mut carry: i64 = 0;
    let mut i: usize = n;

    while i > 0 {
        i = i - 1;
        let val = digits[i] * 2 + carry;
        out_digits.push(val % 10);
        carry = val / 10;
    }

    if carry > 0 {
        out_digits.push(carry);
    }

    let mut result: List = List::Nil;
    let m = out_digits.len();
    let mut j: usize = 0;

    while j < m {
        result = List::Cons(out_digits[j], Box::new(result));
        j = j + 1;
    }

    result
}
