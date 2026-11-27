pub fn add_two_numbers(l1: &List, l2: &List) -> List {
    let mut a: Vec<i64> = Vec::new();
    let mut cur1 = l1;
    let mut done1 = false;
    while !done1 {
        match cur1 {
            List::Nil => {
                done1 = true;
            }
            List::Cons(v, next) => {
                a.push(*v);
                cur1 = &**next;
            }
        }
    }

    let mut b: Vec<i64> = Vec::new();
    let mut cur2 = l2;
    let mut done2 = false;
    while !done2 {
        match cur2 {
            List::Nil => {
                done2 = true;
            }
            List::Cons(v, next) => {
                b.push(*v);
                cur2 = &**next;
            }
        }
    }

    let n1 = a.len();
    let n2 = b.len();
    let mut n = n1;
    if n2 > n {
        n = n2;
    }

    let mut res: Vec<i64> = Vec::new();
    let mut carry: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut sum: i64 = carry;
        if i < n1 {
            sum = sum + a[i];
        }
        if i < n2 {
            sum = sum + b[i];
        }
        let digit: i64 = sum % 10;
        carry = sum / 10;
        res.push(digit);
        i = i + 1;
    }
    if carry > 0 {
        res.push(carry);
    }

    let mut result = List::Nil;
    let mut j = res.len();
    while j > 0 {
        j = j - 1;
        result = List::Cons(res[j], Box::new(result));
    }
    result
}
