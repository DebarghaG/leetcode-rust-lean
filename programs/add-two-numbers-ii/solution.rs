fn collect_digits(list: &List, out: &mut Vec<i64>) {
    match list {
        List::Nil => {}
        List::Cons(value, next) => {
            out.push(*value);
            collect_digits(next, out);
        }
    }
}

pub fn add_two_numbers(l1: &List, l2: &List) -> List {
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();

    collect_digits(l1, &mut a);
    collect_digits(l2, &mut b);

    let mut digits: Vec<i64> = Vec::new();
    let mut i = a.len();
    let mut j = b.len();
    let mut carry: i64 = 0;

    while i > 0 || j > 0 || carry > 0 {
        let mut sum = carry;

        if i > 0 {
            i -= 1;
            sum += a[i];
        }

        if j > 0 {
            j -= 1;
            sum += b[j];
        }

        digits.push(sum % 10);
        carry = sum / 10;
    }

    let mut result = List::Nil;
    let mut k = 0;

    while k < digits.len() {
        result = List::Cons(digits[k], Box::new(result));
        k += 1;
    }

    result
}
