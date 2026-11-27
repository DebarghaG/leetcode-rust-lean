fn collect_rev(l: &List) -> Vec<i64> {
    match l {
        List::Nil => Vec::new(),
        List::Cons(x, next) => {
            let mut v: Vec<i64> = collect_rev(&**next);
            v.push(*x);
            v
        }
    }
}

pub fn is_palindrome(head: &List) -> bool {
    let vals: Vec<i64> = collect_rev(head);
    let n: usize = vals.len();
    let mut i: usize = 0;

    while i < n / 2 {
        let j: usize = n - 1 - i;
        if vals[i] != vals[j] {
            return false;
        }
        i += 1;
    }

    true
}
