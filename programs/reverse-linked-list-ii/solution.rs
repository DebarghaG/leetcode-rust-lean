fn collect_values(l: &List, acc: Vec<i64>) -> Vec<i64> {
    match l {
        List::Nil => acc,
        List::Cons(v, next) => {
            let mut new_acc = acc;
            new_acc.push(*v);
            collect_values(next, new_acc)
        }
    }
}

pub fn reverse_between(head: &List, left: i64, right: i64) -> List {
    let mut vals = collect_values(head, Vec::new());

    let l = (left - 1) as usize;
    let r = (right - 1) as usize;

    let mut i = l;
    let mut j = r;
    while i < j {
        let tmp = vals[i];
        vals[i] = vals[j];
        vals[j] = tmp;
        i += 1;
        j -= 1;
    }

    let mut result = List::Nil;
    let mut k = vals.len();
    while k > 0 {
        k -= 1;
        result = List::Cons(vals[k], Box::new(result));
    }

    result
}
