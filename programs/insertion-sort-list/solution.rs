fn copy_values(l: &List, out: &mut Vec<i64>) {
    match l {
        List::Nil => {}
        List::Cons(v, next) => {
            out.push(*v);
            let next_ref: &List = &**next;
            copy_values(next_ref, out);
        }
    }
}

pub fn insertion_sort_list(head: &List) -> List {
    let mut vals: Vec<i64> = Vec::new();
    copy_values(head, &mut vals);

    let n = vals.len();
    let mut i: usize = 1;
    while i < n {
        let key = vals[i];
        let mut j: usize = i;
        while j > 0 && vals[j - 1] > key {
            vals[j] = vals[j - 1];
            j -= 1;
        }
        vals[j] = key;
        i += 1;
    }

    let mut result = List::Nil;
    let mut k = vals.len();
    while k > 0 {
        k -= 1;
        let val = vals[k];
        result = List::Cons(val, Box::new(result));
    }

    result
}
