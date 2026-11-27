fn collect_rev(l: &List) -> Vec<i64> {
    match l {
        List::Nil => Vec::new(),
        List::Cons(v, next) => {
            let mut rest: Vec<i64> = collect_rev(&**next);
            rest.push(*v);
            rest
        }
    }
}

pub fn delete_duplicates(head: &List) -> List {
    let vals_rev: Vec<i64> = collect_rev(head);

    let mut vals: Vec<i64> = Vec::new();
    let mut idx: usize = vals_rev.len();
    while idx > 0 {
        idx -= 1;
        vals.push(vals_rev[idx]);
    }

    let mut unique: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < vals.len() {
        let v: i64 = vals[i];
        let mut j: usize = i + 1;
        while j < vals.len() && vals[j] == v {
            j += 1;
        }
        if j == i + 1 {
            unique.push(v);
        }
        i = j;
    }

    let mut res: List = List::Nil;
    let mut k: usize = unique.len();
    while k > 0 {
        k -= 1;
        let v: i64 = unique[k];
        res = List::Cons(v, Box::new(res));
    }
    res
}
