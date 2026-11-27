fn collect(l: &List, out: &mut Vec<i64>) {
    match l {
        List::Nil => {}
        List::Cons(v, next) => {
            out.push(*v);
            collect(&**next, out);
        }
    }
}

pub fn nodes_between_critical_points(head: &List) -> Vec<i64> {
    let mut vals: Vec<i64> = Vec::new();
    collect(head, &mut vals);

    let n: usize = vals.len();
    let mut crit: Vec<i64> = Vec::new();

    let mut i: usize = 1;
    while i + 1 < n {
        let a: i64 = vals[i - 1];
        let b: i64 = vals[i];
        let c: i64 = vals[i + 1];
        if (b > a && b > c) || (b < a && b < c) {
            crit.push(i as i64);
        }
        i += 1;
    }

    let mut res: Vec<i64> = Vec::new();
    if crit.len() < 2 {
        res.push(-1);
        res.push(-1);
        return res;
    }

    let max_d: i64 = crit[crit.len() - 1] - crit[0];
    let mut min_d: i64 = max_d;

    let mut k: usize = 1;
    while k < crit.len() {
        let d: i64 = crit[k] - crit[k - 1];
        if d < min_d {
            min_d = d;
        }
        k += 1;
    }

    res.push(min_d);
    res.push(max_d);
    res
}
