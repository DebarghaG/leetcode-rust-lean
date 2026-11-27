pub fn merge_in_between(list1: &List, a: i64, b: i64, list2: &List) -> List {
    let vals1 = list_to_vec(list1);
    let vals2 = list_to_vec(list2);

    let mut result: Vec<i64> = Vec::new();

    let a_usize = a as usize;
    let b_usize = b as usize;

    let mut i: usize = 0;
    while i < a_usize {
        result.push(vals1[i]);
        i += 1;
    }

    i = 0;
    while i < vals2.len() {
        result.push(vals2[i]);
        i += 1;
    }

    i = b_usize + 1;
    while i < vals1.len() {
        result.push(vals1[i]);
        i += 1;
    }

    vec_to_list(&result)
}

fn list_to_vec(l: &List) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut cur: &List = l;

    loop {
        match cur {
            List::Nil => {
                return out;
            }
            List::Cons(v, next) => {
                out.push(*v);
                cur = &**next;
            }
        }
    }
}

fn vec_to_list(v: &[i64]) -> List {
    let mut out: List = List::Nil;
    let mut i: usize = v.len();

    while i > 0 {
        i -= 1;
        out = List::Cons(v[i], Box::new(out));
    }

    out
}
