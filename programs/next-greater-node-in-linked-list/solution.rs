fn collect_values(list: &List, vals: &mut Vec<i64>) {
    match list {
        List::Nil => {}
        List::Cons(v, next) => {
            vals.push(*v);
            collect_values(&**next, vals);
        }
    }
}

pub fn next_larger_nodes(head: &List) -> Vec<i64> {
    let mut vals: Vec<i64> = Vec::new();
    collect_values(head, &mut vals);

    let n = vals.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    let mut j = n;

    while j > 0 {
        j -= 1;
        let x = vals[j];

        while stack.len() > 0 {
            let top = stack[stack.len() - 1];
            if top <= x {
                stack.pop();
            } else {
                break;
            }
        }

        if stack.len() > 0 {
            ans[j] = stack[stack.len() - 1];
        }

        stack.push(x);
    }

    ans
}
