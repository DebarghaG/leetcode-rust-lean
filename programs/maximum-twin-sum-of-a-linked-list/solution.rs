pub fn pair_sum(head: &List) -> i64 {
    let mut vals: Vec<i64> = Vec::new();
    let mut cur: &List = head;
    let mut done: bool = false;

    while !done {
        match cur {
            List::Nil => {
                done = true;
            }
            List::Cons(v, next) => {
                vals.push(*v);
                cur = &**next;
            }
        }
    }

    let n = vals.len();
    let half = n / 2;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < half {
        let s = vals[i] + vals[n - 1 - i];
        if s > ans {
            ans = s;
        }
        i += 1;
    }

    ans
}
