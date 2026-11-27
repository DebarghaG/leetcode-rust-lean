pub fn sort_linked_list(head: &List) -> List {
    let mut negs: Vec<i64> = Vec::new();
    let mut nonnegs: Vec<i64> = Vec::new();

    let mut cur: &List = head;
    let mut done = false;

    while !done {
        match cur {
            List::Nil => {
                done = true;
            }
            List::Cons(v, next) => {
                if *v < 0 {
                    negs.push(*v);
                } else {
                    nonnegs.push(*v);
                }
                cur = &**next;
            }
        }
    }

    let mut out: List = List::Nil;

    let mut i = nonnegs.len();
    while i > 0 {
        i -= 1;
        let value = nonnegs[i];
        out = List::Cons(value, Box::new(out));
    }

    let mut j = 0;
    while j < negs.len() {
        let value = negs[j];
        out = List::Cons(value, Box::new(out));
        j += 1;
    }

    out
}
