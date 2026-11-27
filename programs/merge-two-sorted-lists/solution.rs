fn copy_list(list: &List) -> List {
    match list {
        List::Nil => List::Nil,
        List::Cons(value, next) => {
            List::Cons(*value, Box::new(copy_list(&**next)))
        }
    }
}

pub fn merge_two_lists(list1: &List, list2: &List) -> List {
    match list1 {
        List::Nil => copy_list(list2),
        List::Cons(value1, next1) => {
            match list2 {
                List::Nil => copy_list(list1),
                List::Cons(value2, next2) => {
                    if *value1 <= *value2 {
                        List::Cons(
                            *value1,
                            Box::new(merge_two_lists(&**next1, list2)),
                        )
                    } else {
                        List::Cons(
                            *value2,
                            Box::new(merge_two_lists(list1, &**next2)),
                        )
                    }
                }
            }
        }
    }
}
