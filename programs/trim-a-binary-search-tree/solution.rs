pub fn trim_bst(root: &Tree, low: i64, high: i64) -> Tree {
    match root {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => {
            let val = *v;

            if val < low {
                trim_bst(&**right, low, high)
            } else if val > high {
                trim_bst(&**left, low, high)
            } else {
                let new_left = trim_bst(&**left, low, high);
                let new_right = trim_bst(&**right, low, high);
                Tree::Node(val, Box::new(new_left), Box::new(new_right))
            }
        }
    }
}
