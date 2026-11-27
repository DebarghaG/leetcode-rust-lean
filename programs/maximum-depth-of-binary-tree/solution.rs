pub fn max_depth(root: &Tree) -> i64 {
    match root {
        Tree::Null => {
            return 0;
        }
        Tree::Node(_, left, right) => {
            let dl = max_depth(&**left);
            let dr = max_depth(&**right);
            if dl > dr {
                return dl + 1;
            } else {
                return dr + 1;
            }
        }
    }
}
