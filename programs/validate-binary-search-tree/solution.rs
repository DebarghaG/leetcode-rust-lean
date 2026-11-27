const NEG_INF: i64 = -2147483649;
const POS_INF: i64 = 2147483648;

fn is_valid_bst_helper(t: &Tree, lo: i64, hi: i64) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(v, left, right) => {
            let value = *v;

            if value <= lo {
                return false;
            }
            if value >= hi {
                return false;
            }

            if !is_valid_bst_helper(&**left, lo, value) {
                return false;
            }
            if !is_valid_bst_helper(&**right, value, hi) {
                return false;
            }

            true
        }
    }
}

pub fn is_valid_bst(root: &Tree) -> bool {
    is_valid_bst_helper(root, NEG_INF, POS_INF)
}
