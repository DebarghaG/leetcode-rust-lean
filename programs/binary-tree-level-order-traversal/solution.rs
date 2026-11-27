pub fn level_order(root: &Tree) -> Vec<Vec<i64>> {
    collect_levels(root)
}

// Returns the level-order traversal of the subtree rooted at `node`.
// Each element of the result is one level, left-to-right.
fn collect_levels(node: &Tree) -> Vec<Vec<i64>> {
    match node {
        Tree::Null => {
            let empty: Vec<Vec<i64>> = Vec::new();
            empty
        }
        Tree::Node(value, left, right) => {
            let left_levels: Vec<Vec<i64>> = collect_levels(&**left);
            let right_levels: Vec<Vec<i64>> = collect_levels(&**right);

            let mut result: Vec<Vec<i64>> = Vec::new();

            // The root is always its own first level.
            let mut root_level: Vec<i64> = Vec::new();
            root_level.push(*value);
            result.push(root_level);

            // Merge the levels of the two subtrees depth by depth.
            let mut depth: usize = 0;
            while depth < left_levels.len() || depth < right_levels.len() {
                let mut row: Vec<i64> = Vec::new();

                if depth < left_levels.len() {
                    let mut j: usize = 0;
                    while j < left_levels[depth].len() {
                        row.push(left_levels[depth][j]);
                        j += 1;
                    }
                }

                if depth < right_levels.len() {
                    let mut j: usize = 0;
                    while j < right_levels[depth].len() {
                        row.push(right_levels[depth][j]);
                        j += 1;
                    }
                }

                result.push(row);
                depth += 1;
            }

            result
        }
    }
}

// Test-only helper: pin the *empty* `vec![]` literal (the expected result for an
// empty tree) to `Vec<Vec<i64>>` so it is not ambiguous, while delegating every
// non-empty use to the standard library macro. Absent from non-test builds.
#[cfg(test)]
#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($($tt:tt)*) => {
        ::std::vec![$($tt)*]
    };
}
