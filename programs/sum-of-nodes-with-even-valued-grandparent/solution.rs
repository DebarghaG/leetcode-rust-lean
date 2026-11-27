fn dfs(t: &Tree, parent_even: bool, grandparent_even: bool) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let mut sum: i64 = 0;

            if grandparent_even {
                sum = sum + *v;
            }

            let current_even = *v % 2 == 0;

            sum = sum + dfs(&**l, current_even, parent_even);
            sum = sum + dfs(&**r, current_even, parent_even);

            sum
        }
    }
}

pub fn sum_even_grandparent(root: &Tree) -> i64 {
    dfs(root, false, false)
}
