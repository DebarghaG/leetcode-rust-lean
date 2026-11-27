fn build_bst(nums: &[i64], lo: usize, hi: usize) -> Tree {
    if lo >= hi {
        return Tree::Null;
    }

    let mid = (lo + hi - 1) / 2;
    let left = build_bst(nums, lo, mid);
    let right = build_bst(nums, mid + 1, hi);

    Tree::Node(nums[mid], Box::new(left), Box::new(right))
}

pub fn sorted_array_to_bst(nums: &[i64]) -> Tree {
    build_bst(nums, 0, nums.len())
}
