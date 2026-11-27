fn find_max_index(nums: &[i64], lo: usize, hi: usize) -> usize {
    let mut best = lo;
    let mut i = lo + 1;
    while i < hi {
        if nums[i] > nums[best] {
            best = i;
        }
        i += 1;
    }
    best
}

fn build(nums: &[i64], lo: usize, hi: usize) -> Tree {
    if lo >= hi {
        return Tree::Null;
    }
    let mid = find_max_index(nums, lo, hi);
    let left = build(nums, lo, mid);
    let right = build(nums, mid + 1, hi);
    Tree::Node(nums[mid], Box::new(left), Box::new(right))
}

pub fn construct_maximum_binary_tree(nums: &[i64]) -> Tree {
    build(nums, 0, nums.len())
}
