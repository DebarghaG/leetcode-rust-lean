const OFF: i64 = 20000;
const V_BASE: i64 = 40000;
const V2: i64 = 1600000000;
const BEST_BASE: i64 = 20000;
const BEST_MULT: i64 = 32000000000000;
const BST_MULT: i64 = 640000000000000000;

// Combine this node's value with the packed results of its two children.
// Packed layout (least significant digit first), each field in its own base:
//   min_raw  (base V_BASE,  offset by OFF)
//   max_raw  (base V_BASE,  offset by OFF)
//   size     (base BEST_BASE)
//   best     (base BEST_BASE)
//   is_bst   (0 or 1)
fn combine(val: i64, left: i64, right: i64) -> i64 {
    // Decode left subtree.
    let l_min_raw = left % V_BASE;
    let l1 = left / V_BASE;
    let l_max_raw = l1 % V_BASE;
    let l2 = l1 / V_BASE;
    let l_size = l2 % BEST_BASE;
    let l3 = l2 / BEST_BASE;
    let l_best = l3 % BEST_BASE;
    let l_bst = l3 / BEST_BASE;

    // Decode right subtree.
    let r_min_raw = right % V_BASE;
    let r1 = right / V_BASE;
    let r_max_raw = r1 % V_BASE;
    let r2 = r1 / V_BASE;
    let r_size = r2 % BEST_BASE;
    let r3 = r2 / BEST_BASE;
    let r_best = r3 % BEST_BASE;
    let r_bst = r3 / BEST_BASE;

    // Actual (offset-free) extreme values.
    let lmin = l_min_raw - OFF;
    let lmax = l_max_raw - OFF;
    let rmin = r_min_raw - OFF;
    let rmax = r_max_raw - OFF;

    let size = l_size + r_size + 1;

    // Left subtree is acceptable: empty, or (a BST and all its values < val).
    let l_less: i64 = if lmax < val { 1 } else { 0 };
    let l_bstv: i64 = if l_bst == 1 { 1 } else { 0 };
    let l_both: i64 = l_less * l_bstv;
    let l_ok: i64 = if l_size == 0 { 1 } else { l_both };

    // Right subtree is acceptable: empty, or (a BST and all its values > val).
    let r_greater: i64 = if rmin > val { 1 } else { 0 };
    let r_bstv: i64 = if r_bst == 1 { 1 } else { 0 };
    let r_both: i64 = r_greater * r_bstv;
    let r_ok: i64 = if r_size == 0 { 1 } else { r_both };

    // This whole subtree is a BST iff both children are acceptable.
    let is_bst: i64 = if l_ok == 1 { r_ok } else { 0 };

    // Best BST size found within this subtree.
    let cand: i64 = if is_bst == 1 { size } else { 0 };
    let best1: i64 = if l_best > r_best { l_best } else { r_best };
    let best: i64 = if cand > best1 { cand } else { best1 };

    // Effective extremes, ignoring empty children (which contribute val).
    let lmin_eff: i64 = if l_size == 0 { val } else { lmin };
    let lmax_eff: i64 = if l_size == 0 { val } else { lmax };
    let rmin_eff: i64 = if r_size == 0 { val } else { rmin };
    let rmax_eff: i64 = if r_size == 0 { val } else { rmax };

    let mn1: i64 = if val < lmin_eff { val } else { lmin_eff };
    let min_val: i64 = if mn1 < rmin_eff { mn1 } else { rmin_eff };
    let mx1: i64 = if val > lmax_eff { val } else { lmax_eff };
    let max_val: i64 = if mx1 > rmax_eff { mx1 } else { rmax_eff };

    let min_raw = min_val + OFF;
    let max_raw = max_val + OFF;

    min_raw + max_raw * V_BASE + size * V2 + best * BEST_MULT + is_bst * BST_MULT
}

// Null encodes as an empty BST: size 0, best 0, is_bst 1.
fn dfs(t: &Tree) -> i64 {
    match t {
        Tree::Null => BST_MULT,
        Tree::Node(v, l, r) => {
            let val = *v;
            let left = dfs(l);
            let right = dfs(r);
            combine(val, left, right)
        }
    }
}

pub fn largest_bst_subtree(root: &Tree) -> i64 {
    let packed = dfs(root);
    let shifted = packed / BEST_MULT;
    let best = shifted % BEST_BASE;
    best
}
