import Aegis.LongestZigZag.Code.Funs

/-!
# Specifications of `Aegis.LongestZigZag.longest_zig_zag`

LeetCode problem `longest-zigzag-path-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestZigZag

open Aegis.LongestZigZag

inductive Dir where

  | left : Dir

  | right : Dir

namespace Dir

def flip : Dir → Dir
  | left => right
  | right => left

end Dir

def childDir : Dir → Tree → Option Tree
  | Dir.left, Tree.Node _ l _ => some l
  | Dir.right, Tree.Node _ _ r => some r
  | _, Tree.Null => none

def step (d : Dir) (t : Tree) : Option Tree :=
  match childDir d t with
  | some Tree.Null => none
  | some (Tree.Node x l r) => some (Tree.Node x l r)
  | none => none

def zigzagDirs : Dir → Nat → List Dir
  | _, 0 => []
  | d, n + 1 => d :: zigzagDirs (Dir.flip d) n

def followSteps : Tree → List Dir → Option Tree
  | t, [] => some t
  | t, d :: ds =>
    match step d t with
    | some c => followSteps c ds
    | none => none

def ZigzagFrom (d : Dir) (v : Tree) (k : Nat) : Prop :=
  v ≠ Tree.Null ∧ ∃ u : Tree, followSteps v (zigzagDirs d k) = some u

def Occurs (v : Tree) : Tree → Prop
  | Tree.Null => False
  | Tree.Node x l r => v = Tree.Node x l r ∨ Occurs v l ∨ Occurs v r

def IsMaxZigzag (t : Tree) (r : Int) : Prop :=
  ∃ k : Nat, (k : Int) = r ∧ (∃ (v : Tree) (d : Dir), Occurs v t ∧ ZigzagFrom d v k) ∧
    ∀ (v : Tree) (d : Dir) (k' : Nat), Occurs v t → ZigzagFrom d v k' → k' ≤ k

def size : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + size l + size r

def nodeHeight : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (nodeHeight l) (nodeHeight r)

def height (t : Tree) : Nat := nodeHeight t - 1

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node x l r => Tree.Node x (mirror r) (mirror l)

def SameShape : Tree → Tree → Prop
  | Tree.Null, Tree.Null => True
  | Tree.Node _ l₁ r₁, Tree.Node _ l₂ r₂ => SameShape l₁ l₂ ∧ SameShape r₁ r₂
  | _, _ => False

def LeftSkewed : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => r = Tree.Null ∧ LeftSkewed l

def RightSkewed : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => l = Tree.Null ∧ RightSkewed r

def Perfect : Nat → Tree → Prop
  | 0, t => ∃ x : Std.I64, t = Tree.Node x Tree.Null Tree.Null
  | h + 1, t => ∃ (x : Std.I64) (l r : Tree), t = Tree.Node x l r ∧ Perfect h l ∧ Perfect h r

def AllValuesBetween (lo hi : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node x l r =>
    lo ≤ Std.IScalar.val x ∧ Std.IScalar.val x ≤ hi ∧
      AllValuesBetween lo hi l ∧ AllValuesBetween lo hi r

def spine : Tree → Option (List Dir)
  | Tree.Null => some []
  | Tree.Node _ l r =>
    match l, r with
    | Tree.Null, Tree.Null => some []
    | Tree.Node _ _ _, Tree.Null => (spine l).map (fun ds => Dir.left :: ds)
    | Tree.Null, Tree.Node _ _ _ => (spine r).map (fun ds => Dir.right :: ds)
    | Tree.Node _ _ _, Tree.Node _ _ _ => none

def Alternating : List Dir → Prop
  | [] => True
  | [_] => True
  | d₁ :: d₂ :: ds => d₁ ≠ d₂ ∧ Alternating (d₂ :: ds)

mutual

def Lz : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l _ =>
    match l with
    | Tree.Null => 0
    | Tree.Node _ _ _ => 1 + Rz l

def Rz : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ _ r =>
    match r with
    | Tree.Null => 0
    | Tree.Node _ _ _ => 1 + Lz r

end

inductive FilledOneNull : Tree → Tree → Prop where

  | left {x l r l'} : FilledOneNull l l' → FilledOneNull (Tree.Node x l r) (Tree.Node x l' r)

  | right {x l r r'} : FilledOneNull r r' → FilledOneNull (Tree.Node x l r) (Tree.Node x l r')

  | here_left {x r s} : s ≠ Tree.Null → FilledOneNull (Tree.Node x Tree.Null r) (Tree.Node x s r)

  | here_right {x l s} : s ≠ Tree.Null → FilledOneNull (Tree.Node x l Tree.Null) (Tree.Node x l s)

/-- Let `n` be the number of nodes in the tree. Define a zigzag path from a node `v` with initial direction `d` (where `d` is either `Left` or `Right`) as a sequence of nodes `v = v₀, v₁, …, vₖ` (for some `k ≥ 0`) such that for each `i` with `0 ≤ i < k`, `vᵢ₊₁` is the child of `vᵢ` in direction `dᵢ`, where `dᵢ = d` if `i` is even and `dᵢ` is the opposite direction if `i` is odd, and all `vᵢ` are non-`Null` nodes. The length of this path is `k`. Whenever `longest_zig_zag(root)` returns a result `r`, `r` equals the maximum length of a zigzag path in the tree, i.e., `r = max { k | there exists a node v and a direction d such that there is a zigzag path of length k starting at v with initial direction d }`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. Every node's value is an integer between 1 and 100 inclusive. -/
theorem spec_1 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000)
    (hval : AllValuesBetween 1 100 root) :
    ∀ r, longest_zig_zag root = ok r → IsMaxZigzag root r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000)
    (hval : AllValuesBetween 1 100 root), ∀ r, longest_zig_zag root = ok r → IsMaxZigzag root r.val) := by
  sorry

/-- The function `longest_zig_zag(root)` does not fail (it returns a result `r`, not an error or panic) for every input satisfying the preconditions.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. Every node's value is an integer between 1 and 100 inclusive. -/
theorem spec_2 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000)
    (hval : AllValuesBetween 1 100 root) :
    ∃ r, longest_zig_zag root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000)
    (hval : AllValuesBetween 1 100 root), ∃ r, longest_zig_zag root = ok r) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, we have `0 ≤ r ≤ n - 1`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains `n` nodes with `1 ≤ n ≤ 50000`. -/
theorem spec_3 (root : Tree) (n : Nat) (hne : root ≠ Tree.Null) (hsize : size root = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50000) :
    ∀ r, longest_zig_zag root = ok r → 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hne : root ≠ Tree.Null) (hsize : size root = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50000), ∀ r, longest_zig_zag root = ok r → 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1) := by
  sorry

/-- Let `h` be the height of the tree, defined as the maximum number of edges from the root to any leaf (so a single-node tree has `h = 0`). Whenever `longest_zig_zag(root)` returns a result `r`, we have `r ≤ h`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. -/
theorem spec_4 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000) :
    ∀ r, longest_zig_zag root = ok r → r.val ≤ (height root : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000), ∀ r, longest_zig_zag root = ok r → r.val ≤ (height root : Int)) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, we have `r = 1`.
  Preconditions: The tree rooted at `root` is a left-skewed path or a right-skewed path and contains `n ≥ 3` nodes. A left-skewed path means every node has at most one child and every existing child is a left child; a right-skewed path is analogous with right children. -/
theorem spec_5 (root : Tree) (n : Nat) (hsize : size root = n) (hn : 3 ≤ n)
    (hskew : LeftSkewed root ∨ RightSkewed root) :
    ∀ r, longest_zig_zag root = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hsize : size root = n) (hn : 3 ≤ n)
    (hskew : LeftSkewed root ∨ RightSkewed root), ∀ r, longest_zig_zag root = ok r → r.val = 1) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, we have `r = h`.
  Preconditions: The tree rooted at `root` is a perfect binary tree of height `h ≥ 1` (all leaves are at depth `h` and every internal node has two children). -/
theorem spec_6 (root : Tree) (h : Nat) (hperf : Perfect h root) (hh : 1 ≤ h) :
    ∀ r, longest_zig_zag root = ok r → r.val = (h : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (h : Nat) (hperf : Perfect h root) (hh : 1 ≤ h), ∀ r, longest_zig_zag root = ok r → r.val = (h : Int)) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, there exists a node `v` and a direction `d` (where `d` is either `Left` or `Right`) such that there is a zigzag path of length `r` starting at `v` with initial direction `d` (using the definition of zigzag path from spec_1).
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. -/
theorem spec_7 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000) :
    ∀ r, longest_zig_zag root = ok r →
      ∃ (v : Tree) (d : Dir) (k : Nat), (k : Int) = r.val ∧ Occurs v root ∧
        ZigzagFrom d v k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000), ∀ r, longest_zig_zag root = ok r →
      ∃ (v : Tree) (d : Dir) (k : Nat), (k : Int) = r.val ∧ Occurs v root ∧
        ZigzagFrom d v k) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, for every node `v` and every direction `d` (where `d` is either `Left` or `Right`), if there is a zigzag path starting at `v` with initial direction `d`, then its length is at most `r`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. -/
theorem spec_8 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000) :
    ∀ r, longest_zig_zag root = ok r →
      ∀ (v : Tree) (d : Dir) (k : Nat), Occurs v root → ZigzagFrom d v k → (k : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000), ∀ r, longest_zig_zag root = ok r →
      ∀ (v : Tree) (d : Dir) (k : Nat), Occurs v root → ZigzagFrom d v k → (k : Int) ≤ r.val) := by
  sorry

/-- Whenever `longest_zig_zag(t₁)` returns `r₁` and `longest_zig_zag(t₂)` returns `r₂`, we have `r₁ = r₂`.
  Preconditions: Let `t₁` and `t₂` be two non-empty trees with at most 50000 nodes each. They have the same shape: `t₁` is `Null` if and only if `t₂` is `Null`, and where both are `Node`, their left subtrees have the same shape and their right subtrees have the same shape. (Node values may differ.) -/
theorem spec_9 (t₁ t₂ : Tree) (hne₁ : t₁ ≠ Tree.Null) (hne₂ : t₂ ≠ Tree.Null)
    (hsize₁ : size t₁ ≤ 50000) (hsize₂ : size t₂ ≤ 50000) (hshape : SameShape t₁ t₂) :
    ∀ r₁ r₂, longest_zig_zag t₁ = ok r₁ → longest_zig_zag t₂ = ok r₂ →
      r₁.val = r₂.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (t₁ t₂ : Tree) (hne₁ : t₁ ≠ Tree.Null) (hne₂ : t₂ ≠ Tree.Null)
    (hsize₁ : size t₁ ≤ 50000) (hsize₂ : size t₂ ≤ 50000) (hshape : SameShape t₁ t₂), ∀ r₁ r₂, longest_zig_zag t₁ = ok r₁ → longest_zig_zag t₂ = ok r₂ →
      r₁.val = r₂.val) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns `r` and `longest_zig_zag(mirror(root))` returns `r'`, we have `r = r'`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. Let `mirror(root)` be the tree obtained by swapping the left and right children at every node (recursively). -/
theorem spec_10 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000) :
    ∀ r r', longest_zig_zag root = ok r → longest_zig_zag (mirror root) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000), ∀ r r', longest_zig_zag root = ok r → longest_zig_zag (mirror root) = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever `longest_zig_zag(t)` returns `r` and `longest_zig_zag(t')` returns `r'`, we have `r' ≥ r`.
  Preconditions: Let `t` be a tree satisfying the problem constraints (non-empty, at most 50000 nodes). Let `t'` be obtained from `t` by replacing exactly one occurrence of `Null` (i.e., a missing child of some node) with a non-empty subtree `s`, so that `t'` is a tree that contains `t` as a subtree and has at most 50000 nodes. -/
theorem spec_11 (t t' : Tree) (hne : t ≠ Tree.Null) (hsize : size t ≤ 50000)
    (hsize' : size t' ≤ 50000) (hfill : FilledOneNull t t') :
    ∀ r r', longest_zig_zag t = ok r → longest_zig_zag t' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (t t' : Tree) (hne : t ≠ Tree.Null) (hsize : size t ≤ 50000)
    (hsize' : size t' ≤ 50000) (hfill : FilledOneNull t t'), ∀ r r', longest_zig_zag t = ok r → longest_zig_zag t' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever `longest_zig_zag(root)` returns a result `r`, we have `r = n - 1`.
  Preconditions: The tree rooted at `root` is a single path (every node has at most one child) with alternating edge directions and contains `n ≥ 2` nodes. That is, if the path is `v₀, v₁, …, v_{n-1}` with `v₀ = root`, then for each `i` with `1 ≤ i < n-1`, the direction from `vᵢ` to `vᵢ₊₁` is opposite to the direction from `vᵢ₋₁` to `vᵢ`. -/
theorem spec_12 (root : Tree) (n : Nat) (ds : List Dir) (hn : 2 ≤ n)
    (hsize : size root = n) (hspine : spine root = some ds) (halt : Alternating ds) :
    ∀ r, longest_zig_zag root = ok r → r.val = (n : Int) - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (n : Nat) (ds : List Dir) (hn : 2 ≤ n)
    (hsize : size root = n) (hspine : spine root = some ds) (halt : Alternating ds), ∀ r, longest_zig_zag root = ok r → r.val = (n : Int) - 1) := by
  sorry

/-- For every node `v` in the tree, define `L(v)` and `R(v)` as follows: if `v` has no left child, `L(v) = 0`; otherwise `L(v) = 1 + R(left(v))`. If `v` has no right child, `R(v) = 0`; otherwise `R(v) = 1 + L(right(v))`. Whenever `longest_zig_zag(root)` returns a result `r`, we have `r = max { max(L(v), R(v)) | v is a node in the tree }`.
  Preconditions: The tree rooted at `root` is non-empty (`root ≠ Null`) and contains at most 50000 nodes. -/
theorem spec_13 (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000) :
    ∀ r, longest_zig_zag root = ok r →
      ∃ k : Nat, (k : Int) = r.val ∧
        (∃ v : Tree, Occurs v root ∧ k = max (Lz v) (Rz v)) ∧
        (∀ v : Tree, Occurs v root → max (Lz v) (Rz v) ≤ k) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree) (hne : root ≠ Tree.Null) (hsize : size root ≤ 50000), ∀ r, longest_zig_zag root = ok r →
      ∃ k : Nat, (k : Int) = r.val ∧
        (∃ v : Tree, Occurs v root ∧ k = max (Lz v) (Rz v)) ∧
        (∀ v : Tree, Occurs v root → max (Lz v) (Rz v) ≤ k)) := by
  sorry

end AegisSpec.LongestZigZag
