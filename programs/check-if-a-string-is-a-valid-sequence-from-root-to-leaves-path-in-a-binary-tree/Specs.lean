import Aegis.IsValidSequence.Code.Funs

/-!
# Specifications of `Aegis.IsValidSequence.is_valid_sequence`

LeetCode problem `check-if-a-string-is-a-valid-sequence-from-root-to-leaves-path-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsValidSequence

  open Aegis.IsValidSequence

  def AllDigits : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => 0 ≤ v.val ∧ v.val ≤ 9 ∧ AllDigits l ∧ AllDigits r

  def ArrDigits (arr : Slice Std.I64) : Prop :=
    ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 9

  def IsLeaf (t : Tree) : Prop := ∃ v, t = Tree.Node v Tree.Null Tree.Null

  def IsChild (p c : Tree) : Prop := ∃ v l r, p = Tree.Node v l r ∧ (c = l ∨ c = r)

  def IsRootLeafPath : Tree → List Tree → Prop
    | _, [] => False
    | t, [n] => n = t ∧ IsLeaf n
    | t, n :: m :: rest => n = t ∧ IsChild n m ∧ IsRootLeafPath m (m :: rest)

  def NodeVals : List Tree → List Int
    | [] => []
    | Tree.Node v _ _ :: rest => v.val :: NodeVals rest
    | Tree.Null :: rest => NodeVals rest

  def TreeHeight : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (TreeHeight l) (TreeHeight r)

  def MinDepth : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ Tree.Null Tree.Null => 1
    | Tree.Node _ Tree.Null r => 1 + MinDepth r
    | Tree.Node _ l Tree.Null => 1 + MinDepth l
    | Tree.Node _ l r => 1 + min (MinDepth l) (MinDepth r)

  def AtMostOneChild : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => (l = Tree.Null ∨ r = Tree.Null) ∧ AtMostOneChild l ∧ AtMostOneChild r

  def AllNodesEq (v : Int) : Tree → Prop
    | Tree.Null => True
    | Tree.Node w l r => w.val = v ∧ AllNodesEq v l ∧ AllNodesEq v r

  /-- Whenever `is_valid_sequence(root, arr)` returns a result `r`, `r = true` if and only if there exists a root-to-leaf path in `root` whose sequence of node values equals `arr`. That is, there exists a sequence of nodes `n_0, n_1, ..., n_{k-1}` such that `k = len(arr)`, `n_0 = root`, `n_{k-1}` is a leaf (i.e., `n_{k-1} = Tree.Node(v, Tree.Null, Tree.Null)` for some integer `v`), for each `i` with `0 <= i < k-1`, `n_{i+1}` is a child of `n_i` (either the left or the right child), and for each `i` with `0 <= i < k`, the value of `n_i` equals `arr[i]`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_1 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root) :
      ∀ r, is_valid_sequence root arr = ok r →
        (r = true ↔
          ∃ ns : List Tree,
            IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
              NodeVals ns = arr.val.map (fun x => x.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root), ∀ r, is_valid_sequence root arr = ok r →
          (r = true ↔
            ∃ ns : List Tree,
              IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
                NodeVals ns = arr.val.map (fun x => x.val))) := by
    sorry

  /-- For every tree `root` and every slice `arr` satisfying the preconditions, `is_valid_sequence(root, arr)` returns a result (i.e., it does not fail with overflow, out-of-bounds, or panic).
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_2 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root) :
      ∃ r, is_valid_sequence root arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root), ∃ r, is_valid_sequence root arr = ok r) := by
    sorry

  /-- If `root = Tree.Null`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `root = Tree.Null`. -/
  theorem spec_3 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hroot : root = Tree.Null) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hroot : root = Tree.Null), is_valid_sequence root arr = ok false) := by
    sorry

  /-- If `root` is a single leaf node with value `v`, then `is_valid_sequence(root, arr)` returns `true` if and only if `len(arr) = 1` and `arr[0] = v`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `root = Tree.Node(v, Tree.Null, Tree.Null)` for some integer `v` with `0 <= v <= 9`. -/
  theorem spec_4 (root : Tree) (arr : Slice Std.I64) (v : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
      (hroot : root = Tree.Node v Tree.Null Tree.Null) :
      ∀ r, is_valid_sequence root arr = ok r →
        (r = true ↔ arr.val.length = 1 ∧ arr.val.map (fun x => x.val) = [v.val]) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64) (v : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
        (hroot : root = Tree.Node v Tree.Null Tree.Null), ∀ r, is_valid_sequence root arr = ok r →
          (r = true ↔ arr.val.length = 1 ∧ arr.val.map (fun x => x.val) = [v.val])) := by
    sorry

  /-- If `len(arr) = 1`, then `is_valid_sequence(root, arr)` returns `true` if and only if `root = Tree.Node(arr[0], Tree.Null, Tree.Null)`. That is, the root itself must be a leaf (no children) and its value must equal `arr[0]`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `len(arr) = 1`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_5 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hlen_one : arr.val.length = 1) (htree : AllDigits root) :
      ∀ r, is_valid_sequence root arr = ok r →
        (r = true ↔ root = Tree.Node (arr.val[0]'(by omega)) Tree.Null Tree.Null) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hlen_one : arr.val.length = 1) (htree : AllDigits root), ∀ r, is_valid_sequence root arr = ok r →
          (r = true ↔ root = Tree.Node (arr.val[0]'(by omega)) Tree.Null Tree.Null)) := by
    sorry

  /-- Let `height(root)` be defined by `height(Tree.Null) = 0` and `height(Tree.Node(_, l, r)) = 1 + max(height(l), height(r))`. If `len(arr) > height(root)`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_6 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root)
      (hgt : TreeHeight root < arr.val.length) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root)
        (hgt : TreeHeight root < arr.val.length), is_valid_sequence root arr = ok false) := by
    sorry

  /-- Let `min_depth(root)` be defined for a non-null tree as follows: if `root = Tree.Node(v, Tree.Null, Tree.Null)`, then `min_depth(root) = 1`; if exactly one child is non-null (say `Tree.Node(v, child, Tree.Null)` or `Tree.Node(v, Tree.Null, child)`), then `min_depth(root) = 1 + min_depth(child)`; if both children are non-null, then `min_depth(root) = 1 + min(min_depth(left), min_depth(right))`. If `len(arr) < min_depth(root)`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `root` is not `Tree.Null`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_7 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hne : root ≠ Tree.Null) (htree : AllDigits root)
      (hlt : arr.val.length < MinDepth root) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hne : root ≠ Tree.Null) (htree : AllDigits root)
        (hlt : arr.val.length < MinDepth root), is_valid_sequence root arr = ok false) := by
    sorry

  /-- If `arr[0] != v`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `root = Tree.Node(v, _, _)` for some integer `v` with `0 <= v <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_8 (root : Tree) (arr : Slice Std.I64) (v : Std.I64) (left right : Tree)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
      (hroot : root = Tree.Node v left right)
      (hne : (arr.val[0]'(by omega)).val ≠ v.val) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64) (v : Std.I64) (left right : Tree)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
        (hroot : root = Tree.Node v left right)
        (hne : (arr.val[0]'(by omega)).val ≠ v.val), is_valid_sequence root arr = ok false) := by
    sorry

  /-- If `is_valid_sequence(root, arr)` returns `true`, then there exists a root-to-leaf path in `root` whose sequence of node values equals `arr`. That is, there exists a sequence of nodes `n_0, n_1, ..., n_{k-1}` such that `k = len(arr)`, `n_0 = root`, `n_{k-1}` is a leaf, for each `i` with `0 <= i < k-1`, `n_{i+1}` is a child of `n_i`, and for each `i` with `0 <= i < k`, the value of `n_i` equals `arr[i]`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_9 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root)
      (hok : is_valid_sequence root arr = ok true) :
      ∃ ns : List Tree,
        IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
          NodeVals ns = arr.val.map (fun x => x.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root)
        (hok : is_valid_sequence root arr = ok true), ∃ ns : List Tree,
          IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
            NodeVals ns = arr.val.map (fun x => x.val)) := by
    sorry

  /-- Under the precondition that `root` is non-null and every node has at most one child, the tree has exactly one root-to-leaf path. Let that path's value sequence be `seq` (a list of length `k`, where `k` is the number of nodes on the path). Then `is_valid_sequence(root, arr)` returns `true` if and only if `arr` equals `seq` (i.e., `len(arr) = k` and for all `i` with `0 <= i < k`, `arr[i] = seq[i]`).
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive; `root != Tree.Null`; every node in `root` has at most one child (i.e., for every node `Tree.Node(_, l, r)`, either `l = Tree.Null` or `r = Tree.Null`). -/
  theorem spec_10 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root)
      (hne : root ≠ Tree.Null) (hone : AtMostOneChild root) :
      ∃ seq : List Int,
        (∃ ns : List Tree, IsRootLeafPath root ns ∧ NodeVals ns = seq) ∧
          (∀ ns : List Tree, IsRootLeafPath root ns → NodeVals ns = seq) ∧
            ∀ r, is_valid_sequence root arr = ok r →
              (r = true ↔ arr.val.map (fun x => x.val) = seq) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root)
        (hne : root ≠ Tree.Null) (hone : AtMostOneChild root), ∃ seq : List Int,
          (∃ ns : List Tree, IsRootLeafPath root ns ∧ NodeVals ns = seq) ∧
            (∀ ns : List Tree, IsRootLeafPath root ns → NodeVals ns = seq) ∧
              ∀ r, is_valid_sequence root arr = ok r →
                (r = true ↔ arr.val.map (fun x => x.val) = seq)) := by
    sorry

  /-- If there is no root-to-leaf path in `root` of length exactly `len(arr)`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_11 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root)
      (hnone : ¬ ∃ ns : List Tree, IsRootLeafPath root ns ∧ ns.length = arr.val.length) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root)
        (hnone : ¬ ∃ ns : List Tree, IsRootLeafPath root ns ∧ ns.length = arr.val.length), is_valid_sequence root arr = ok false) := by
    sorry

  /-- Under the precondition that all node values and all elements of `arr` are equal to the same digit `v`, `is_valid_sequence(root, arr)` returns `true` if and only if there exists a root-to-leaf path in `root` of length `len(arr)`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; there exists an integer `v` with `0 <= v <= 9` such that every node in `root` has value `v` and every element of `arr` equals `v`. -/
  theorem spec_12 (root : Tree) (arr : Slice Std.I64) (v : Int)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (hv0 : 0 ≤ v) (hv9 : v ≤ 9) (htree : AllNodesEq v root)
      (harr : ∀ (i : Nat) (h : i < arr.val.length), (arr.val[i]'h).val = v) :
      ∀ r, is_valid_sequence root arr = ok r →
        (r = true ↔ ∃ ns : List Tree, IsRootLeafPath root ns ∧ ns.length = arr.val.length) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64) (v : Int)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (hv0 : 0 ≤ v) (hv9 : v ≤ 9) (htree : AllNodesEq v root)
        (harr : ∀ (i : Nat) (h : i < arr.val.length), (arr.val[i]'h).val = v), ∀ r, is_valid_sequence root arr = ok r →
          (r = true ↔ ∃ ns : List Tree, IsRootLeafPath root ns ∧ ns.length = arr.val.length)) := by
    sorry

  /-- If `root` is a leaf and `len(arr) > 1`, then `is_valid_sequence(root, arr)` returns `false`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; `root = Tree.Node(v, Tree.Null, Tree.Null)` for some integer `v` with `0 <= v <= 9`; `len(arr) > 1`. -/
  theorem spec_13 (root : Tree) (arr : Slice Std.I64) (v : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
      (hroot : root = Tree.Node v Tree.Null Tree.Null) (hgt : 1 < arr.val.length) :
      is_valid_sequence root arr = ok false := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64) (v : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (hv0 : 0 ≤ v.val) (hv9 : v.val ≤ 9)
        (hroot : root = Tree.Node v Tree.Null Tree.Null) (hgt : 1 < arr.val.length), is_valid_sequence root arr = ok false) := by
    sorry

  /-- If there exists a root-to-leaf path in `root` whose sequence of node values equals `arr`, then `is_valid_sequence(root, arr)` returns `true`.
    Preconditions: `1 <= len(arr) <= 5000`; for all `i` with `0 <= i < len(arr)`, `0 <= arr[i] <= 9`; for every node in `root`, its value is between `0` and `9` inclusive. -/
  theorem spec_14 (root : Tree) (arr : Slice Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
      (harr : ArrDigits arr) (htree : AllDigits root)
      (hex : ∃ ns : List Tree,
        IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
          NodeVals ns = arr.val.map (fun x => x.val)) :
      is_valid_sequence root arr = ok true := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (arr : Slice Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 5000)
        (harr : ArrDigits arr) (htree : AllDigits root)
        (hex : ∃ ns : List Tree,
          IsRootLeafPath root ns ∧ ns.length = arr.val.length ∧
            NodeVals ns = arr.val.map (fun x => x.val)), is_valid_sequence root arr = ok true) := by
    sorry

  end AegisSpec.IsValidSequence
