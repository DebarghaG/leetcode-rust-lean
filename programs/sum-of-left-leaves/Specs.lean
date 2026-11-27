import Aegis.SumOfLeftLeaves.Code.Funs

/-!
# Specifications of `Aegis.SumOfLeftLeaves.sum_of_left_leaves`

LeetCode problem `sum-of-left-leaves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfLeftLeaves

  open Aegis.SumOfLeftLeaves

  def vals : Tree → List ℤ
    | .Null => []
    | .Node a l r => a.val :: (vals l ++ vals r)

  def nodeCount (t : Tree) : ℕ := (vals t).length

  def totalSum (t : Tree) : ℤ := (vals t).sum

  def valuesInBounds (t : Tree) : Prop := ∀ x ∈ vals t, -1000 ≤ x ∧ x ≤ 1000

  def leafVal : Tree → ℤ
    | .Node a .Null .Null => a.val
    | _ => 0

  def leftLeafVals : Tree → List ℤ
    | .Null => []
    | .Node _ l r =>
        leftLeafVals l ++ leftLeafVals r ++
          (match l with
            | .Node a .Null .Null => [a.val]
            | _ => [])

  def leftLeafSum (t : Tree) : ℤ := (leftLeafVals t).sum

  def leftLeafCount (t : Tree) : ℕ := (leftLeafVals t).length

  def rightLeafVals : Tree → List ℤ
    | .Null => []
    | .Node _ l r =>
        rightLeafVals l ++ rightLeafVals r ++
          (match r with
            | .Node a .Null .Null => [a.val]
            | _ => [])

  def rightLeafSum (t : Tree) : ℤ := (rightLeafVals t).sum

  def sameShape : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node _ l r, .Node _ l' r' => sameShape l l' ∧ sameShape r r'
    | _, _ => False

  def leftLeafValuesAgree : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node _ l r, .Node _ l' r' =>
        (match l, l' with
          | .Node a .Null .Null, .Node a' _ _ => a.val = a'.val
          | _, _ => True) ∧
          leftLeafValuesAgree l l' ∧
          leftLeafValuesAgree r r'
    | _, _ => False

  def IsNegationOf : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node a l r, .Node a' l' r' => a'.val = -a.val ∧ IsNegationOf l l' ∧ IsNegationOf r r'
    | _, _ => False

  def IsMirrorOf : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node a l r, .Node a' l' r' => a'.val = a.val ∧ IsMirrorOf l r' ∧ IsMirrorOf r l'
    | _, _ => False

  def IsShiftBy (c : ℤ) : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node a l r, .Node a' l' r' => a'.val = a.val + c ∧ IsShiftBy c l l' ∧ IsShiftBy c r r'
    | _, _ => False

  /-- The function returns a result r. Define S(root) as the sum of the values of all node occurrences x in root such that x is the left child of some node occurrence y in root and x has no children, i.e. x = Node(a, Null, Null) for some integer a. Each such occurrence is counted exactly once, and S(root) = 0 if there are no such occurrences. Then the returned value satisfies r = S(root).
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, and every node value lies in the closed interval [-1000, 1000]. -/
  theorem spec_1 (root : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root) :
      ∃ r, sum_of_left_leaves root = ok r ∧ r.val = leftLeafSum root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root), ∃ r, sum_of_left_leaves root = ok r ∧ r.val = leftLeafSum root) := by
    sorry

  /-- The function returns a result r; it does not fail. In particular, for this execution there is no arithmetic overflow, no panic, and no out-of-bounds access.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, and every node value lies in [-1000, 1000]. -/
  theorem spec_2 (root : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root) :
      ∃ r, sum_of_left_leaves root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root), ∃ r, sum_of_left_leaves root = ok r) := by
    sorry

  /-- Let n be the number of node occurrences in root. The function returns a result r satisfying -1000 * n <= r <= 1000 * n.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, and every node value lies in [-1000, 1000]. -/
  theorem spec_3 (root : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root) :
      ∃ r, sum_of_left_leaves root = ok r ∧
        -1000 * (nodeCount root : ℤ) ≤ r.val ∧ r.val ≤ 1000 * (nodeCount root : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root), ∃ r, sum_of_left_leaves root = ok r ∧
          -1000 * (nodeCount root : ℤ) ≤ r.val ∧ r.val ≤ 1000 * (nodeCount root : ℤ)) := by
    sorry

  /-- Let T be the sum of all node values in root. The function returns a result r satisfying 0 <= r <= T.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, every node value lies in [-1000, 1000], and every node value is non-negative. -/
  theorem spec_4 (root : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root)
      (hnn : ∀ x ∈ vals root, 0 ≤ x) :
      ∃ r, sum_of_left_leaves root = ok r ∧ 0 ≤ r.val ∧ r.val ≤ totalSum root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root)
        (hnn : ∀ x ∈ vals root, 0 ≤ x), ∃ r, sum_of_left_leaves root = ok r ∧ 0 ≤ r.val ∧ r.val ≤ totalSum root) := by
    sorry

  /-- Let S(T) denote the sum of values of all left leaves of T, defined as in spec_1 with S(Null) = 0. If L is a leaf, write L = Node(a, Null, Null); set c = a in that case, and set c = 0 otherwise. The function returns a result r satisfying r = S(L) + S(R) + c.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, every node value lies in [-1000, 1000], and root = Node(v, L, R) for some integer v and subtrees L and R. -/
  theorem spec_5 (root : Tree) (v : Aeneas.Std.I64) (L R : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root)
      (hroot : root = Tree.Node v L R) :
      ∃ r, sum_of_left_leaves root = ok r ∧
        r.val = leftLeafSum L + leftLeafSum R + leafVal L := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (v : Aeneas.Std.I64) (L R : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root)
        (hroot : root = Tree.Node v L R), ∃ r, sum_of_left_leaves root = ok r ∧
          r.val = leftLeafSum L + leftLeafSum R + leafVal L) := by
    sorry

  /-- If r is the result returned on root and r2 is the result returned on root2, then r = r2.
    Preconditions: root and root2 are Trees, each with between 1 and 1000 node occurrences inclusive, every node value in either tree lies in [-1000, 1000], root2 has exactly the same shape as root, and for every node occurrence that is a left leaf in root, the corresponding occurrence in root2 has the same value; values at all other positions may differ arbitrarily within [-1000, 1000]. -/
  theorem spec_6 (root root2 : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hn2 : 1 ≤ nodeCount root2 ∧ nodeCount root2 ≤ 1000)
      (hv : valuesInBounds root)
      (hv2 : valuesInBounds root2)
      (hs : sameShape root root2)
      (hl : leftLeafValuesAgree root root2) :
      ∀ r r2, sum_of_left_leaves root = ok r → sum_of_left_leaves root2 = ok r2 →
        r.val = r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root root2 : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hn2 : 1 ≤ nodeCount root2 ∧ nodeCount root2 ≤ 1000)
        (hv : valuesInBounds root)
        (hv2 : valuesInBounds root2)
        (hs : sameShape root root2)
        (hl : leftLeafValuesAgree root root2), ∀ r r2, sum_of_left_leaves root = ok r → sum_of_left_leaves root2 = ok r2 →
          r.val = r2.val) := by
    sorry

  /-- If r is the result returned on root and r_neg is the result returned on root_neg, then r_neg = -r.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, every node value lies in [-1000, 1000], and root_neg is obtained from root by replacing every node value x with -x. -/
  theorem spec_7 (root root_neg : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root)
      (hneg : IsNegationOf root root_neg) :
      ∀ r r_neg, sum_of_left_leaves root = ok r → sum_of_left_leaves root_neg = ok r_neg →
        r_neg.val = -r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root root_neg : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root)
        (hneg : IsNegationOf root root_neg), ∀ r r_neg, sum_of_left_leaves root = ok r → sum_of_left_leaves root_neg = ok r_neg →
          r_neg.val = -r.val) := by
    sorry

  /-- Let Q be the sum of the values of all node occurrences x in root_mir such that x is the right child of some node occurrence y in root_mir and x has no children; if there are none, Q = 0. The function returns a result r satisfying r = Q.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, every node value lies in [-1000, 1000], and root_mir is obtained from root by recursively swapping the left and right children of every node while keeping all values unchanged. -/
  theorem spec_8 (root root_mir : Tree)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root)
      (hmir : IsMirrorOf root root_mir) :
      ∃ r, sum_of_left_leaves root = ok r ∧ r.val = rightLeafSum root_mir := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root root_mir : Tree)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root)
        (hmir : IsMirrorOf root root_mir), ∃ r, sum_of_left_leaves root = ok r ∧ r.val = rightLeafSum root_mir) := by
    sorry

  /-- Let m be the number of left-leaf node occurrences in root. If r is the result returned on root and r_shift is the result returned on root_shift, then r_shift = r + c * m.
    Preconditions: root is a Tree with between 1 and 1000 node occurrences inclusive, every node value lies in [-1000, 1000], c is an integer such that x + c is in [-1000, 1000] for every node value x in root, and root_shift is obtained from root by replacing every node value x with x + c. -/
  theorem spec_9 (root root_shift : Tree) (c : ℤ)
      (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
      (hv : valuesInBounds root)
      (hc : ∀ x ∈ vals root, -1000 ≤ x + c ∧ x + c ≤ 1000)
      (hshift : IsShiftBy c root root_shift) :
      ∀ r r_shift, sum_of_left_leaves root = ok r → sum_of_left_leaves root_shift = ok r_shift →
        r_shift.val = r.val + c * (leftLeafCount root : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root root_shift : Tree) (c : ℤ)
        (hn : 1 ≤ nodeCount root ∧ nodeCount root ≤ 1000)
        (hv : valuesInBounds root)
        (hc : ∀ x ∈ vals root, -1000 ≤ x + c ∧ x + c ≤ 1000)
        (hshift : IsShiftBy c root root_shift), ∀ r r_shift, sum_of_left_leaves root = ok r → sum_of_left_leaves root_shift = ok r_shift →
          r_shift.val = r.val + c * (leftLeafCount root : ℤ)) := by
    sorry

  end AegisSpec.SumOfLeftLeaves
