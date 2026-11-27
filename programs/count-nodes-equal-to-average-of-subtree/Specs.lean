import Aegis.AverageOfSubtree.Code.Funs

/-!
# Specifications of `Aegis.AverageOfSubtree.average_of_subtree`

LeetCode problem `count-nodes-equal-to-average-of-subtree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AverageOfSubtree

open Aegis.AverageOfSubtree

def treeSum : Tree → Int
  | Tree.Null => 0
  | Tree.Node v l r => v.val + treeSum l + treeSum r

def treeSize : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + treeSize l + treeSize r

def treeLeaves : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ Tree.Null Tree.Null => 1
  | Tree.Node _ l r => treeLeaves l + treeLeaves r

def treeAvg (t : Tree) : Int := Int.ediv (treeSum t) (treeSize t : Int)

def treeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node v l r =>
    (if v.val = treeAvg (Tree.Node v l r) then 1 else 0) + treeCount l + treeCount r

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

def valuesInRange (lo hi : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => lo ≤ v.val ∧ v.val ≤ hi ∧ valuesInRange lo hi l ∧ valuesInRange lo hi r

def allValuesEq (c : Int) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => v.val = c ∧ allValuesEq c l ∧ allValuesEq c r

def AllNodesAverage : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    (v.val = treeAvg (Tree.Node v l r) ∧ AllNodesAverage l ∧ AllNodesAverage r)

def InternalNodesNotAverage : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    ((l ≠ Tree.Null ∨ r ≠ Tree.Null) → v.val ≠ treeAvg (Tree.Node v l r)) ∧
      InternalNodesNotAverage l ∧ InternalNodesNotAverage r

def shiftValues (d : Int) : Tree → Tree → Prop
  | Tree.Null, Tree.Null => True
  | Tree.Node v l r, Tree.Node v' l' r' =>
    v'.val = v.val + d ∧ shiftValues d l l' ∧ shiftValues d r r'
  | _, _ => False

def IsChain3 (v w u : Std.I64) : Tree → Prop
  | Tree.Node v₁ (Tree.Node w₁ (Tree.Node u₁ Tree.Null Tree.Null) Tree.Null) Tree.Null =>
    v₁ = v ∧ w₁ = w ∧ u₁ = u
  | Tree.Node v₁ (Tree.Node w₁ Tree.Null (Tree.Node u₁ Tree.Null Tree.Null)) Tree.Null =>
    v₁ = v ∧ w₁ = w ∧ u₁ = u
  | Tree.Node v₁ Tree.Null (Tree.Node w₁ (Tree.Node u₁ Tree.Null Tree.Null) Tree.Null) =>
    v₁ = v ∧ w₁ = w ∧ u₁ = u
  | Tree.Node v₁ Tree.Null (Tree.Node w₁ Tree.Null (Tree.Node u₁ Tree.Null Tree.Null)) =>
    v₁ = v ∧ w₁ = w ∧ u₁ = u
  | _ => False

/-- The function returns a result res and res = count(root), where size(Null)=0, size(Node v l r)=1+size(l)+size(r), sum(Null)=0, sum(Node v l r)=v+sum(l)+sum(r), and count(Null)=0, count(Node v l r) = [v = floor((v+sum(l)+sum(r))/(1+size(l)+size(r)))] + count(l) + count(r), with [P]=1 if P holds and 0 otherwise. Equivalently, res is the number of nodes n of root such that val(n) = floor(sum(s_n)/size(s_n)), where s_n is the subtree rooted at n.
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_1 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64, average_of_subtree root = ok res ∧ res.val = (treeCount root : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64, average_of_subtree root = ok res ∧ res.val = (treeCount root : Int)) := by
  sorry

/-- The function returns a result res; it does not fail, panic, or overflow on any root satisfying the preconditions.
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_2 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64, average_of_subtree root = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64, average_of_subtree root = ok res) := by
  sorry

/-- The function returns a result res and 0 <= res <= size(root).
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_3 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64,
      average_of_subtree root = ok res ∧ 0 ≤ res.val ∧ res.val ≤ (treeSize root : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64,
      average_of_subtree root = ok res ∧ 0 ≤ res.val ∧ res.val ≤ (treeSize root : Int)) := by
  sorry

/-- The function returns a result res and res >= leaves(root), where leaves(Null)=0, leaves(Node v Null Null)=1, and leaves(Node v l r)=leaves(l)+leaves(r) when at least one of l, r is non-Null.
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_4 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64, average_of_subtree root = ok res ∧ (treeLeaves root : Int) ≤ res.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64, average_of_subtree root = ok res ∧ (treeLeaves root : Int) ≤ res.val) := by
  sorry

/-- The function returns a result res and res = size(root).
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, every node value is an integer in [0,1000], and there is an integer c with 0 <= c <= 1000 such that every node of root has value c. -/
theorem spec_5 (root : Tree) (c : Int)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root)
    (hc : 0 ≤ c ∧ c ≤ 1000)
    (hconst : allValuesEq c root) :
    ∃ res : Std.I64, average_of_subtree root = ok res ∧ res.val = (treeSize root : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (c : Int)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root)
    (hc : 0 ≤ c ∧ c ≤ 1000)
    (hconst : allValuesEq c root), ∃ res : Std.I64, average_of_subtree root = ok res ∧ res.val = (treeSize root : Int)) := by
  sorry

/-- The function returns a result res on root. Let m = mirror(root), where mirror(Null)=Null and mirror(Node v l r)=Node v (mirror r) (mirror l). Then the function returns the same result res on m; i.e., average_of_subtree(root) = average_of_subtree(m).
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_6 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64,
      average_of_subtree root = ok res ∧ average_of_subtree (mirror root) = ok res := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64,
      average_of_subtree root = ok res ∧ average_of_subtree (mirror root) = ok res) := by
  sorry

/-- The function returns a result res, and res = size(root) if and only if for every node n of root, val(n) = floor(sum(s_n)/size(s_n)), where s_n is the subtree rooted at n and sum(Null)=0, sum(Node v l r)=v+sum(l)+sum(r).
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_7 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        (res.val = (treeSize root : Int) ↔ AllNodesAverage root) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        (res.val = (treeSize root : Int) ↔ AllNodesAverage root)) := by
  sorry

/-- The function returns a result res, and res = leaves(root) if and only if every internal node n of root (a node with at least one non-Null child) satisfies val(n) != floor(sum(s_n)/size(s_n)), where leaves(Null)=0, leaves(Node v Null Null)=1, and leaves(Node v l r)=leaves(l)+leaves(r) when at least one of l, r is non-Null, and s_n is the subtree rooted at n.
  Preconditions: root is a binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node v l r)=1+size(l)+size(r); every node value is an integer in [0,1000]. -/
theorem spec_8 (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root) :
    ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        (res.val = (treeLeaves root : Int) ↔ InternalNodesNotAverage root) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root), ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        (res.val = (treeLeaves root : Int) ↔ InternalNodesNotAverage root)) := by
  sorry

/-- The function returns a result res on root and a result res' on root', and res = res'.
  Preconditions: root and root' are binary trees with 1 <= size <= 1000 and every node value in [0,1000], and there is an integer d such that root' is obtained from root by replacing every node value v with v+d (so every value of root' is also in [0,1000]). -/
theorem spec_9 (root root' : Tree) (d : Int)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root)
    (hsize' : 1 ≤ treeSize root' ∧ treeSize root' ≤ 1000)
    (hval' : valuesInRange 0 1000 root')
    (hshift : shiftValues d root root') :
    ∃ res res' : Std.I64,
      average_of_subtree root = ok res ∧ average_of_subtree root' = ok res' ∧ res = res' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root root' : Tree) (d : Int)
    (hsize : 1 ≤ treeSize root ∧ treeSize root ≤ 1000)
    (hval : valuesInRange 0 1000 root)
    (hsize' : 1 ≤ treeSize root' ∧ treeSize root' ≤ 1000)
    (hval' : valuesInRange 0 1000 root')
    (hshift : shiftValues d root root'), ∃ res res' : Std.I64,
      average_of_subtree root = ok res ∧ average_of_subtree root' = ok res' ∧ res = res') := by
  sorry

/-- The function returns a result res and res = 1 + [v <= w <= v+1], where [P]=1 if P holds and 0 otherwise; explicitly, res = 2 when w is v or v+1, and res = 1 otherwise.
  Preconditions: root = Node v (Node w Null Null) Null or root = Node v Null (Node w Null Null), with 0 <= v <= 1000 and 0 <= w <= 1000. -/
theorem spec_10 (v w : Std.I64)
    (hv : 0 ≤ v.val ∧ v.val ≤ 1000)
    (hw : 0 ≤ w.val ∧ w.val ≤ 1000) :
    (∃ res : Std.I64,
        average_of_subtree (Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null) = ok res ∧
          res.val = 1 + (if v.val ≤ w.val ∧ w.val ≤ v.val + 1 then (1 : Int) else 0)) ∧
      (∃ res : Std.I64,
        average_of_subtree (Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null)) = ok res ∧
          res.val = 1 + (if v.val ≤ w.val ∧ w.val ≤ v.val + 1 then (1 : Int) else 0)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (v w : Std.I64)
    (hv : 0 ≤ v.val ∧ v.val ≤ 1000)
    (hw : 0 ≤ w.val ∧ w.val ≤ 1000), (∃ res : Std.I64,
        average_of_subtree (Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null) = ok res ∧
          res.val = 1 + (if v.val ≤ w.val ∧ w.val ≤ v.val + 1 then (1 : Int) else 0)) ∧
      (∃ res : Std.I64,
        average_of_subtree (Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null)) = ok res ∧
          res.val = 1 + (if v.val ≤ w.val ∧ w.val ≤ v.val + 1 then (1 : Int) else 0))) := by
  sorry

/-- The function returns a result res and res = 1 + [w <= u <= w+1] + [2v <= w+u <= 2v+2], where [P]=1 if P holds and 0 otherwise.
  Preconditions: root is a chain of exactly three nodes with values v (the root), w (the only child of the root), and u (the only child of w), where each non-root node is the unique child (left or right) of its parent, and 0 <= v,w,u <= 1000. -/
theorem spec_11 (v w u : Std.I64) (root : Tree)
    (hv : 0 ≤ v.val ∧ v.val ≤ 1000)
    (hw : 0 ≤ w.val ∧ w.val ≤ 1000)
    (hu : 0 ≤ u.val ∧ u.val ≤ 1000)
    (hchain : IsChain3 v w u root) :
    ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        res.val = 1 + (if w.val ≤ u.val ∧ u.val ≤ w.val + 1 then (1 : Int) else 0) +
            (if 2 * v.val ≤ w.val + u.val ∧ w.val + u.val ≤ 2 * v.val + 2 then (1 : Int) else 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (v w u : Std.I64) (root : Tree)
    (hv : 0 ≤ v.val ∧ v.val ≤ 1000)
    (hw : 0 ≤ w.val ∧ w.val ≤ 1000)
    (hu : 0 ≤ u.val ∧ u.val ≤ 1000)
    (hchain : IsChain3 v w u root), ∃ res : Std.I64,
      average_of_subtree root = ok res ∧
        res.val = 1 + (if w.val ≤ u.val ∧ u.val ≤ w.val + 1 then (1 : Int) else 0) +
            (if 2 * v.val ≤ w.val + u.val ∧ w.val + u.val ≤ 2 * v.val + 2 then (1 : Int) else 0)) := by
  sorry

end AegisSpec.AverageOfSubtree
