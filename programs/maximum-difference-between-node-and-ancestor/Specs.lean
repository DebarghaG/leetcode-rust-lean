import Aegis.MaxAncestorDiff.Code.Funs

/-!
# Specifications of `Aegis.MaxAncestorDiff.max_ancestor_diff`

LeetCode problem `maximum-difference-between-node-and-ancestor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxAncestorDiff

  open Aegis.MaxAncestorDiff

  def size : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + size l + size r

  def values : Tree → List Int
    | .Null => []
    | .Node v l r => v.val :: (values l ++ values r)

  def ValuesIn (t : Tree) (lo hi : Int) : Prop := ∀ x ∈ values t, lo ≤ x ∧ x ≤ hi

  def AllValuesEqual (t : Tree) : Prop := ∃ c, ∀ x ∈ values t, x = c

  def IsChain : Tree → Prop
    | .Null => True
    | .Node _ l r => (l = .Null ∨ r = .Null) ∧ IsChain l ∧ IsChain r

  def listMax (l : List Int) : Int := l.foldl max 0

  def listMin (l : List Int) : Int := l.foldl min 100000

  def maxVal (t : Tree) : Int := listMax (values t)

  def minVal (t : Tree) : Int := listMin (values t)

  def absDiff (a b : Int) : Int := max (a - b) (b - a)

  def ancPairsAux (acc : List Int) : Tree → List (Int × Int)
    | .Null => []
    | .Node v l r =>
      acc.map (fun a => (a, v.val))
        ++ ancPairsAux (v.val :: acc) l
        ++ ancPairsAux (v.val :: acc) r

  def ancPairs (t : Tree) : List (Int × Int) := ancPairsAux [] t

  def ancPairMax (t : Tree) : Int :=
    (ancPairs t).foldr (fun p acc => max (absDiff p.1 p.2) acc) 0

  def toI64 (x : Int) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def shift (c : Int) : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node (toI64 (v.val + c)) (shift c l) (shift c r)

  def revValues : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node (toI64 (100000 - v.val)) (revValues l) (revValues r)

  def PruneAt : Tree → Tree → Prop
    | .Null, _ => False
    | .Node v l r, t' =>
      t' = .Null
        ∨ (∃ l', PruneAt l l' ∧ t' = .Node v l' r)
        ∨ (∃ r', PruneAt r r' ∧ t' = .Node v l r')

  def AddLeafAt (w : Std.I64) : Tree → Tree → Prop
    | .Null, _ => False
    | .Node v l r, t' =>
      (l = .Null ∧ t' = .Node v (.Node w .Null .Null) r)
        ∨ (r = .Null ∧ t' = .Node v l (.Node w .Null .Null))
        ∨ (∃ l', AddLeafAt w l l' ∧ t' = .Node v l' r)
        ∨ (∃ r', AddLeafAt w r r' ∧ t' = .Node v l r')

  def rootLeafPathsAux (acc : List Int) : Tree → List (List Int)
    | .Null => []
    | .Node v .Null .Null => [acc ++ [v.val]]
    | .Node v l r =>
      rootLeafPathsAux (acc ++ [v.val]) l ++ rootLeafPathsAux (acc ++ [v.val]) r

  def rootLeafPaths (t : Tree) : List (List Int) := rootLeafPathsAux [] t

  def pathSpread (p : List Int) : Int := listMax p - listMin p

  def pathSpreadMax (t : Tree) : Int :=
    (rootLeafPaths t).foldr (fun p acc => max (pathSpread p) acc) 0

  def nodeContrib (acc : List Int) (x : Int) : Int :=
    match acc with
    | [] => 0
    | _ => max (x - listMin acc) (listMax acc - x)

  def nodeContribMaxAux (acc : List Int) : Tree → Int
    | .Null => 0
    | .Node v l r =>
      max (nodeContrib acc v.val)
        (max (nodeContribMaxAux (v.val :: acc) l) (nodeContribMaxAux (v.val :: acc) r))

  def nodeContribMax (t : Tree) : Int := nodeContribMaxAux [] t

  /-- The function returns a result r, and r equals the maximum, over all pairs of nodes (a,b) of root such that a is a proper ancestor of b, of the absolute difference |value(a) - value(b)|. Here a is a proper ancestor of b means a != b and b occurs in the left or right subtree of a, equivalently a occurs on the path from the root to b and is not b.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_1 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∃ res : Std.I64, max_ancestor_diff root = ok res ∧ res.val = ancPairMax root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∃ res : Std.I64, max_ancestor_diff root = ok res ∧ res.val = ancPairMax root) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds position.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∃ res : Std.I64, max_ancestor_diff root = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∃ res : Std.I64, max_ancestor_diff root = ok res) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= maxVal(root) - minVal(root), where maxVal(root) and minVal(root) are the maximum and minimum values among all nodes of root.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_3 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        0 ≤ res.val ∧ res.val ≤ maxVal root - minVal root := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          0 ≤ res.val ∧ res.val ≤ maxVal root - minVal root) := by
    sorry

  /-- Whenever the function returns a result r, there exist nodes a and b of root such that a is a proper ancestor of b and r = |value(a) - value(b)|.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_4 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∃ p ∈ ancPairs root, res.val = absDiff p.1 p.2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          ∃ p ∈ ancPairs root, res.val = absDiff p.1 p.2) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of nodes a and b of root such that a is a proper ancestor of b, we have |value(a) - value(b)| <= r.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_5 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∀ p ∈ ancPairs root, absDiff p.1 p.2 ≤ res.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          ∀ p ∈ ancPairs root, absDiff p.1 p.2 ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if every node of root has the same value.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_6 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        (res.val = 0 ↔ AllValuesEqual root) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          (res.val = 0 ↔ AllValuesEqual root)) := by
    sorry

  /-- Whenever the function returns a result r, r = maxVal(root) - minVal(root), where maxVal(root) and minVal(root) are the maximum and minimum values among all nodes of root.
    Preconditions: root has between 2 and 5000 nodes inclusive, every node value is in [0, 100000], and root is a chain: every node has at most one non-null child. -/
  theorem spec_7 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) (hchain : IsChain root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - minVal root := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000) (hchain : IsChain root), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = maxVal root - minVal root) := by
    sorry

  /-- Whenever the function returns a result r, r = max(|x - y|, |x - z|).
    Preconditions: root is exactly Node(x, Node(y, Null, Null), Node(z, Null, Null)) for integers x, y, z in [0, 100000]. -/
  theorem spec_8 (root : Tree) (x y z : Std.I64)
      (hroot : root = .Node x (.Node y .Null .Null) (.Node z .Null .Null))
      (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
      (hy : 0 ≤ y.val ∧ y.val ≤ 100000)
      (hz : 0 ≤ z.val ∧ z.val ≤ 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = max (absDiff x.val y.val) (absDiff x.val z.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (x y z : Std.I64)
        (hroot : root = .Node x (.Node y .Null .Null) (.Node z .Null .Null))
        (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
        (hy : 0 ≤ y.val ∧ y.val ≤ 100000)
        (hz : 0 ≤ z.val ∧ z.val ≤ 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = max (absDiff x.val y.val) (absDiff x.val z.val)) := by
    sorry

  /-- Whenever max_ancestor_diff(root) returns r and max_ancestor_diff(root_c) returns r_c, we have r_c = r.
    Preconditions: root has between 2 and 5000 nodes inclusive, every node value is in [0, 100000], c is an integer, and every node value v satisfies 0 <= v + c <= 100000. root_c is the tree obtained from root by replacing every node value v with v + c. -/
  theorem spec_9 (root : Tree) (c : Int)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hc : ∀ v ∈ values root, 0 ≤ v + c ∧ v + c ≤ 100000) :
      ∀ res res_c : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (shift c root) = ok res_c → res_c.val = res.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (c : Int)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000)
        (hc : ∀ v ∈ values root, 0 ≤ v + c ∧ v + c ≤ 100000), ∀ res res_c : Std.I64,
          max_ancestor_diff root = ok res →
            max_ancestor_diff (shift c root) = ok res_c → res_c.val = res.val) := by
    sorry

  /-- Whenever max_ancestor_diff(root) returns r and max_ancestor_diff(mirror(root)) returns r_m, we have r_m = r.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. mirror(root) is the tree with the same nodes obtained by recursively swapping the left and right child of every node. -/
  theorem spec_10 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res res_m : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (mirror root) = ok res_m → res_m.val = res.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res res_m : Std.I64,
          max_ancestor_diff root = ok res →
            max_ancestor_diff (mirror root) = ok res_m → res_m.val = res.val) := by
    sorry

  /-- Whenever max_ancestor_diff(root) returns r and max_ancestor_diff(root_rev) returns r_rev, we have r_rev = r.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. root_rev is the tree with the same shape obtained by replacing every node value v with 100000 - v. -/
  theorem spec_11 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res res_rev : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (revValues root) = ok res_rev → res_rev.val = res.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res res_rev : Std.I64,
          max_ancestor_diff root = ok res →
            max_ancestor_diff (revValues root) = ok res_rev → res_rev.val = res.val) := by
    sorry

  /-- Whenever max_ancestor_diff(root) returns r and max_ancestor_diff(root') returns r', we have r' <= r.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. root' is obtained from root by replacing one node with Null, deleting that node and all its descendants, and root' still has between 2 and 5000 nodes and all its values in [0, 100000]. -/
  theorem spec_12 (root root' : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hprune : PruneAt root root')
      (hsize'_lo : 2 ≤ size root') (hsize'_hi : size root' ≤ 5000)
      (hval' : ValuesIn root' 0 100000) :
      ∀ res res' : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root' = ok res' → res'.val ≤ res.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root' : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000)
        (hprune : PruneAt root root')
        (hsize'_lo : 2 ≤ size root') (hsize'_hi : size root' ≤ 5000)
        (hval' : ValuesIn root' 0 100000), ∀ res res' : Std.I64,
          max_ancestor_diff root = ok res →
            max_ancestor_diff root' = ok res' → res'.val ≤ res.val) := by
    sorry

  /-- Whenever max_ancestor_diff(root) returns r and max_ancestor_diff(root_plus) returns r_plus, we have r <= r_plus.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. root_plus is obtained by replacing one Null child pointer in root with a new leaf Node(w, Null, Null), where 0 <= w <= 100000, and root_plus has at most 5000 nodes. -/
  theorem spec_13 (root root_plus : Tree) (w : Std.I64)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hw : 0 ≤ w.val ∧ w.val ≤ 100000)
      (hgraft : AddLeafAt w root root_plus)
      (hsize_plus : size root_plus ≤ 5000) :
      ∀ res res_plus : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root_plus = ok res_plus → res.val ≤ res_plus.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root root_plus : Tree) (w : Std.I64)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000)
        (hw : 0 ≤ w.val ∧ w.val ≤ 100000)
        (hgraft : AddLeafAt w root root_plus)
        (hsize_plus : size root_plus ≤ 5000), ∀ res res_plus : Std.I64,
          max_ancestor_diff root = ok res →
            max_ancestor_diff root_plus = ok res_plus → res.val ≤ res_plus.val) := by
    sorry

  /-- Whenever the function returns a result r, r = maxVal(root) - x, where maxVal(root) is the maximum value among all nodes of root.
    Preconditions: root has between 2 and 5000 nodes inclusive, every node value is in [0, 100000], and the root value x is equal to minVal(root), the minimum value among all nodes of root. -/
  theorem spec_14 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = minVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - x.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (x : Std.I64) (l r : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000)
        (hroot : root = .Node x l r)
        (hx : x.val = minVal root), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = maxVal root - x.val) := by
    sorry

  /-- Whenever the function returns a result r, r = x - minVal(root), where minVal(root) is the minimum value among all nodes of root.
    Preconditions: root has between 2 and 5000 nodes inclusive, every node value is in [0, 100000], and the root value x is equal to maxVal(root), the maximum value among all nodes of root. -/
  theorem spec_15 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = maxVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = x.val - minVal root := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (root : Tree) (x : Std.I64) (l r : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000)
        (hroot : root = .Node x l r)
        (hx : x.val = maxVal root), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = x.val - minVal root) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum, over all root-to-leaf paths P of root, of maxVal(P) - minVal(P), where maxVal(P) and minVal(P) are the maximum and minimum node values on the path P.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_16 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = pathSpreadMax root := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = pathSpreadMax root) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum, over all nodes b of root, of max(value(b) - minAncestor(b), maxAncestor(b) - value(b)), where minAncestor(b) and maxAncestor(b) are respectively the minimum and maximum values among the proper ancestors of b; for the root, whose set of proper ancestors is empty, the contribution is 0.
    Preconditions: root has between 2 and 5000 nodes inclusive, and every node value is an integer in [0, 100000]. -/
  theorem spec_17 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
        (hval : ValuesIn root 0 100000), ∀ res : Std.I64, max_ancestor_diff root = ok res →
          res.val = nodeContribMax root) := by
    sorry

  end AegisSpec.MaxAncestorDiff
