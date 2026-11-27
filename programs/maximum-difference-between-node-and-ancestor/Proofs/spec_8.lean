import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_8` (maximum-difference-between-node-and-ancestor).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxAncestorDiff

  /-!
  # Specifications of `Aegis.MaxAncestorDiff.max_ancestor_diff`

  `max_ancestor_diff : Tree → Result Std.I64` where
  `inductive Tree | Null | Node : Std.I64 → Tree → Tree → Tree`.

  The Rust program computes, for the tree `root = Node v l r`, the maximum of
  `dfs l v v` and `dfs r v r`, where `dfs t mn mx` carries the running minimum/maximum
  of the values on the path from `root` to `t` (inclusive) and returns
  `mx - mn` at a `Null` child, taking the maximum over all `Null` children
  (i.e. over all root-to-`Null` path extensions).

  ## How nodes are represented

  In this file a *node* of a tree `t` is represented by the subtree occurring at that node
  (the tree constructors are structural, so two nodes with the same content are not
  distinguished; this is harmless because every specification below only depends on node
  *values* and on the ancestor relation, both of which are invariant under this quotient).
  Lists of node values are built with the helper `values`.
  -/

  open Aegis.MaxAncestorDiff

  /-! ### Basic notions on trees -/

  /-- Number of nodes of a tree. -/
  def size : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + size l + size r

  /-- The list of node values of a tree (pre-order); it records every node value exactly once. -/
  def values : Tree → List Int
    | .Null => []
    | .Node v l r => v.val :: (values l ++ values r)

  /-- Every node value of `t` lies in the closed interval `[lo, hi]`. -/
  def ValuesIn (t : Tree) (lo hi : Int) : Prop := ∀ x ∈ values t, lo ≤ x ∧ x ≤ hi

  /-- All nodes of a tree have the same value. -/
  def AllValuesEqual (t : Tree) : Prop := ∃ c, ∀ x ∈ values t, x = c

  /-- `t` is a chain: every node has at most one non-null child. -/
  def IsChain : Tree → Prop
    | .Null => True
    | .Node _ l r => (l = .Null ∨ r = .Null) ∧ IsChain l ∧ IsChain r

  /-! ### Extrema of the node values of a tree -/

  /-- Maximum of a list of integers (`0` for the empty list). -/
  def listMax (l : List Int) : Int := l.foldl max 0

  /-- Minimum of a list of integers (`100000` for the empty list). -/
  def listMin (l : List Int) : Int := l.foldl min 100000

  /-- `maxVal(root)`: the maximum value of the nodes of `root`.
  Whenever all node values lie in `[0, 100000]` (the hypothesis of every specification below)
  and the tree is nonempty, this is exactly the maximum of the node values. -/
  def maxVal (t : Tree) : Int := listMax (values t)

  /-- `minVal(root)`: the minimum value of the nodes of `root`.
  Whenever all node values lie in `[0, 100000]` (the hypothesis of every specification below)
  and the tree is nonempty, this is exactly the minimum of the node values. -/
  def minVal (t : Tree) : Int := listMin (values t)

  /-! ### Proper ancestor pairs -/

  /-- `|a - b|`, as an integer. -/
  def absDiff (a b : Int) : Int := max (a - b) (b - a)

  /-- Auxiliary definition for `ancPairs`, carrying the values of the proper ancestors of the
  current node (`acc`, ordered from the nearest ancestor upwards). -/
  def ancPairsAux (acc : List Int) : Tree → List (Int × Int)
    | .Null => []
    | .Node v l r =>
      acc.map (fun a => (a, v.val))
        ++ ancPairsAux (v.val :: acc) l
        ++ ancPairsAux (v.val :: acc) r

  /-- The list of all pairs `(value a, value b)` such that the node with value `a` is a *proper
  ancestor* of the node with value `b`: `a ≠ b` and `b` occurs in the left or right subtree of
  `a` (equivalently, `a` occurs on the path from the root to `b` and is not `b`). -/
  def ancPairs (t : Tree) : List (Int × Int) := ancPairsAux [] t

  /-- The maximum, over all pairs of nodes `(a, b)` of `t` with `a` a proper ancestor of `b`,
  of `|value a - value b|`.

  For the empty tree (or a single node) the list of pairs is empty and the value is `0`; all
  specifications below assume a root with at least two nodes, where the list is nonempty. -/
  def ancPairMax (t : Tree) : Int :=
    (ancPairs t).foldr (fun p acc => max (absDiff p.1 p.2) acc) 0

  /-! ### Tree transformations used by the invariance/deduction specifications -/

  /-- Build an `I64` from an integer, truncating to 64 bits. -/
  def toI64 (x : Int) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

  /-- `mirror(root)`: swap the left and right child of every node. -/
  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  /-- `root_c`: add `c` to every node value.
  (When every shifted value satisfies `0 ≤ v + c ≤ 100000` — the hypothesis of `spec_S9` — this
  really is the tree obtained by replacing every node value `v` with `v + c`.) -/
  def shift (c : Int) : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node (toI64 (v.val + c)) (shift c l) (shift c r)

  /-- `root_rev`: replace every node value `v` with `100000 - v`
  (under the hypothesis `0 ≤ v ≤ 100000` this is again an in-range node value). -/
  def revValues : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node (toI64 (100000 - v.val)) (revValues l) (revValues r)

  /-- `PruneAt t t'`: `t'` is obtained from `t` by replacing one node with `Null`, thereby
  deleting that node and all its descendants.  Exactly one node is removed: the disjunct
  `t' = .Null` deletes the root of `t`, and the other two disjuncts delete a single node of the
  left, resp. right, subtree.  (`PruneAt .Null _` is `False`: there is no node to delete.) -/
  def PruneAt : Tree → Tree → Prop
    | .Null, _ => False
    | .Node v l r, t' =>
      t' = .Null
        ∨ (∃ l', PruneAt l l' ∧ t' = .Node v l' r)
        ∨ (∃ r', PruneAt r r' ∧ t' = .Node v l r')

  /-- `AddLeafAt w t t'`: `t'` is obtained from `t` by replacing one null child pointer of `t`
  with the new leaf `Node w .Null .Null`. -/
  def AddLeafAt (w : Std.I64) : Tree → Tree → Prop
    | .Null, _ => False
    | .Node v l r, t' =>
      (l = .Null ∧ t' = .Node v (.Node w .Null .Null) r)
        ∨ (r = .Null ∧ t' = .Node v l (.Node w .Null .Null))
        ∨ (∃ l', AddLeafAt w l l' ∧ t' = .Node v l' r)
        ∨ (∃ r', AddLeafAt w r r' ∧ t' = .Node v l r')

  /-! ### Root-to-leaf paths -/

  /-- Auxiliary definition for `rootLeafPaths`, carrying the values on the path from the root to
  the current node (the current node excluded). -/
  def rootLeafPathsAux (acc : List Int) : Tree → List (List Int)
    | .Null => []
    | .Node v .Null .Null => [acc ++ [v.val]]
    | .Node v l r =>
      rootLeafPathsAux (acc ++ [v.val]) l ++ rootLeafPathsAux (acc ++ [v.val]) r

  /-- All root-to-leaf paths of a tree, each given as the list of the node values on it
  (a leaf is a node with two null children). -/
  def rootLeafPaths (t : Tree) : List (List Int) := rootLeafPathsAux [] t

  /-- `maxVal(P) - minVal(P)` for a path `P` given as a list of node values. -/
  def pathSpread (p : List Int) : Int := listMax p - listMin p

  /-- The maximum, over all root-to-leaf paths `P` of `t`, of `maxVal(P) - minVal(P)`. -/
  def pathSpreadMax (t : Tree) : Int :=
    (rootLeafPaths t).foldr (fun p acc => max (pathSpread p) acc) 0

  /-! ### Per-node characterization -/

  /-- Contribution of a node with value `x` whose list of proper ancestor values is `acc`:
  `max(x - min(acc), max(acc) - x)`, and `0` when `acc` is empty (the root case). -/
  def nodeContrib (acc : List Int) (x : Int) : Int :=
    match acc with
    | [] => 0
    | _ => max (x - listMin acc) (listMax acc - x)

  /-- Auxiliary definition for `nodeContribMax`, carrying the values of the proper ancestors of
  the current node. -/
  def nodeContribMaxAux (acc : List Int) : Tree → Int
    | .Null => 0
    | .Node v l r =>
      max (nodeContrib acc v.val)
        (max (nodeContribMaxAux (v.val :: acc) l) (nodeContribMaxAux (v.val :: acc) r))

  /-- The maximum, over all nodes `b` of `t`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))`, where `minAncestor(b)` and
  `maxAncestor(b)` are the minimum and maximum values of the proper ancestors of `b`; the
  contribution of the root (which has no proper ancestor) is `0`. -/
  def nodeContribMax (t : Tree) : Int := nodeContribMaxAux [] t

  /-! ## Specifications -/

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry

  /-** spec_S1 (MAIN) [functional]: the result is the maximum, over all pairs of nodes `(a, b)` of
  `root` such that `a` is a proper ancestor of `b`, of `|value a - value b|`. -/
  theorem spec_S1 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∃ res : Std.I64, max_ancestor_diff root = ok res ∧ res.val = ancPairMax root := by
    sorry

  /-** spec_S2 [no_failure]: the function returns a result; it does not fail, overflow, panic,
  or access an out-of-bounds position. -/
  theorem spec_S2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∃ res : Std.I64, max_ancestor_diff root = ok res := by
    sorry

  /-** spec_S3 [bounds]: every returned value lies in `[0, maxVal(root) - minVal(root)]`. -/
  theorem spec_S3 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        0 ≤ res.val ∧ res.val ≤ maxVal root - minVal root := by
    sorry

  /-** spec_S4 [witness]: the returned value is attained by a pair of nodes `(a, b)` of `root`
  with `a` a proper ancestor of `b`. -/
  theorem spec_S4 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∃ p ∈ ancPairs root, res.val = absDiff p.1 p.2 := by
    sorry

  /-** spec_S5 [relational]: the returned value dominates `|value a - value b|` for every pair of
  nodes `(a, b)` of `root` with `a` a proper ancestor of `b`. -/
  theorem spec_S5 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∀ p ∈ ancPairs root, absDiff p.1 p.2 ≤ res.val := by
    sorry

  /-** spec_S6 [edge]: the result is `0` if and only if every node of `root` has the same value. -/
  theorem spec_S6 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        (res.val = 0 ↔ AllValuesEqual root) := by
    sorry

  /-** spec_S7 [shape]: on a chain, the result is `maxVal(root) - minVal(root)`. -/
  theorem spec_S7 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) (hchain : IsChain root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - minVal root := by
    sorry

  /-! ### Auxiliary lemmas for `spec_S8` -/

  /-- If the true difference `a.val - b.val` fits in 64 bits, then the subtraction succeeds and
  returns exactly that difference. -/
  lemma I64_sub_ok {a b : Std.I64} (h : IScalar.inBounds .I64 (a.val - b.val)) :
      ∃ c : Std.I64, a - b = ok c ∧ c.val = a.val - b.val := by
    have hm := IScalar.tryMk_eq (ty := .I64) (a.val - b.val)
    cases h' : (IScalar.tryMk .I64 (a.val - b.val)).match with
    | ok y =>
      have hsub : IScalar.tryMk .I64 (a.val - b.val) = ok y := by
        rw [← Result.match.isOk, h']
      exact ⟨y, hsub, by rw [h'] at hm; exact hm.1⟩
    | div => rw [h'] at hm; exact hm.elim
    | vis e k => rw [h'] at hm; exact absurd h hm

  /-- `max a b - min a b` is the absolute difference of `a` and `b`. -/
  lemma max_sub_min (a b : Int) : max a b - min a b = max (a - b) (b - a) := by
    rcases le_total a b with h | h <;> omega

  /-- `dfs` on a leaf whose root-to-parent path has minimum `mn` and maximum `mx`. -/
  lemma dfs_leaf (v mn mx : Std.I64) (hv0 : 0 ≤ v.val) (hv1 : v.val ≤ 100000)
      (hmn0 : 0 ≤ mn.val) (hmn1 : mn.val ≤ 100000)
      (hmx0 : 0 ≤ mx.val) (hmx1 : mx.val ≤ 100000) :
      ∃ d : Std.I64, dfs (.Node v .Null .Null) mn mx = ok d ∧
        d.val = max v.val mx.val - min v.val mn.val := by
    have hmin : ((if v < mn then v else mn) : Std.I64).val = min v.val mn.val := by
      split <;> simp_all <;> omega
    have hmax : ((if v > mx then v else mx) : Std.I64).val = max v.val mx.val := by
      split <;> simp_all <;> omega
    have hb : IScalar.inBounds .I64
        (((if v > mx then v else mx) : Std.I64).val -
          ((if v < mn then v else mn) : Std.I64).val) := by
      rw [hmin, hmax]
      simp only [IScalar.inBounds, IScalarTy.numBits]
      omega
    obtain ⟨d, hd, hdv⟩ := I64_sub_ok hb
    have e1 : ((if v < mn then ok v else ok mn) : Result Std.I64) = ok (if v < mn then v else mn) := by
      split <;> simp_all
    have e2 : ((if v > mx then ok v else ok mx) : Result Std.I64) = ok (if v > mx then v else mx) := by
      split <;> simp_all
    refine ⟨d, ?_, ?_⟩
    · simp only [dfs.eq_def, e2, e1, bind_ok, hd]
      split <;> rfl
    · rw [hdv, hmax, hmin]

  /-** spec_S8 [shape]: on the tree `Node x (Node y Null Null) (Node z Null Null)` the result is
  `max(|x - y|, |x - z|)`. -/
  theorem spec_8 (root : Tree) (x y z : Std.I64)
      (hroot : root = .Node x (.Node y .Null .Null) (.Node z .Null .Null))
      (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
      (hy : 0 ≤ y.val ∧ y.val ≤ 100000)
      (hz : 0 ≤ z.val ∧ z.val ≤ 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = max (absDiff x.val y.val) (absDiff x.val z.val) := by
    intro res h
    subst hroot
    simp only [max_ancestor_diff] at h
    obtain ⟨d1, hd1, hd1v⟩ := dfs_leaf y x x hy.1 hy.2 hx.1 hx.2 hx.1 hx.2
    obtain ⟨d2, hd2, hd2v⟩ := dfs_leaf z x x hz.1 hz.2 hx.1 hx.2 hx.1 hx.2
    have e1 : d1.val = absDiff x.val y.val := by
      rw [hd1v, max_sub_min]
      simp only [absDiff]
      exact max_comm _ _
    have e2 : d2.val = absDiff x.val z.val := by
      rw [hd2v, max_sub_min]
      simp only [absDiff]
      exact max_comm _ _
    rw [hd1, hd2] at h
    simp only [bind_ok] at h
    by_cases hc : d1 > d2
    · rw [if_pos hc] at h
      simp only [Result.ok.injEq] at h
      subst h
      have hcv : d2.val < d1.val := by simpa using hc
      omega
    · rw [if_neg hc] at h
      simp only [Result.ok.injEq] at h
      subst h
      have hcv : d1.val ≤ d2.val := by simpa using le_of_not_gt hc
      omega

  /-** spec_S9 [invariance]: adding a constant `c` to every node value does not change the
  result. -/
  theorem spec_S9 (root : Tree) (c : Int)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hc : ∀ v ∈ values root, 0 ≤ v + c ∧ v + c ≤ 100000) :
      ∀ res res_c : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (shift c root) = ok res_c → res_c.val = res.val := by
    sorry

  /-** spec_S10 [invariance]: mirroring the tree does not change the result. -/
  theorem spec_S10 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res res_m : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (mirror root) = ok res_m → res_m.val = res.val := by
    sorry

  /-** spec_S11 [invariance]: replacing every node value `v` with `100000 - v` does not change
  the result. -/
  theorem spec_S11 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res res_rev : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (revValues root) = ok res_rev → res_rev.val = res.val := by
    sorry

  /-** spec_S12 [relational]: deleting one node and all its descendants can only decrease the
  result. -/
  theorem spec_S12 (root root' : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hprune : PruneAt root root')
      (hsize'_lo : 2 ≤ size root') (hsize'_hi : size root' ≤ 5000)
      (hval' : ValuesIn root' 0 100000) :
      ∀ res res' : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root' = ok res' → res'.val ≤ res.val := by
    sorry

  /-** spec_S13 [relational]: attaching one new leaf at a null child pointer can only increase
  the result. -/
  theorem spec_S13 (root root_plus : Tree) (w : Std.I64)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hw : 0 ≤ w.val ∧ w.val ≤ 100000)
      (hgraft : AddLeafAt w root root_plus)
      (hsize_plus : size root_plus ≤ 5000) :
      ∀ res res_plus : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root_plus = ok res_plus → res.val ≤ res_plus.val := by
    sorry

  /-** spec_S14 [relational]: if the root value `x` is the minimum value of the tree, the result
  is `maxVal(root) - x`. -/
  theorem spec_S14 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = minVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - x.val := by
    sorry

  /-** spec_S15 [relational]: if the root value `x` is the maximum value of the tree, the result
  is `x - minVal(root)`. -/
  theorem spec_S15 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = maxVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = x.val - minVal root := by
    sorry

  /-** spec_C1 [characterization]: the result is the maximum, over all root-to-leaf paths `P`,
  of `maxVal(P) - minVal(P)`. -/
  theorem spec_C1 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = pathSpreadMax root := by
    sorry

  /-** spec_C2 [per-node]: the result is the maximum, over all nodes `b`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))` (and `0` for the root). -/
  theorem spec_C2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    sorry

  end AegisSpec.MaxAncestorDiff
