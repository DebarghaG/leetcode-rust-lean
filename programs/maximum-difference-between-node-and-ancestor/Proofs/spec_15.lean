import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_15` (maximum-difference-between-node-and-ancestor).
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

  /-** spec_S8 [shape]: on the tree `Node x (Node y Null Null) (Node z Null Null)` the result is
  `max(|x - y|, |x - z|)`. -/
  theorem spec_S8 (root : Tree) (x y z : Std.I64)
      (hroot : root = .Node x (.Node y .Null .Null) (.Node z .Null .Null))
      (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
      (hy : 0 ≤ y.val ∧ y.val ≤ 100000)
      (hz : 0 ≤ z.val ∧ z.val ≤ 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = max (absDiff x.val y.val) (absDiff x.val z.val) := by
    sorry

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

  /-! ### Auxiliary development for `spec_S15` -/

  section S15Aux

  /-- `foldl min` is bounded by its initial accumulator. -/
  lemma foldl_min_le_acc (l : List Int) (b : Int) : l.foldl min b ≤ b := by
    induction l generalizing b with
    | nil => simp
    | cons x l ih => simpa using le_trans (ih (min b x)) (min_le_left b x)

  /-- `foldl min` is bounded by each of the elements of the list. -/
  lemma foldl_min_le_of_mem (l : List Int) (b : Int) {a : Int} (ha : a ∈ l) :
      l.foldl min b ≤ a := by
    induction l generalizing b with
    | nil => exact absurd ha (List.not_mem_nil)
    | cons x l ih =>
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_trans (foldl_min_le_acc l (min b a)) (min_le_right b a)
      · exact ih (min b x) ha

  /-- `foldl min` is either the accumulator or one of the elements of the list. -/
  lemma foldl_min_self_or_mem (l : List Int) (b : Int) :
      l.foldl min b = b ∨ l.foldl min b ∈ l := by
    induction l generalizing b with
    | nil => exact Or.inl rfl
    | cons x l ih =>
      rcases ih (min b x) with h | h
      · rcases min_choice b x with hb | hb
        · exact Or.inl (h.trans hb)
        · exact Or.inr (by rw [List.mem_cons]; exact Or.inl (h.trans hb))
      · exact Or.inr (List.mem_cons_of_mem x h)

  /-- The accumulator is bounded by `foldl max`. -/
  lemma le_foldl_max_acc (l : List Int) (b : Int) : b ≤ l.foldl max b := by
    induction l generalizing b with
    | nil => simp
    | cons x l ih => exact le_trans (le_max_left b x) (ih (max b x))

  /-- Every element of the list is bounded by `foldl max`. -/
  lemma le_foldl_max_of_mem (l : List Int) (b : Int) {a : Int} (ha : a ∈ l) :
      a ≤ l.foldl max b := by
    induction l generalizing b with
    | nil => exact absurd ha (List.not_mem_nil)
    | cons x l ih =>
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_trans (le_max_right b a) (le_foldl_max_acc l (max b a))
      · exact ih (max b x) ha

  /-- `foldl max` is either the accumulator or one of the elements of the list. -/
  lemma foldl_max_self_or_mem (l : List Int) (b : Int) :
      l.foldl max b = b ∨ l.foldl max b ∈ l := by
    induction l generalizing b with
    | nil => exact Or.inl rfl
    | cons x l ih =>
      rcases ih (max b x) with h | h
      · rcases max_choice b x with hb | hb
        · exact Or.inl (h.trans hb)
        · exact Or.inr (by rw [List.mem_cons]; exact Or.inl (h.trans hb))
      · exact Or.inr (List.mem_cons_of_mem x h)

  /-- Monotonicity of the minimal value of a nonempty list against the accumulator `100000`. -/
  lemma foldl_min_eq_min (l : List Int) (b : Int) (hb : b ≤ 100000)
      (hl : ∀ a ∈ l, a ≤ 100000) :
      l.foldl min b = min b (l.foldl min 100000) := by
    induction l generalizing b with
    | nil => simp [min_eq_left hb]
    | cons x l ih =>
      have hx : x ≤ 100000 := hl x (by simp)
      have hl' : ∀ a ∈ l, a ≤ 100000 := fun a ha => hl a (by simp [ha])
      have hb' : min b x ≤ 100000 := le_trans (min_le_left _ _) hb
      rw [List.foldl_cons, ih (min b x) hb' hl']
      have hacc : (x :: l).foldl min 100000 = l.foldl min x := by
        rw [List.foldl_cons, min_eq_right hx]
      rw [hacc, ih x hx hl', min_assoc]

  /-- Minimum of the node values, recursively (with `100000` as the top element). -/
  def tmin : Tree → Int
    | .Null => 100000
    | .Node v l r => min v.val (min (tmin l) (tmin r))

  /-- `tmin` computes the same value as `minVal` for trees with values at most `100000`. -/
  lemma tmin_eq_minVal (t : Tree) (h : ∀ v ∈ values t, v ≤ 100000) :
      minVal t = tmin t := by
    induction t with
    | Null => rfl
    | Node v l r ihl ihr =>
      have hv : v.val ≤ 100000 := h v.val (by simp [values])
      have hl : ∀ a ∈ values l, a ≤ 100000 := fun a ha => h a (by simp [values, ha])
      have hr : ∀ a ∈ values r, a ≤ 100000 := fun a ha => h a (by simp [values, ha])
      have hb : min v.val ((values l).foldl min 100000) ≤ 100000 :=
        le_trans (min_le_left _ _) hv
      have hl1 : (values l).foldl min v.val = min v.val (minVal l) := by
        simpa [minVal, listMin] using foldl_min_eq_min (values l) v.val hv hl
      have hr1 : (values r).foldl min (min v.val (minVal l)) =
          min (min v.val (minVal l)) (minVal r) := by
        simpa [minVal, listMin] using
          foldl_min_eq_min (values r) (min v.val ((values l).foldl min 100000)) hb hr
      show listMin (v.val :: (values l ++ values r)) =
        min v.val (min (tmin l) (tmin r))
      rw [listMin, List.foldl_cons, min_eq_right hv, List.foldl_append, hl1, hr1,
        ← ihl hl, ← ihr hr, ← min_assoc]

  /-- Signed subtraction is successful and computes the integer difference when in bounds. -/
  lemma sub_ok_of_bounds {x y : Std.I64} (h : IScalar.inBounds .I64 (x.val - y.val)) :
      ∃ z : Std.I64, (x - y : Result Std.I64) = ok z ∧ z.val = x.val - y.val := by
    have hh := IScalar.sub_equiv (ty := .I64) x y
    split at hh
    · rename_i zv hz
      exact ⟨zv, Result.match.isOk.mp hz, hh.2.1⟩
    · exact absurd h (by assumption)
    · exact hh.elim

  /-- The value of `if a > b then a else b` is `max a.val b.val`. -/
  lemma if_gt_val (a b : Std.I64) : (if a > b then a else b).val = max a.val b.val := by
    by_cases h : a > b
    · have h' : b.val ≤ a.val := le_of_lt h
      simp [h, max_eq_left h']
    · have h' : a.val ≤ b.val := not_lt.mp h
      simp [h, max_eq_right h']

  /-- `max (X - u) (X - w) = X - min u w`. -/
  lemma sub_max_min (X u w : Int) : max (X - u) (X - w) = X - min u w := by
    by_cases h : u ≤ w
    · rw [min_eq_left h, max_eq_left (sub_le_sub_left h X)]
    · have h' : w ≤ u := le_of_lt (not_le.mp h)
      rw [min_eq_right h', max_eq_right (sub_le_sub_left h' X)]

  /-- Associativity-style identity for the minimum of four values. -/
  lemma min_min_min (X c d : Int) : min (min X c) (min X d) = min X (min c d) := by
    simp only [Int.min_def]
    split_ifs <;> omega

  /-- Specification of `dfs`: starting from the accumulated bounds `mn` and `mx`, the result is
  `mx - (minimum of the running minimum and of the node values)`. -/
  lemma dfs_min_spec (t : Tree) (mn mx : Std.I64) (h0 : 0 ≤ mn.val)
      (hlm : mn.val ≤ mx.val) (hmx : mx.val ≤ 100000)
      (hv : ∀ v ∈ values t, 0 ≤ v ∧ v ≤ mx.val) :
      ∃ res : Std.I64, dfs t mn mx = ok res ∧ res.val = mx.val - min mn.val (tmin t) := by
    induction t generalizing mn mx with
    | Null =>
      have hb : IScalar.inBounds .I64 (mx.val - mn.val) := by
        constructor <;> scalar_tac
      obtain ⟨z, hz, hzv⟩ := sub_ok_of_bounds hb
      refine ⟨z, ?_, ?_⟩
      · rw [dfs.eq_def]; exact hz
      · rw [hzv]
        show mx.val - mn.val = mx.val - min mn.val (100000 : Int)
        rw [min_eq_left (le_trans hlm hmx)]
    | Node v l r ihl ihr =>
      have hv0 : 0 ≤ v.val := (hv v.val (by simp [values])).1
      have hvmx : v.val ≤ mx.val := (hv v.val (by simp [values])).2
      have hvl : ∀ u ∈ values l, 0 ≤ u ∧ u ≤ mx.val :=
        fun u hu => hv u (by simp [values, hu])
      have hvr : ∀ u ∈ values r, 0 ≤ u ∧ u ≤ mx.val :=
        fun u hu => hv u (by simp [values, hu])
      set nm : Std.I64 := (if v < mn then v else mn) with hnm
      have hnm_val : nm.val = min mn.val v.val := by
        by_cases h : v < mn
        · have h' : v.val < mn.val := h
          simp [hnm, h, min_eq_right (le_of_lt h')]
        · have h' : mn.val ≤ v.val := not_lt.mp h
          simp [hnm, h, min_eq_left h']
      have hnm0 : 0 ≤ nm.val := by rw [hnm_val]; exact le_min h0 hv0
      have hnmmx : nm.val ≤ mx.val := by
        rw [hnm_val]; exact le_trans (min_le_left _ _) hlm
      obtain ⟨a, ha, hva⟩ := ihl nm mx hnm0 hnmmx hmx hvl
      obtain ⟨b, hb, hvb⟩ := ihr nm mx hnm0 hnmmx hmx hvr
      have hnm_ok : (if v < mn then ok v else ok mn) = ok nm := by
        by_cases h : v < mn <;> simp [hnm, h]
      have hnmx_ok : (if v > mx then ok v else ok mx) = ok mx := by
        by_cases h : v > mx
        · exact absurd h (not_lt.mpr hvmx)
        · simp [h]
      refine ⟨(if a > b then a else b), ?_, ?_⟩
      · rw [dfs.eq_def]
        simp only [hnm_ok, hnmx_ok, ha, hb, bind_ok]
        by_cases hab : a > b <;> simp [hab]
      · rw [if_gt_val, hva, hvb]
        show max (mx.val - min nm.val (tmin l)) (mx.val - min nm.val (tmin r)) =
          mx.val - min mn.val (min v.val (min (tmin l) (tmin r)))
        rw [hnm_val, sub_max_min, min_min_min, min_assoc]

  end S15Aux

  /-** spec_S15 [relational]: if the root value `x` is the maximum value of the tree, the result
  is `x - minVal(root)`. -/
  theorem spec_15 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = maxVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = x.val - minVal root := by
    subst hroot
    intro res hres
    have hxmem : x.val ∈ values (.Node x l r) := by simp [values]
    have hx0 : 0 ≤ x.val := (hval x.val hxmem).1
    have hxm : x.val ≤ 100000 := (hval x.val hxmem).2
    have hmax : ∀ u ∈ values (.Node x l r), u ≤ x.val := by
      intro u hu
      have h := le_foldl_max_of_mem (values (.Node x l r)) 0 hu
      rw [hx]; exact h
    have hvl : ∀ u ∈ values l, 0 ≤ u ∧ u ≤ x.val := by
      intro u hu
      exact ⟨(hval u (by simp [values, hu])).1, hmax u (by simp [values, hu])⟩
    have hvr : ∀ u ∈ values r, 0 ≤ u ∧ u ≤ x.val := by
      intro u hu
      exact ⟨(hval u (by simp [values, hu])).1, hmax u (by simp [values, hu])⟩
    obtain ⟨a, ha, hva⟩ := dfs_min_spec l x x hx0 (le_refl _) hxm hvl
    obtain ⟨b, hb, hvb⟩ := dfs_min_spec r x x hx0 (le_refl _) hxm hvr
    have hmad : max_ancestor_diff (.Node x l r) = ok (if a > b then a else b) := by
      rw [max_ancestor_diff.eq_def]
      simp only [ha, hb, bind_ok]
      by_cases hab : a > b <;> simp [hab]
    have hres' : res = (if a > b then a else b) := by
      rw [hmad] at hres
      simpa using hres.symm
    have htmin : minVal (.Node x l r) = min x.val (min (tmin l) (tmin r)) := by
      rw [tmin_eq_minVal _ (fun u hu => (hval u hu).2)]
      rfl
    rw [hres', if_gt_val, hva, hvb, htmin, sub_max_min, min_min_min]

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
