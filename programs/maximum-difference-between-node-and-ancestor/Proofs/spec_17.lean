import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_17` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary results used by `spec_C2` -/

  /-- `spread mn mx t` is the value computed by `dfs t mn mx`, assuming that no arithmetic
  operation overflows. -/
  def spread (mn mx : Std.I64) : Tree → Int
    | .Null => mx.val - mn.val
    | .Node v l r =>
      max (spread (if v < mn then v else mn) (if v > mx then v else mx) l)
          (spread (if v < mn then v else mn) (if v > mx then v else mx) r)

  lemma ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
      (if c then Result.ok x else Result.ok y) = Result.ok (if c then x else y) := by
    split <;> rfl

  lemma foldl_max_init (l : List Int) (a : Int) (ha : 0 ≤ a) :
      l.foldl max a = max a (l.foldl max 0) := by
    induction l generalizing a with
    | nil => simp; omega
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max a x) (by omega), ih (max 0 x) (by omega)]
      omega

  lemma foldl_min_init (l : List Int) (a : Int) (ha : a ≤ 100000)
      (hl : ∀ y ∈ l, y ≤ 100000) :
      l.foldl min a = min a (l.foldl min 100000) := by
    induction l generalizing a with
    | nil => simp; omega
    | cons x xs ih =>
      obtain ⟨hx, hxs⟩ : x ≤ 100000 ∧ ∀ y ∈ xs, y ≤ 100000 :=
        ⟨hl x (by simp), fun y hy => hl y (by simp [hy])⟩
      simp only [List.foldl_cons]
      rw [ih (min a x) (by omega) hxs, show min 100000 x = x from by omega, ih x hx hxs]
      omega

  lemma listMax_cons (v : Int) (acc : List Int) (hv : 0 ≤ v) :
      listMax (v :: acc) = max v (listMax acc) := by
    simp only [listMax]
    rw [show (v :: acc).foldl max 0 = acc.foldl max (max 0 v) from rfl,
      show max 0 v = v from by omega]
    exact foldl_max_init acc v hv

  lemma listMin_cons (v : Int) (acc : List Int) (hv : v ≤ 100000)
      (hacc : ∀ x ∈ acc, x ≤ 100000) :
      listMin (v :: acc) = min v (listMin acc) := by
    simp only [listMin]
    rw [show (v :: acc).foldl min 100000 = acc.foldl min (min 100000 v) from rfl,
      show min 100000 v = v from by omega]
    exact foldl_min_init acc v hv hacc

  lemma le_foldl_max (l : List Int) (b : Int) : b ≤ l.foldl max b := by
    induction l generalizing b with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left b x) (ih (max b x))

  lemma foldl_max_le (l : List Int) (b x : Int) (hx : x ∈ l) : x ≤ l.foldl max b := by
    induction l generalizing b with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (le_max_right b x) (le_foldl_max ys (max b x))
      · exact ih (max b y) hx

  lemma foldl_min_le (l : List Int) (b : Int) : l.foldl min b ≤ b := by
    induction l generalizing b with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min b x)) (min_le_left b x)

  lemma le_foldl_min (l : List Int) (b x : Int) (hx : x ∈ l) : l.foldl min b ≤ x := by
    induction l generalizing b with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (foldl_min_le ys (min b x)) (min_le_right b x)
      · exact ih (min b y) hx

  lemma listMax_nonneg (l : List Int) : 0 ≤ listMax l := le_foldl_max l 0

  lemma listMin_le_100000 (l : List Int) : listMin l ≤ 100000 := foldl_min_le l 100000

  lemma foldl_min_nonneg (l : List Int) (b : Int) (hb : 0 ≤ b) (h : ∀ x ∈ l, 0 ≤ x) :
      0 ≤ l.foldl min b := by
    induction l generalizing b with
    | nil => simpa using hb
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (min b x) (by have hx : 0 ≤ x := h x (by simp); omega)
        (fun y hy => h y (by simp [hy]))

  lemma listMin_nonneg (l : List Int) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ listMin l :=
    foldl_min_nonneg l 100000 (by norm_num) h

  lemma foldl_max_le_ub (l : List Int) (b : Int) (hb : b ≤ 100000)
      (h : ∀ x ∈ l, x ≤ 100000) : l.foldl max b ≤ 100000 := by
    induction l generalizing b with
    | nil => simpa using hb
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (max b x) (by have hx : x ≤ 100000 := h x (by simp); omega)
        (fun y hy => h y (by simp [hy]))

  lemma listMax_le_ub (l : List Int) (h : ∀ x ∈ l, x ≤ 100000) : listMax l ≤ 100000 :=
    foldl_max_le_ub l 0 (by norm_num) h

  lemma listMin_le_listMax (v : Int) (acc : List Int) (hv : 0 ≤ v ∧ v ≤ 100000)
      (hacc : ∀ x ∈ acc, 0 ≤ x ∧ x ≤ 100000) :
      listMin (v :: acc) ≤ listMax (v :: acc) := by
    have h1 : listMin (v :: acc) ≤ v := by
      rw [listMin_cons v acc hv.2 (fun x hx => (hacc x hx).2)]
      exact min_le_left v (listMin acc)
    have h2 : v ≤ listMax (v :: acc) := by
      rw [listMax_cons v acc hv.1]
      exact le_max_left v (listMax acc)
    omega

  /-- The maximum, over the nodes of `t`, of the contribution of each node with respect to the
  proper ancestors listed (from the nearest upwards) in `v :: acc`, is the value computed by
  `dfs`. -/
  lemma spread_eq_nodeContribMaxAux (t : Tree) :
      ∀ (v : Int) (acc : List Int) (mn mx : Std.I64),
        (∀ x ∈ v :: acc, 0 ≤ x ∧ x ≤ 100000) →
        ValuesIn t 0 100000 →
        mn.val = listMin (v :: acc) → mx.val = listMax (v :: acc) →
        spread mn mx t = max (mx.val - mn.val) (nodeContribMaxAux (v :: acc) t) := by
    induction t with
    | Null =>
      intro v acc mn mx hv _ hmn hmx
      have hle : listMin (v :: acc) ≤ listMax (v :: acc) :=
        listMin_le_listMax v acc (hv v (by simp)) (fun x hx => hv x (by simp [hx]))
      simp only [spread, nodeContribMaxAux]
      omega
    | Node w l r ihl ihr =>
      intro v acc mn mx hv hvt hmn hmx
      obtain ⟨hwv, hacc⟩ :
          (0 ≤ w.val ∧ w.val ≤ 100000) ∧ (∀ x ∈ v :: acc, 0 ≤ x ∧ x ≤ 100000) :=
        ⟨hvt w.val (by simp [values]), hv⟩
      have hvl : ValuesIn l 0 100000 :=
        fun x hx => hvt x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hvr : ValuesIn r 0 100000 :=
        fun x hx => hvt x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hacc' : ∀ x ∈ w.val :: v :: acc, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hwv
        · exact hv x hx
      have hle : listMin (v :: acc) ≤ listMax (v :: acc) :=
        listMin_le_listMax v acc (hv v (by simp)) (fun x hx => hv x (by simp [hx]))
      have hmn2 : listMin (w.val :: v :: acc) = min w.val (listMin (v :: acc)) :=
        listMin_cons w.val (v :: acc) hwv.2 (fun x hx => (hv x hx).2)
      have hmx2 : listMax (w.val :: v :: acc) = max w.val (listMax (v :: acc)) :=
        listMax_cons w.val (v :: acc) hwv.1
      have hmn' : (if w < mn then w else mn).val = listMin (w.val :: v :: acc) := by
        rw [hmn2]
        split <;> (rename_i h; simp only [IScalar.lt_equiv] at h; omega)
      have hmx' : (if w > mx then w else mx).val = listMax (w.val :: v :: acc) := by
        rw [hmx2]
        split <;> (rename_i h; simp only [IScalar.lt_equiv] at h; omega)
      rw [spread,
        ihl w (v :: acc) (if w < mn then w else mn) (if w > mx then w else mx)
          hacc' hvl hmn' hmx',
        ihr w (v :: acc) (if w < mn then w else mn) (if w > mx then w else mx)
          hacc' hvr hmn' hmx']
      simp only [nodeContribMaxAux, nodeContrib]
      omega

  lemma ite_min_nonneg (a b : Std.I64) (ha : 0 ≤ a.val) (hb : 0 ≤ b.val) :
      0 ≤ (if a < b then a else b).val := by
    split <;> (rename_i h; simp only [IScalar.lt_equiv] at h) <;> omega

  lemma ite_max_le_ub (a b : Std.I64) (ha : a.val ≤ 100000) (hb : b.val ≤ 100000) :
      (if a > b then a else b).val ≤ 100000 := by
    split <;> (rename_i h; simp only [IScalar.lt_equiv] at h) <;> omega

  lemma ite_min_le_ite_max (mn mx v : Std.I64) (h : mn.val ≤ mx.val) :
      (if v < mn then v else mn).val ≤ (if v > mx then v else mx).val := by
    split <;> split <;> (simp only [IScalar.lt_equiv] at *; omega)

  @[local step]
  theorem dfs_spread (t : Tree) (mn mx : Std.I64)
      (hlo : 0 ≤ mn.val) (hmn : mn.val ≤ mx.val) (hmx : mx.val ≤ 100000)
      (hv : ValuesIn t 0 100000) :
      dfs t mn mx ⦃ res => res.val = spread mn mx t ⦄ := by
    unfold dfs
    cases h : t with
    | Null => step*; simp only [spread]; omega
    | Node v l r =>
      have hvn : ValuesIn (Tree.Node v l r) 0 100000 := h ▸ hv
      have hv1 : 0 ≤ v.val ∧ v.val ≤ 100000 := hvn v.val (by simp [values])
      have hvl : ValuesIn l 0 100000 := fun x hx =>
        hvn x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hvr : ValuesIn r 0 100000 := fun x hx =>
        hvn x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have h1 : 0 ≤ (if v < mn then v else mn).val := ite_min_nonneg v mn hv1.1 hlo
      have h2 : (if v < mn then v else mn).val ≤ (if v > mx then v else mx).val :=
        ite_min_le_ite_max mn mx v hmn
      have h3 : (if v > mx then v else mx).val ≤ 100000 := ite_max_le_ub v mx hv1.2 hmx
      simp only [ite_ok, bind_tc_eq, bind_ok]
      step*
      all_goals
        first
          | exact h1
          | exact h2
          | exact h3
          | exact hvl
          | exact hvr
          | (simp only [spread]; split <;> (simp only [IScalar.lt_equiv] at *; omega))
    termination_by size t
    decreasing_by
      all_goals (simp only [h, size]; omega)

  lemma dfs_ok (t : Tree) (mn mx res : Std.I64)
      (hlo : 0 ≤ mn.val) (hmn : mn.val ≤ mx.val) (hmx : mx.val ≤ 100000)
      (hv : ValuesIn t 0 100000) (h : dfs t mn mx = ok res) :
      res.val = spread mn mx t := by
    simpa [h] using dfs_spread t mn mx hlo hmn hmx hv

  /-** spec_C2 [per-node]: the result is the maximum, over all nodes `b`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))` (and `0` for the root). -/
  theorem spec_17 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    intro res hres
    have hspec : max_ancestor_diff root ⦃ res => res.val = nodeContribMax root ⦄ := by
      cases h : root with
      | Null => rw [h] at hsize_lo; simp [size] at hsize_lo
      | Node v l r =>
        have hvn : ValuesIn (Tree.Node v l r) 0 100000 := h ▸ hval
        obtain ⟨hv1a, hv1b⟩ : 0 ≤ v.val ∧ v.val ≤ 100000 := hvn v.val (by simp [values])
        have hvl : ValuesIn l 0 100000 := fun x hx =>
          hvn x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
        have hvr : ValuesIn r 0 100000 := fun x hx =>
          hvn x (by simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
        have hacc : ∀ x ∈ v.val :: ([] : List Int), 0 ≤ x ∧ x ≤ 100000 := by
          intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact ⟨hv1a, hv1b⟩
        have hmin : listMin [v.val] = v.val := by
          simp only [listMin, List.foldl_cons, List.foldl_nil]
          omega
        have hmax : listMax [v.val] = v.val := by
          simp only [listMax, List.foldl_cons, List.foldl_nil]
          omega
        have hspL := spread_eq_nodeContribMaxAux l v.val [] v v hacc hvl hmin.symm hmax.symm
        have hspR := spread_eq_nodeContribMaxAux r v.val [] v v hacc hvr hmin.symm hmax.symm
        unfold max_ancestor_diff
        simp only [ite_ok]
        step*
        rw [hspL, sub_self] at a_post
        rw [hspR, sub_self] at b_post
        simp only [nodeContribMax, nodeContribMaxAux, nodeContrib]
        split <;> (simp only [IScalar.lt_equiv] at *; omega)
    simpa [hres] using hspec

  end AegisSpec.MaxAncestorDiff
