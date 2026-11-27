import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_14` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Helpers for `spec_S14` -/

  /-- Pure (mathematical) version of `dfs`: the maximum, over all `Null` positions of `t`, of the
  running maximum minus the running minimum of the values on the path to that position.
  It mirrors the recursion of `dfs` (`Std.I64` inputs, `Int` result). -/
  def dfsSpec (mn mx : Std.I64) : Tree → Int
    | .Null => mx.val - mn.val
    | .Node v l r =>
      max (dfsSpec (if v < mn then v else mn) (if v > mx then v else mx) l)
        (dfsSpec (if v < mn then v else mn) (if v > mx then v else mx) r)

  /-- Lifting an `if` through `Result.ok`. -/
  lemma ite_ok (c : Prop) [Decidable c] (a b : Std.I64) :
      (if c then ok a else ok b : Result Std.I64) = ok (if c then a else b) := by
    split <;> rfl

  lemma ite_max_val (v mx : Std.I64) : (if v > mx then v else mx).val = max mx.val v.val := by
    by_cases h : v > mx
    · have h' : mx.val < v.val := h
      rw [if_pos h]
      omega
    · have h' : ¬ (mx.val < v.val) := h
      rw [if_neg h]
      omega

  lemma ite_min_val (v mn : Std.I64) : (if v < mn then v else mn).val = min v.val mn.val := by
    by_cases h : v < mn
    · have h' : v.val < mn.val := h
      rw [if_pos h]
      omega
    · have h' : ¬ (v.val < mn.val) := h
      rw [if_neg h]
      omega

  lemma le_foldl_max (l : List Int) (a : Int) : a ≤ l.foldl max a := by
    induction l generalizing a with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left a x) (ih (max a x))

  lemma foldl_max_shift (l : List Int) (a b : Int) (h : a ≤ b) :
      l.foldl max b = max b (l.foldl max a) := by
    induction l generalizing a b with
    | nil => simp; omega
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (a := max a x) (b := max b x) (by omega)]
      have := le_foldl_max xs (max a x)
      omega

  lemma foldl_max_append (l₁ l₂ : List Int) (a : Int) :
      (l₁ ++ l₂).foldl max a = max (l₁.foldl max a) (l₂.foldl max a) := by
    rw [List.foldl_append, foldl_max_shift l₂ a (l₁.foldl max a) (le_foldl_max l₁ a)]

  lemma foldl_min_le_self (l : List Int) (a : Int) : l.foldl min a ≤ a := by
    induction l generalizing a with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min a x)) (min_le_left a x)

  lemma foldl_min_le_mem (l : List Int) (a x : Int) (h : x ∈ l) : l.foldl min a ≤ x := by
    induction l generalizing a with
    | nil => simp at h
    | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with hxy | h
      · rw [hxy]
        exact le_trans (foldl_min_le_self ys (min a y)) (min_le_right a y)
      · exact ih (min a y) h

  lemma dfsSpec_eq_foldl (t : Tree) (mn mx : Std.I64)
      (h : ∀ y ∈ values t, mn.val ≤ y) :
      dfsSpec mn mx t = (values t).foldl max mx.val - mn.val := by
    induction t generalizing mn mx with
    | Null => simp [dfsSpec, values]
    | Node v l r ihl ihr =>
      have hv : mn.val ≤ v.val := h v.val (by simp [values])
      have hl : ∀ y ∈ values l, mn.val ≤ y := fun y hy => h y (by simp [values, hy])
      have hr : ∀ y ∈ values r, mn.val ≤ y := fun y hy => h y (by simp [values, hy])
      have hmn : (if v < mn then v else mn) = mn := by
        rw [if_neg]
        simp only [IScalar.lt_equiv, not_lt]
        exact hv
      simp only [dfsSpec, values, List.foldl_cons]
      rw [hmn, ihl mn _ hl, ihr mn _ hr, ite_max_val, foldl_max_append]
      omega

  lemma maxVal_node (x : Std.I64) (l r : Tree) (h : 0 ≤ x.val) :
      maxVal (.Node x l r)
        = max ((values l).foldl max x.val) ((values r).foldl max x.val) := by
    have h1 : maxVal (.Node x l r) = (values l ++ values r).foldl max (max 0 x.val) := by
      simp [maxVal, listMax, values]
    have h2 : max 0 x.val = x.val := by omega
    rw [h1, h2, foldl_max_append]

  lemma dfsSpec_node_max (x : Std.I64) (l r : Tree) (hx : 0 ≤ x.val)
      (hl : ∀ y ∈ values l, x.val ≤ y) (hr : ∀ y ∈ values r, x.val ≤ y) :
      max (dfsSpec x x l) (dfsSpec x x r)
        = maxVal (.Node x l r) - x.val := by
    rw [dfsSpec_eq_foldl l x x hl, dfsSpec_eq_foldl r x x hr,
      maxVal_node x l r hx]
    omega

  lemma minVal_le_mem {t : Tree} {y : Int} (h : y ∈ values t) : minVal t ≤ y :=
    foldl_min_le_mem (values t) 100000 y h

  theorem dfs_dspec (t : Tree) : ∀ (mn mx : Std.I64), ValuesIn t 0 100000 →
      0 ≤ mn.val → mn.val ≤ 100000 → 0 ≤ mx.val → mx.val ≤ 100000 →
      Std.WP.dspec (dfs t mn mx) (fun res => res.val = dfsSpec mn mx t) := by
    induction t with
    | Null =>
      intro mn mx hv hmn0 hmn1 hmx0 hmx1
      simp only [dfs.eq_def, dfsSpec]
      step
      assumption
    | Node v l r ihl ihr =>
      intro mn mx hv hmn0 hmn1 hmx0 hmx1
      rw [dfs.eq_def]
      simp only [dfsSpec, ite_ok, bind_ok]
      have hv1 : 0 ≤ v.val := (hv v.val (by simp [values])).1
      have hv2 : v.val ≤ 100000 := (hv v.val (by simp [values])).2
      have hvl : ValuesIn l 0 100000 := fun y hy => hv y (by simp [values, hy])
      have hvr : ValuesIn r 0 100000 := fun y hy => hv y (by simp [values, hy])
      have h1 : 0 ≤ (if v < mn then v else mn).val := by rw [ite_min_val]; omega
      have h2 : (if v < mn then v else mn).val ≤ 100000 := by rw [ite_min_val]; omega
      have h3 : 0 ≤ (if v > mx then v else mx).val := by rw [ite_max_val]; omega
      have h4 : (if v > mx then v else mx).val ≤ 100000 := by rw [ite_max_val]; omega
      have ih1 := ihl (if v < mn then v else mn) (if v > mx then v else mx) hvl h1 h2 h3 h4
      step with ih1
      have ih2 := ihr (if v < mn then v else mn) (if v > mx then v else mx) hvr h1 h2 h3 h4
      step with ih2
      rw [Std.WP.dspec_ok]
      by_cases hab : a > b
      · have hab' : b.val < a.val := hab
        rw [if_pos hab]
        omega
      · have hab' : ¬ (b.val < a.val) := hab
        rw [if_neg hab]
        omega

  /-** spec_S14 [relational]: if the root value `x` is the minimum value of the tree, the result
  is `maxVal(root) - x`. -/
  theorem spec_14 (root : Tree) (x : Std.I64) (l r : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hroot : root = .Node x l r)
      (hx : x.val = minVal root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - x.val := by
    subst hroot
    intro res hres
    have hvx : 0 ≤ x.val ∧ x.val ≤ 100000 := hval x.val (by simp [values])
    have hx0 : 0 ≤ x.val := hvx.1
    have hx1 : x.val ≤ 100000 := hvx.2
    -- `x` is a lower bound for all node values
    have hl : ∀ y ∈ values l, x.val ≤ y := by
      intro y hy
      have h1 : y ∈ values (.Node x l r) := by simp [values, hy]
      have h2 := minVal_le_mem h1
      omega
    have hr : ∀ y ∈ values r, x.val ≤ y := by
      intro y hy
      have h1 : y ∈ values (.Node x l r) := by simp [values, hy]
      have h2 := minVal_le_mem h1
      omega
    have hvl : ValuesIn l 0 100000 := fun y hy => hval y (by simp [values, hy])
    have hvr : ValuesIn r 0 100000 := fun y hy => hval y (by simp [values, hy])
    -- the value computed by the program
    have hmain : Std.WP.dspec (max_ancestor_diff (.Node x l r))
        (fun res => res.val = maxVal (.Node x l r) - x.val) := by
      rw [max_ancestor_diff.eq_def]
      simp only [ite_ok]
      have hdsl := dfs_dspec l x x hvl hx0 hx1 hx0 hx1
      step with hdsl
      have hdsr := dfs_dspec r x x hvr hx0 hx1 hx0 hx1
      step with hdsr
      rw [Std.WP.dspec_ok]
      have hM := dfsSpec_node_max x l r hx0 hl hr
      by_cases hab : a > b
      · have hab' : b.val < a.val := hab
        rw [if_pos hab]
        omega
      · have hab' : ¬ (b.val < a.val) := hab
        rw [if_neg hab]
        omega
    rw [hres] at hmain
    exact (Std.WP.dspec_ok res).mp hmain

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
