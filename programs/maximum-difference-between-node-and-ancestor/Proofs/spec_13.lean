import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_13` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary material for `spec_S13` -/

  /-- Integer-valued version of the running maximum computed by `dfs`: at a null node it
  returns `mx - mn`, and at a node with value `v` it pushes `v` into the running interval. -/
  def fmax (t : Tree) (mn mx : Int) : Int :=
    match t with
    | .Null => mx - mn
    | .Node v l r =>
      max (fmax l (min mn v.val) (max mx v.val)) (fmax r (min mn v.val) (max mx v.val))

  @[simp] theorem fmax_null (mn mx : Int) : fmax .Null mn mx = mx - mn := rfl

  @[simp] theorem fmax_node (v : Std.I64) (l r : Tree) (mn mx : Int) :
      fmax (.Node v l r) mn mx =
        max (fmax l (min mn v.val) (max mx v.val))
          (fmax r (min mn v.val) (max mx v.val)) := rfl

  /-- Value of the running-minimum update performed by `dfs`. -/
  theorem ite_min_val (v mn : Std.I64) :
      (if v < mn then v else mn).val = min mn.val v.val := by
    by_cases h : v < mn
    · have h' : v.val < mn.val := by simpa using h
      rw [if_pos h]
      exact (min_eq_right (le_of_lt h')).symm
    · have h' : mn.val ≤ v.val := by simpa using h
      rw [if_neg h]
      exact (min_eq_left h').symm

  /-- Value of the running-maximum update performed by `dfs`. -/
  theorem ite_max_val (v mx : Std.I64) :
      (if v > mx then v else mx).val = max mx.val v.val := by
    by_cases h : v > mx
    · have h' : mx.val < v.val := by simpa using h
      rw [if_pos h]
      exact (max_eq_right (le_of_lt h')).symm
    · have h' : v.val ≤ mx.val := by simpa using h
      rw [if_neg h]
      exact (max_eq_left h').symm

  theorem ite_max_val' (a b : Std.I64) :
      (if a > b then a else b).val = max a.val b.val := by
    rw [ite_max_val a b, max_comm]

  /-- A successful checked subtraction, as an equation on values. -/
  theorem I64.sub_eq_ok {x y : Std.I64} (h : IScalar.inBounds .I64 (x.val - y.val)) :
      ∃ z : Std.I64, x - y = ok z ∧ z.val = x.val - y.val := by
    have h' := @IScalar.sub_equiv .I64 x y
    split at h'
    next z heq =>
      obtain ⟨-, hval, -⟩ := h'
      simp at heq
      exact ⟨z, heq, hval⟩
    next heq =>
      exfalso
      exact h' h
    next => exact h'.elim

  /-- Unfolding of `dfs` at a node, once the recursive calls are known. -/
  theorem dfs_node_ok (v : Std.I64) (l r : Tree) (mn mx a b : Std.I64)
      (ha : dfs l (if v < mn then v else mn) (if v > mx then v else mx) = ok a)
      (hb : dfs r (if v < mn then v else mn) (if v > mx then v else mx) = ok b) :
      dfs (.Node v l r) mn mx = ok (if a > b then a else b) := by
    rw [dfs.eq_def]
    simp only []
    by_cases h1 : v < mn <;> by_cases h2 : v > mx
    · rw [if_pos h1, if_pos h2] at ha hb
      rw [if_pos h1, if_pos h2]
      simp only [ha, hb, bind_ok, bind_tc_ok]
      by_cases h3 : a > b <;> simp [h3]
    · rw [if_pos h1, if_neg h2] at ha hb
      rw [if_pos h1, if_neg h2]
      simp only [ha, hb, bind_ok, bind_tc_ok]
      by_cases h3 : a > b <;> simp [h3]
    · rw [if_neg h1, if_pos h2] at ha hb
      rw [if_neg h1, if_pos h2]
      simp only [ha, hb, bind_ok, bind_tc_ok]
      by_cases h3 : a > b <;> simp [h3]
    · rw [if_neg h1, if_neg h2] at ha hb
      rw [if_neg h1, if_neg h2]
      simp only [ha, hb, bind_ok, bind_tc_ok]
      by_cases h3 : a > b <;> simp [h3]

  /-- Unfolding of `max_ancestor_diff` at a node, once the recursive calls are known. -/
  theorem mad_node_ok (v a b : Std.I64) (l r : Tree)
      (ha : dfs l v v = ok a) (hb : dfs r v v = ok b) :
      max_ancestor_diff (.Node v l r) = ok (if a > b then a else b) := by
    rw [max_ancestor_diff.eq_def]
    simp only []
    simp only [ha, hb, bind_ok, bind_tc_ok]
    by_cases h : a > b <;> simp [h]

  /-! #### Specification of `dfs` -/

  theorem dfs_spec (t : Tree) (mn mx : Std.I64) (hval : ValuesIn t 0 100000)
      (hmn : 0 ≤ mn.val) (hmx : mx.val ≤ 100000) (hle : mn.val ≤ mx.val) :
      ∃ r : Std.I64, dfs t mn mx = ok r ∧ r.val = fmax t mn.val mx.val := by
    induction t generalizing mn mx with
    | Null =>
      rw [dfs.eq_def, fmax_null]
      simp only []
      refine I64.sub_eq_ok ?_
      simp only [IScalar.inBounds]
      constructor
      · scalar_tac
      · scalar_tac
    | Node v l r ihl ihr =>
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hval_l : ValuesIn l 0 100000 := fun x hx => hval x (by
        simp only [values, List.mem_cons]
        exact Or.inr (List.mem_append_left _ hx))
      have hval_r : ValuesIn r 0 100000 := fun x hx => hval x (by
        simp only [values, List.mem_cons]
        exact Or.inr (List.mem_append_right _ hx))
      have hm' : (if v < mn then v else mn).val = min mn.val v.val := ite_min_val v mn
      have hx' : (if v > mx then v else mx).val = max mx.val v.val := ite_max_val v mx
      have hle' : min mn.val v.val ≤ max mx.val v.val :=
        le_trans (min_le_left _ _) (le_trans hle (le_max_left _ _))
      obtain ⟨a, ha, hav⟩ :=
        ihl (if v < mn then v else mn) (if v > mx then v else mx) hval_l
          (by rw [hm']; exact le_min hmn hv.1)
          (by rw [hx']; exact max_le hmx hv.2)
          (by rw [hm', hx']; exact hle')
      obtain ⟨b, hb, hbv⟩ :=
        ihr (if v < mn then v else mn) (if v > mx then v else mx) hval_r
          (by rw [hm']; exact le_min hmn hv.1)
          (by rw [hx']; exact max_le hmx hv.2)
          (by rw [hm', hx']; exact hle')
      have hav' : a.val = fmax l (min mn.val v.val) (max mx.val v.val) := by
        rw [hav, hm', hx']
      have hbv' : b.val = fmax r (min mn.val v.val) (max mx.val v.val) := by
        rw [hbv, hm', hx']
      rw [dfs_node_ok v l r mn mx a b ha hb]
      refine ⟨if a > b then a else b, rfl, ?_⟩
      rw [ite_max_val', hav', hbv', fmax_node]

  /-! #### Specification of `max_ancestor_diff` at a node -/

  theorem mad_node (v : Std.I64) (l r : Tree) (res : Std.I64)
      (hval : ValuesIn (.Node v l r) 0 100000)
      (hres : max_ancestor_diff (.Node v l r) = ok res) :
      res.val = fmax (.Node v l r) v.val v.val := by
    have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
    have hval_l : ValuesIn l 0 100000 := fun x hx => hval x (by
      simp only [values, List.mem_cons]
      exact Or.inr (List.mem_append_left _ hx))
    have hval_r : ValuesIn r 0 100000 := fun x hx => hval x (by
      simp only [values, List.mem_cons]
      exact Or.inr (List.mem_append_right _ hx))
    obtain ⟨a, ha, hav⟩ := dfs_spec l v v hval_l hv.1 hv.2 le_rfl
    obtain ⟨b, hb, hbv⟩ := dfs_spec r v v hval_r hv.1 hv.2 le_rfl
    have hres' : res = if a > b then a else b := by
      rw [mad_node_ok v a b l r ha hb] at hres
      exact (Result.ok_injective hres).symm
    rw [hres', ite_max_val', hav, hbv, fmax_node]
    simp

  /-! #### Monotonicity of `fmax` -/

  theorem fmax_mono (t : Tree) :
      ∀ (mn mn' mx mx' : Int), mn' ≤ mn → mx ≤ mx' →
        fmax t mn mx ≤ fmax t mn' mx' := by
    induction t with
    | Null =>
      intro mn mn' mx mx' h1 h2
      simp only [fmax_null]
      omega
    | Node v l r ihl ihr =>
      intro mn mn' mx mx' h1 h2
      simp only [fmax_node]
      apply max_le_max
      · exact ihl _ _ _ _ (min_le_min h1 le_rfl) (max_le_max h2 le_rfl)
      · exact ihr _ _ _ _ (min_le_min h1 le_rfl) (max_le_max h2 le_rfl)

  theorem fmax_ge_sub (t : Tree) :
      ∀ (mn mx : Int), mn ≤ mx → mx - mn ≤ fmax t mn mx := by
    induction t with
    | Null =>
      intro mn mx h
      simp only [fmax_null]
      omega
    | Node v l r ihl ihr =>
      intro mn mx h
      simp only [fmax_node]
      have hmin : min mn v.val ≤ mn := min_le_left _ _
      have hmax : mx ≤ max mx v.val := le_max_left _ _
      have h1 : min mn v.val ≤ max mx v.val :=
        le_trans hmin (le_trans h (le_max_left _ _))
      have hunion : mx - mn ≤ max mx v.val - min mn v.val := by omega
      exact le_trans hunion (le_trans (ihl _ _ h1) (le_max_left _ _))

  /-! #### Grafting a leaf -/

  theorem fmax_add_leaf (w : Std.I64) (t : Tree) :
      ∀ t', AddLeafAt w t t' → ∀ mn mx, mn ≤ mx → fmax t mn mx ≤ fmax t' mn mx := by
    induction t with
    | Null =>
      intro t' h mn mx hle
      simp only [AddLeafAt] at h
    | Node v l r ihl ihr =>
      intro t' h mn mx hle
      simp only [AddLeafAt] at h
      have h1 : min mn v.val ≤ max mx v.val :=
        le_trans (min_le_left _ _) (le_trans hle (le_max_left _ _))
      rcases h with ⟨hl, rfl⟩ | ⟨hr, rfl⟩ | ⟨l', hl', rfl⟩ | ⟨r', hr', rfl⟩
      · subst hl
        show max (fmax .Null (min mn v.val) (max mx v.val))
            (fmax r (min mn v.val) (max mx v.val))
          ≤ max (fmax (.Node w .Null .Null) (min mn v.val) (max mx v.val))
              (fmax r (min mn v.val) (max mx v.val))
        apply max_le
        · exact le_trans (fmax_ge_sub _ _ _ h1) (le_max_left _ _)
        · exact le_max_right _ _
      · subst hr
        show max (fmax l (min mn v.val) (max mx v.val))
            (fmax .Null (min mn v.val) (max mx v.val))
          ≤ max (fmax l (min mn v.val) (max mx v.val))
              (fmax (.Node w .Null .Null) (min mn v.val) (max mx v.val))
        apply max_le
        · exact le_max_left _ _
        · exact le_trans (fmax_ge_sub _ _ _ h1) (le_max_right _ _)
      · show max (fmax l (min mn v.val) (max mx v.val))
            (fmax r (min mn v.val) (max mx v.val))
          ≤ max (fmax l' (min mn v.val) (max mx v.val))
              (fmax r (min mn v.val) (max mx v.val))
        apply max_le
        · exact le_trans (ihl l' hl' _ _ h1) (le_max_left _ _)
        · exact le_max_right _ _
      · show max (fmax l (min mn v.val) (max mx v.val))
            (fmax r (min mn v.val) (max mx v.val))
          ≤ max (fmax l (min mn v.val) (max mx v.val))
              (fmax r' (min mn v.val) (max mx v.val))
        apply max_le
        · exact le_max_left _ _
        · exact le_trans (ihr r' hr' _ _ h1) (le_max_right _ _)

  /-! #### Values of a grafted tree -/

  theorem addLeafAt_values (w : Std.I64) :
      ∀ (t t' : Tree), AddLeafAt w t t' → ∀ x, x ∈ values t' → x ∈ values t ∨ x = w.val := by
    intro t
    induction t with
    | Null =>
      intro t' h
      simp only [AddLeafAt] at h
    | Node v l r ihl ihr =>
      intro t' h x hx
      simp only [AddLeafAt] at h
      rcases h with ⟨hl, rfl⟩ | ⟨hr, rfl⟩ | ⟨l', hl', rfl⟩ | ⟨r', hr', rfl⟩
      · subst hl
        simp only [values, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false, List.mem_singleton, false_or] at hx ⊢
        tauto
      · subst hr
        simp only [values, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false, List.mem_singleton, false_or] at hx ⊢
        tauto
      · simp only [values, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases List.mem_append.mp hx with hx | hx
          · rcases ihl l' hl' x hx with hx | hx
            · exact Or.inl (Or.inr (List.mem_append_left _ hx))
            · exact Or.inr hx
          · exact Or.inl (Or.inr (List.mem_append_right _ hx))
      · simp only [values, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl (Or.inr (List.mem_append_left _ hx))
          · rcases ihr r' hr' x hx with hx | hx
            · exact Or.inl (Or.inr (List.mem_append_right _ hx))
            · exact Or.inr hx

  theorem ValuesIn.addLeafAt {t t' : Tree} {w : Std.I64} {lo hi : Int}
      (hg : AddLeafAt w t t') (h : ValuesIn t lo hi) (h1 : lo ≤ w.val) (h2 : w.val ≤ hi) :
      ValuesIn t' lo hi := by
    intro x hx
    rcases addLeafAt_values w t t' hg x hx with h' | h'
    · exact h x h'
    · subst h'
      exact ⟨h1, h2⟩

  /-** spec_S13 [relational]: attaching one new leaf at a null child pointer can only increase
  the result. -/
  theorem spec_13 (root root_plus : Tree) (w : Std.I64)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hw : 0 ≤ w.val ∧ w.val ≤ 100000)
      (hgraft : AddLeafAt w root root_plus)
      (hsize_plus : size root_plus ≤ 5000) :
      ∀ res res_plus : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root_plus = ok res_plus → res.val ≤ res_plus.val := by
    intro res res_plus hres hres_plus
    cases root with
    | Null =>
      simp only [size] at hsize_lo
      omega
    | Node v l r =>
      have hgraft0 : AddLeafAt w (.Node v l r) root_plus := hgraft
      have hroot : res.val = fmax (.Node v l r) v.val v.val := mad_node v l r res hval hres
      have hmono : fmax (.Node v l r) v.val v.val ≤ fmax root_plus v.val v.val :=
        fmax_add_leaf w (.Node v l r) root_plus hgraft0 v.val v.val le_rfl
      simp only [AddLeafAt] at hgraft
      rcases hgraft with ⟨hl, rfl⟩ | ⟨hr, rfl⟩ | ⟨l', hl', rfl⟩ | ⟨r', hr', rfl⟩
      · subst hl
        have hval_plus : ValuesIn (.Node v (.Node w .Null .Null) r) 0 100000 :=
          ValuesIn.addLeafAt hgraft0 hval hw.1 hw.2
        have hplus : res_plus.val = fmax (.Node v (.Node w .Null .Null) r) v.val v.val :=
          mad_node v (.Node w .Null .Null) r res_plus hval_plus hres_plus
        rw [hroot, hplus]
        exact hmono
      · subst hr
        have hval_plus : ValuesIn (.Node v l (.Node w .Null .Null)) 0 100000 :=
          ValuesIn.addLeafAt hgraft0 hval hw.1 hw.2
        have hplus : res_plus.val = fmax (.Node v l (.Node w .Null .Null)) v.val v.val :=
          mad_node v l (.Node w .Null .Null) res_plus hval_plus hres_plus
        rw [hroot, hplus]
        exact hmono
      · have hval_plus : ValuesIn (.Node v l' r) 0 100000 :=
          ValuesIn.addLeafAt hgraft0 hval hw.1 hw.2
        have hplus : res_plus.val = fmax (.Node v l' r) v.val v.val :=
          mad_node v l' r res_plus hval_plus hres_plus
        rw [hroot, hplus]
        exact hmono
      · have hval_plus : ValuesIn (.Node v l r') 0 100000 :=
          ValuesIn.addLeafAt hgraft0 hval hw.1 hw.2
        have hplus : res_plus.val = fmax (.Node v l r') v.val v.val :=
          mad_node v l r' res_plus hval_plus hres_plus
        rw [hroot, hplus]
        exact hmono

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
