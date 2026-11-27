import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_5` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary results for `spec_S5` -/

  /-- The value of an `I64` subtraction, when it succeeds. -/
  lemma I64.sub_val_eq {x y z : Std.I64} (h : x - y = ok z)
      (hx : 0 ≤ x.val) (hx2 : x.val ≤ 100000) (hy : 0 ≤ y.val) (hy2 : y.val ≤ 100000) :
      z.val = x.val - y.val := by
    have hmin : IScalar.min IScalarTy.I64 ≤ x.val - y.val := by scalar_tac
    have hmax : x.val - y.val ≤ IScalar.max IScalarTy.I64 := by scalar_tac
    have hs : x - y ⦃ z => z.val = x.val - y.val ⦄ := IScalar.sub_spec hmin hmax
    rw [h] at hs
    simpa using hs

  /-- Correctness of `dfs` with respect to the ancestor pairs: the value it returns dominates
  `|a - b|` for every proper ancestor value `a` (from `acc`) and every node value `b` of `t`, and
  it is at least `mx - mn`. -/
  lemma dfs_aux (t : Tree) :
      ∀ (mn mx res : Std.I64) (acc : List Int), dfs t mn mx = ok res →
        ValuesIn t 0 100000 →
        (∀ a ∈ acc, mn.val ≤ a ∧ a ≤ mx.val) →
        0 ≤ mn.val → mn.val ≤ 100000 → 0 ≤ mx.val → mx.val ≤ 100000 →
        (mx.val - mn.val ≤ res.val) ∧ ∀ p ∈ ancPairsAux acc t, absDiff p.1 p.2 ≤ res.val := by
    induction t with
    | Null =>
      intro mn mx res acc hdes hval hacc h1 h2 h3 h4
      rw [dfs.eq_1] at hdes
      have hsub : res.val = mx.val - mn.val := I64.sub_val_eq hdes h3 h4 h1 h2
      refine ⟨by rw [hsub], ?_⟩
      intro p hp
      simp [ancPairsAux] at hp
    | Node v l r ihl ihr =>
      intro mn mx res acc hdes hval hacc h1 h2 h3 h4
      obtain ⟨hv1, hv2⟩ : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hlv : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hrv : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hmn'ok : (if v < mn then ok v else ok mn) = ok (if v < mn then v else mn) := by
        by_cases h : v < mn <;> simp [h]
      have hmx'ok : (if v > mx then ok v else ok mx) = ok (if v > mx then v else mx) := by
        by_cases h : v > mx <;> simp [h]
      rw [dfs.eq_2] at hdes
      rw [hmn'ok, hmx'ok] at hdes
      simp only [bind_ok] at hdes
      set mn' : Std.I64 := (if v < mn then v else mn) with hmn'def
      set mx' : Std.I64 := (if v > mx then v else mx) with hmx'def
      have hmn'v : mn'.val = min v.val mn.val := by
        rw [hmn'def]
        by_cases h : v < mn
        · rw [if_pos h]
          have h' : v.val < mn.val := by simpa using h
          exact (min_eq_left (le_of_lt h')).symm
        · rw [if_neg h]
          have h' : ¬ v.val < mn.val := by simpa using h
          exact (min_eq_right (not_lt.mp h')).symm
      have hmx'v : mx'.val = max v.val mx.val := by
        rw [hmx'def]
        by_cases h : v > mx
        · rw [if_pos h]
          have h' : mx.val < v.val := by simpa using h
          exact (max_eq_left (le_of_lt h')).symm
        · rw [if_neg h]
          have h' : ¬ mx.val < v.val := by simpa using h
          exact (max_eq_right (not_lt.mp h')).symm
      have hmn'lo : 0 ≤ mn'.val := by rw [hmn'v]; exact le_min hv1 h1
      have hmn'hi : mn'.val ≤ 100000 := by rw [hmn'v]; exact le_trans (min_le_right _ _) h2
      have hmx'lo : 0 ≤ mx'.val := by rw [hmx'v]; exact le_trans h3 (le_max_right _ _)
      have hmx'hi : mx'.val ≤ 100000 := by rw [hmx'v]; exact max_le hv2 h4
      have hacc' : ∀ a ∈ v.val :: acc, mn'.val ≤ a ∧ a ≤ mx'.val := by
        intro a ha
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ⟨by rw [hmn'v]; exact min_le_left _ _,
                 by rw [hmx'v]; exact le_max_left _ _⟩
        · obtain ⟨ha1, ha2⟩ := hacc a ha
          exact ⟨le_trans (by rw [hmn'v]; exact min_le_right _ _) ha1,
                 le_trans ha2 (by rw [hmx'v]; exact le_max_right _ _)⟩
      cases hla : dfs l mn' mx' with
      | ret a =>
        rw [hla] at hdes
        simp only [bind_ok] at hdes
        cases hrb : dfs r mn' mx' with
        | ret b =>
          rw [hrb] at hdes
          simp only [bind_ok] at hdes
          obtain ⟨hbasel, hpairl⟩ :=
            ihl mn' mx' a (v.val :: acc) hla hlv hacc' hmn'lo hmn'hi hmx'lo hmx'hi
          obtain ⟨_, hpairr⟩ :=
            ihr mn' mx' b (v.val :: acc) hrb hrv hacc' hmn'lo hmn'hi hmx'lo hmx'hi
          have hres : res.val = max a.val b.val := by
            by_cases hgt : a > b
            · rw [if_pos hgt] at hdes
              have heq : a = res := by simpa using hdes
              have h' : b.val < a.val := by simpa using hgt
              rw [← heq, max_eq_left (le_of_lt h')]
            · rw [if_neg hgt] at hdes
              have heq : b = res := by simpa using hdes
              have h' : ¬ b.val < a.val := by simpa using hgt
              rw [← heq, max_eq_right (not_lt.mp h')]
          refine ⟨?_, ?_⟩
          · rw [hres]
            have hstep : mx.val - mn.val ≤ mx'.val - mn'.val := by
              rw [hmn'v, hmx'v]
              have ha := le_max_right v.val mx.val
              have hb := min_le_right v.val mn.val
              omega
            exact le_trans hstep (le_trans hbasel (le_max_left _ _))
          · intro p hp
            rw [hres]
            simp only [ancPairsAux] at hp
            rw [List.mem_append, List.mem_append] at hp
            rcases hp with (hp | hp) | hp
            · rw [List.mem_map] at hp
              obtain ⟨a₀, ha₀, rfl⟩ := hp
              obtain ⟨ha₀1, ha₀2⟩ := hacc a₀ ha₀
              have hsp : absDiff a₀ v.val ≤ mx'.val - mn'.val := by
                rw [hmn'v, hmx'v]
                have hm1 := min_le_left v.val mn.val
                have hm2 := min_le_right v.val mn.val
                have hx1 := le_max_left v.val mx.val
                have hx2 := le_max_right v.val mx.val
                simp only [absDiff]
                apply max_le <;> omega
              exact le_trans hsp (le_trans hbasel (le_max_left _ _))
            · exact le_trans (hpairl p hp) (le_max_left _ _)
            · exact le_trans (hpairr p hp) (le_max_right _ _)
        | vis e k => rw [hrb] at hdes; simp at hdes
        | div => rw [hrb] at hdes; simp at hdes
      | vis e k => rw [hla] at hdes; simp at hdes
      | div => rw [hla] at hdes; simp at hdes

  /-** spec_S5 [relational]: the returned value dominates `|value a - value b|` for every pair of
  nodes `(a, b)` of `root` with `a` a proper ancestor of `b`. -/
  theorem spec_5 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∀ p ∈ ancPairs root, absDiff p.1 p.2 ≤ res.val := by
    intro res hdes
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      obtain ⟨hv1, hv2⟩ : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hlv : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hrv : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      rw [max_ancestor_diff.eq_2] at hdes
      cases hla : dfs l v v with
      | ret a =>
        rw [hla] at hdes
        simp only [bind_ok] at hdes
        cases hrb : dfs r v v with
        | ret b =>
          rw [hrb] at hdes
          simp only [bind_ok] at hdes
          have hacc : ∀ x ∈ [v.val], v.val ≤ x ∧ x ≤ v.val := by
            intro x hx
            rw [List.mem_singleton] at hx
            cases hx
            exact ⟨le_rfl, le_rfl⟩
          obtain ⟨_, hpairl⟩ := dfs_aux l v v a [v.val] hla hlv hacc hv1 hv2 hv1 hv2
          obtain ⟨_, hpairr⟩ := dfs_aux r v v b [v.val] hrb hrv hacc hv1 hv2 hv1 hv2
          have hres : res.val = max a.val b.val := by
            by_cases hgt : a > b
            · rw [if_pos hgt] at hdes
              have heq : a = res := by simpa using hdes
              have h' : b.val < a.val := by simpa using hgt
              rw [← heq, max_eq_left (le_of_lt h')]
            · rw [if_neg hgt] at hdes
              have heq : b = res := by simpa using hdes
              have h' : ¬ b.val < a.val := by simpa using hgt
              rw [← heq, max_eq_right (not_lt.mp h')]
          intro p hp
          rw [hres]
          simp only [ancPairs, ancPairsAux, List.map_nil, List.nil_append, List.mem_append] at hp
          rcases hp with hp | hp
          · exact le_trans (hpairl p hp) (le_max_left _ _)
          · exact le_trans (hpairr p hp) (le_max_right _ _)
        | vis e k => rw [hrb] at hdes; simp at hdes
        | div => rw [hrb] at hdes; simp at hdes
      | vis e k => rw [hla] at hdes; simp at hdes
      | div => rw [hla] at hdes; simp at hdes

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

  /-** spec_C2 [per-node]: the result is the maximum, over all nodes `b`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))` (and `0` for the root). -/
  theorem spec_C2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    sorry

  end AegisSpec.MaxAncestorDiff
