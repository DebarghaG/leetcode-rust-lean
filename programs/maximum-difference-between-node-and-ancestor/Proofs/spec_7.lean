import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_7` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary lemmas for `spec_S7` -/

  lemma values_node (v : Std.I64) (l r : Tree) :
      values (Tree.Node v l r) = v.val :: (values l ++ values r) := rfl

  lemma values_null : values Tree.Null = [] := rfl

  lemma ValuesIn_node {v : Std.I64} {l r : Tree} {lo hi : Int}
      (h : ValuesIn (Tree.Node v l r) lo hi) :
      (lo ≤ v.val ∧ v.val ≤ hi) ∧ ValuesIn l lo hi ∧ ValuesIn r lo hi := by
    refine ⟨h v.val (by simp [values_node]), ?_, ?_⟩
    · intro x hx
      exact h x (by simp [values_node, hx])
    · intro x hx
      exact h x (by simp [values_node, hx])

  lemma le_foldl_max : ∀ (l : List Int) (a b : Int), a ≤ b → a ≤ l.foldl max b
    | [], _, b, h => h
    | c :: l, a, b, h => le_foldl_max l a (max b c) (le_trans h (le_max_left b c))

  lemma foldl_max_eq (l : List Int) (a : Int) (h : 0 ≤ a) :
      l.foldl max a = max a (l.foldl max 0) := by
    induction l generalizing a with
    | nil => exact (max_eq_left h).symm
    | cons b l ih =>
      have e1 : l.foldl max (max a b) = max (max a b) (l.foldl max 0) :=
        ih (max a b) (le_trans h (le_max_left a b))
      have e2 : l.foldl max (max 0 b) = max (max 0 b) (l.foldl max 0) :=
        ih (max 0 b) (le_max_left 0 b)
      simp only [List.foldl_cons, e1, e2]
      rcases lt_or_ge (0 : Int) b with hb | hb
      · have h2 : max 0 b = b := max_eq_right (le_of_lt hb)
        rw [h2]
        exact max_assoc a b _
      · have h1 : max a b = a := max_eq_left (le_trans hb h)
        have h2 : max 0 b = 0 := max_eq_left hb
        rw [h1, h2]
        have hM : 0 ≤ l.foldl max 0 := le_foldl_max l 0 0 le_rfl
        conv_rhs => rw [max_eq_right hM]

  lemma listMax_nonneg (l : List Int) : 0 ≤ listMax l := le_foldl_max l 0 0 le_rfl

  lemma listMax_cons (a : Int) (l : List Int) (h : 0 ≤ a) :
      listMax (a :: l) = max a (listMax l) := by
    unfold listMax
    rw [List.foldl_cons, max_eq_right h]
    exact foldl_max_eq l a h

  lemma foldl_min_le : ∀ (l : List Int) (a b : Int), b ≤ a → l.foldl min b ≤ a
    | [], _, b, h => h
    | c :: l, a, b, h => foldl_min_le l a (min b c) (le_trans (min_le_left b c) h)

  lemma foldl_min_eq (l : List Int) (a : Int) (h : a ≤ 100000) :
      l.foldl min a = min a (l.foldl min 100000) := by
    induction l generalizing a with
    | nil => exact (min_eq_left h).symm
    | cons b l ih =>
      have e1 : l.foldl min (min a b) = min (min a b) (l.foldl min 100000) :=
        ih (min a b) (le_trans (min_le_left a b) h)
      have e2 : l.foldl min (min 100000 b) = min (min 100000 b) (l.foldl min 100000) :=
        ih (min 100000 b) (min_le_left 100000 b)
      simp only [List.foldl_cons, e1, e2]
      rcases lt_or_ge b (100000 : Int) with hb | hb
      · have h2 : min 100000 b = b := min_eq_right (le_of_lt hb)
        rw [h2]
        exact min_assoc a b _
      · have h1 : min a b = a := min_eq_left (le_trans h hb)
        have h2 : min 100000 b = 100000 := min_eq_left hb
        rw [h1, h2]
        have hM : l.foldl min 100000 ≤ 100000 := foldl_min_le l 100000 100000 le_rfl
        conv_rhs => rw [min_eq_right hM]

  lemma listMin_le (l : List Int) : listMin l ≤ 100000 := foldl_min_le l 100000 100000 le_rfl

  lemma listMin_cons (a : Int) (l : List Int) (h : a ≤ 100000) :
      listMin (a :: l) = min a (listMin l) := by
    unfold listMin
    rw [List.foldl_cons, min_eq_right h]
    exact foldl_min_eq l a h

  lemma ite_min_val (v mn : Std.I64) :
      WP.spec (if v < mn then ok v else ok mn) (fun r => r.val = min mn.val v.val) := by
    by_cases h : v < mn
    · rw [if_pos h, WP.spec_ok]
      have h' : v.val < mn.val := h
      exact (min_eq_right (le_of_lt h')).symm
    · rw [if_neg h, WP.spec_ok]
      have h' : mn.val ≤ v.val := not_lt.mp h
      exact (min_eq_left h').symm

  lemma ite_max_val (v mx : Std.I64) :
      WP.spec (if v > mx then ok v else ok mx) (fun r => r.val = max mx.val v.val) := by
    by_cases h : v > mx
    · rw [if_pos h, WP.spec_ok]
      have h' : mx.val < v.val := h
      exact (max_eq_right (le_of_lt h')).symm
    · rw [if_neg h, WP.spec_ok]
      have h' : v.val ≤ mx.val := not_lt.mp h
      exact (max_eq_left h').symm

  lemma ite_branch_val (a b : Std.I64) :
      WP.spec (if a > b then ok a else ok b) (fun r => r.val = max a.val b.val) := by
    by_cases h : a > b
    · rw [if_pos h, WP.spec_ok]
      have h' : b.val < a.val := h
      exact (max_eq_left (le_of_lt h')).symm
    · rw [if_neg h, WP.spec_ok]
      have h' : a.val ≤ b.val := not_lt.mp h
      exact (max_eq_right h').symm

  /-- `WP.spec` form implies the `∀ res, f = ok res → _` form. -/
  lemma spec_apply {m : Result Std.I64} {Q : Int → Prop} (h : WP.spec m (fun r => Q r.val))
      (res : Std.I64) (hr : m = ok res) : Q res.val := by
    rw [hr] at h
    rw [WP.spec_ok] at h
    exact h

  set_option maxHeartbeats 1000000 in
  /-- The `dfs` computation on a chain: it returns `max mx (maxVal t) - min mn (minVal t)`. -/
  lemma dfs_chain_spec (t : Tree) (mn mx : Std.I64)
      (hchain : IsChain t) (hval : ValuesIn t 0 100000)
      (hmn0 : 0 ≤ mn.val) (hmnle : mn.val ≤ mx.val) (hmx1 : mx.val ≤ 100000) :
      WP.spec (dfs t mn mx) (fun res => res.val = max mx.val (maxVal t) - min mn.val (minVal t)) := by
    induction t generalizing mn mx with
    | Null =>
      rw [dfs.eq_1]
      have hgoal : max mx.val (maxVal Tree.Null) - min mn.val (minVal Tree.Null) = mx.val - mn.val := by
        have h0 : 0 ≤ mx.val := le_trans hmn0 hmnle
        have h1 : mn.val ≤ 100000 := le_trans hmnle hmx1
        have e1 : maxVal Tree.Null = 0 := rfl
        have e2 : minVal Tree.Null = 100000 := rfl
        rw [e1, e2, max_eq_left h0, min_eq_left h1]
      rw [hgoal]
      step
      assumption
    | Node v l r ihl ihr =>
      obtain ⟨hsep, hcl, hcr⟩ := hchain
      obtain ⟨⟨hv0, hv1⟩, hval_l, hval_r⟩ := ValuesIn_node hval
      rw [dfs.eq_def]
      simp only [Std.bind, Result.ok]
      show WP.spec (Std.bind (if v < mn then Result.ok v else Result.ok mn) (fun nmn =>
            Std.bind (if v > mx then Result.ok v else Result.ok mx) (fun nmx =>
              Std.bind (dfs l nmn nmx) (fun a =>
                Std.bind (dfs r nmn nmx) (fun b =>
                  if a > b then Result.ok a else Result.ok b)))))
          (fun res => res.val = max mx.val (maxVal (Tree.Node v l r)) - min mn.val (minVal (Tree.Node v l r)))
      refine WP.spec_bind (m := (if v < mn then Result.ok v else Result.ok mn))
        (Pₘ := fun x => x.val = min mn.val v.val) (ite_min_val v mn) ?_
      intro nmn hnmn
      refine WP.spec_bind (m := (if v > mx then Result.ok v else Result.ok mx))
        (Pₘ := fun x => x.val = max mx.val v.val) (ite_max_val v mx) ?_
      intro nmx hnmx
      have hnmn0 : 0 ≤ nmn.val := by rw [hnmn]; omega
      have hnmx1 : nmx.val ≤ 100000 := by rw [hnmx]; omega
      have hle' : nmn.val ≤ nmx.val := by rw [hnmn, hnmx]; omega
      refine WP.spec_bind (m := dfs l nmn nmx)
        (Pₘ := fun x => x.val = max nmx.val (maxVal l) - min nmn.val (minVal l))
        (ihl nmn nmx hcl hval_l hnmn0 hle' hnmx1) ?_
      intro a ha
      refine WP.spec_bind (m := dfs r nmn nmx)
        (Pₘ := fun x => x.val = max nmx.val (maxVal r) - min nmn.val (minVal r))
        (ihr nmn nmx hcr hval_r hnmn0 hle' hnmx1) ?_
      intro b hb
      refine WP.spec_mono (ite_branch_val a b) ?_
      intro res hres
      rcases hsep with hl | hr
      · subst hl
        have hmaxVal : maxVal (Tree.Node v Tree.Null r) = max v.val (maxVal r) := by
          unfold maxVal
          rw [values_node, listMax_cons _ _ hv0]
          rfl
        have hminVal : minVal (Tree.Node v Tree.Null r) = min v.val (minVal r) := by
          unfold minVal
          rw [values_node, listMin_cons _ _ hv1]
          rfl
        have ha' : a.val = nmx.val - nmn.val := by
          rw [ha]
          have e1 : maxVal Tree.Null = 0 := rfl
          have e2 : minVal Tree.Null = 100000 := rfl
          rw [e1, e2, max_eq_left (le_trans hnmn0 hle'), min_eq_left (le_trans hle' hnmx1)]
        have e1 : max mx.val (max v.val (maxVal r)) = max nmx.val (maxVal r) := by
          rw [← max_assoc, ← hnmx]
        have e2 : min mn.val (min v.val (minVal r)) = min nmn.val (minVal r) := by
          rw [← min_assoc, ← hnmn]
        rw [hmaxVal, hminVal, e1, e2, hres, hb, ha']
        omega
      · subst hr
        have hmaxVal : maxVal (Tree.Node v l Tree.Null) = max v.val (maxVal l) := by
          unfold maxVal
          rw [values_node, listMax_cons _ _ hv0]
          rw [values_null, List.append_nil]
        have hminVal : minVal (Tree.Node v l Tree.Null) = min v.val (minVal l) := by
          unfold minVal
          rw [values_node, listMin_cons _ _ hv1]
          rw [values_null, List.append_nil]
        have hb' : b.val = nmx.val - nmn.val := by
          rw [hb]
          have e1 : maxVal Tree.Null = 0 := rfl
          have e2 : minVal Tree.Null = 100000 := rfl
          rw [e1, e2, max_eq_left (le_trans hnmn0 hle'), min_eq_left (le_trans hle' hnmx1)]
        have e1 : max mx.val (max v.val (maxVal l)) = max nmx.val (maxVal l) := by
          rw [← max_assoc, ← hnmx]
        have e2 : min mn.val (min v.val (minVal l)) = min nmn.val (minVal l) := by
          rw [← min_assoc, ← hnmn]
        rw [hmaxVal, hminVal, e1, e2, hres, ha, hb']
        omega

  set_option maxHeartbeats 1000000 in
  /-- `max_ancestor_diff` on a chain returns `maxVal root - minVal root`. -/
  lemma max_ancestor_diff_chain_spec (root : Tree) (hchain : IsChain root)
      (hval : ValuesIn root 0 100000) (hpos : 1 ≤ size root) :
      WP.spec (max_ancestor_diff root) (fun res => res.val = maxVal root - minVal root) := by
    cases root with
    | Null => simp [size] at hpos
    | Node v l r =>
      obtain ⟨hsep, hcl, hcr⟩ := hchain
      obtain ⟨⟨hv0, hv1⟩, hval_l, hval_r⟩ := ValuesIn_node hval
      rw [max_ancestor_diff.eq_def]
      simp only [Std.bind, Result.ok]
      show WP.spec (Std.bind (dfs l v v) (fun a =>
              Std.bind (dfs r v v) (fun b =>
                if a > b then Result.ok a else Result.ok b)))
          (fun res => res.val = maxVal (Tree.Node v l r) - minVal (Tree.Node v l r))
      refine WP.spec_bind (m := dfs l v v)
        (Pₘ := fun x => x.val = max v.val (maxVal l) - min v.val (minVal l))
        (dfs_chain_spec l v v hcl hval_l hv0 le_rfl hv1) ?_
      intro a ha
      refine WP.spec_bind (m := dfs r v v)
        (Pₘ := fun x => x.val = max v.val (maxVal r) - min v.val (minVal r))
        (dfs_chain_spec r v v hcr hval_r hv0 le_rfl hv1) ?_
      intro b hb
      refine WP.spec_mono (ite_branch_val a b) ?_
      intro res hres
      rcases hsep with hl | hr
      · subst hl
        have hmaxVal : maxVal (Tree.Node v Tree.Null r) = max v.val (maxVal r) := by
          unfold maxVal
          rw [values_node, listMax_cons _ _ hv0]
          rfl
        have hminVal : minVal (Tree.Node v Tree.Null r) = min v.val (minVal r) := by
          unfold minVal
          rw [values_node, listMin_cons _ _ hv1]
          rfl
        have ha0 : a.val = 0 := by
          rw [ha]
          have e1 : maxVal Tree.Null = 0 := rfl
          have e2 : minVal Tree.Null = 100000 := rfl
          rw [e1, e2, max_eq_left hv0, min_eq_left hv1]
          omega
        rw [hmaxVal, hminVal, hres, ha0, hb]
        omega
      · subst hr
        have hmaxVal : maxVal (Tree.Node v l Tree.Null) = max v.val (maxVal l) := by
          unfold maxVal
          rw [values_node, listMax_cons _ _ hv0]
          rw [values_null, List.append_nil]
        have hminVal : minVal (Tree.Node v l Tree.Null) = min v.val (minVal l) := by
          unfold minVal
          rw [values_node, listMin_cons _ _ hv1]
          rw [values_null, List.append_nil]
        have hb0 : b.val = 0 := by
          rw [hb]
          have e1 : maxVal Tree.Null = 0 := rfl
          have e2 : minVal Tree.Null = 100000 := rfl
          rw [e1, e2, max_eq_left hv0, min_eq_left hv1]
          omega
        rw [hmaxVal, hminVal, hres, ha, hb0]
        omega

  /-** spec_S7 [shape]: on a chain, the result is `maxVal(root) - minVal(root)`. -/
  theorem spec_7 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) (hchain : IsChain root) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = maxVal root - minVal root := by
    intro res hres
    have h := max_ancestor_diff_chain_spec root hchain hval (by omega)
    rw [hres] at h
    rw [WP.spec_ok] at h
    exact h

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
