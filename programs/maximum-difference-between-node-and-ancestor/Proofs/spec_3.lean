import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_3` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary lemmas used in the proof of `spec_S3` -/

  theorem foldl_min_le_self (a : Int) (l : List Int) : l.foldl min a ≤ a := by
    induction l generalizing a with
    | nil => simp
    | cons y t ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min a y)) (Int.min_le_left _ _)

  theorem foldl_max_ge_self (a : Int) (l : List Int) : a ≤ l.foldl max a := by
    induction l generalizing a with
    | nil => simp
    | cons y t ih =>
      simp only [List.foldl_cons]
      exact le_trans (Int.le_max_left _ _) (ih (max a y))

  theorem foldl_min_le_of_mem {a x : Int} {l : List Int} (h : x ∈ l) : l.foldl min a ≤ x := by
    induction l generalizing a with
    | nil => simp at h
    | cons y t ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_trans (foldl_min_le_self (min a x) t) (Int.min_le_right _ _)
      · exact ih (a := min a y) h'

  theorem le_foldl_max_of_mem {a x : Int} {l : List Int} (h : x ∈ l) : x ≤ l.foldl max a := by
    induction l generalizing a with
    | nil => simp at h
    | cons y t ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_trans (Int.le_max_right _ _) (foldl_max_ge_self (max a x) t)
      · exact ih (a := max a y) h'

  theorem minVal_le_of_mem {t : Tree} {x : Int} (h : x ∈ values t) : minVal t ≤ x :=
    foldl_min_le_of_mem (a := 100000) h

  theorem le_maxVal_of_mem {t : Tree} {x : Int} (h : x ∈ values t) : x ≤ maxVal t :=
    le_foldl_max_of_mem (a := 0) h

  /-- Destructuration of a `Result` do-block which returns `ok`: if `bind x f` succeeds then `x`
  itself is an `ok` value. -/
  theorem Result.bind_ok_elim {α β : Type} {x : Std.Result α} {f : α → Std.Result β} {y : β}
      (h : Aeneas.Std.bind x f = Aeneas.Std.Result.ok y) :
      ∃ a, x = Aeneas.Std.Result.ok a ∧ f a = Aeneas.Std.Result.ok y := by
    cases hx : x.match with
    | ok a =>
      have hx' : x = Aeneas.Std.Result.ok a := Aeneas.Std.Result.match.isOk.mp hx
      subst hx'
      have h' : Aeneas.Std.bind (Aeneas.Std.Result.ok a) f = Aeneas.Std.Result.ok y := h
      simp only [Aeneas.Std.bind_ok] at h'
      exact ⟨a, rfl, h'⟩
    | div =>
      have hx' : x = Aeneas.Std.Result.div := Aeneas.Std.Result.match.isDiv.mp hx
      subst hx'
      have h' : Aeneas.Std.bind (Aeneas.Std.Result.div) f = Aeneas.Std.Result.ok y := h
      simp at h'
    | vis e k =>
      have hx' : x = Aeneas.Std.Result.vis e k := Aeneas.Std.Result.match.isVis.mp hx
      subst hx'
      have h' : Aeneas.Std.bind (Aeneas.Std.Result.vis e k) f = Aeneas.Std.Result.ok y := h
      simp at h'

  /-- Value of an `if` whose two branches are `ok` values. -/
  theorem ite_ok_val {c : Prop} [Decidable c] {x y z : Std.I64}
      (h : (if c then Aeneas.Std.Result.ok x else Aeneas.Std.Result.ok y)
        = Aeneas.Std.Result.ok z) :
      z.val = if c then x.val else y.val := by
    by_cases hc : c
    · rw [if_pos hc] at h
      have hz : z = x := by simpa using h.symm
      rw [hz]
      simp [hc]
    · rw [if_neg hc] at h
      have hz : z = y := by simpa using h.symm
      rw [hz]
      simp [hc]

  theorem dfs_null (mn mx : Std.I64) : Aegis.MaxAncestorDiff.dfs .Null mn mx = mx - mn := by
    rw [Aegis.MaxAncestorDiff.dfs.eq_def]

  theorem dfs_node (v : Std.I64) (l r : Tree) (mn mx : Std.I64) :
      Aegis.MaxAncestorDiff.dfs (.Node v l r) mn mx = (do
        let nmn ← if v < mn then ok v else ok mn
        let nmx ← if v > mx then ok v else ok mx
        let a ← Aegis.MaxAncestorDiff.dfs l nmn nmx
        let b ← Aegis.MaxAncestorDiff.dfs r nmn nmx
        if a > b then ok a else ok b) := by
    rw [Aegis.MaxAncestorDiff.dfs.eq_def]

  theorem max_ancestor_diff_node (v : Std.I64) (l r : Tree) :
      Aegis.MaxAncestorDiff.max_ancestor_diff (.Node v l r) = (do
        let a ← Aegis.MaxAncestorDiff.dfs l v v
        let b ← Aegis.MaxAncestorDiff.dfs r v v
        if a > b then ok a else ok b) := by
    rw [Aegis.MaxAncestorDiff.max_ancestor_diff.eq_def]

  /-- If `dfs` succeeds, the returned value lies in `[0, hi - lo]`, where `lo`/`hi` bound the
  carried minimum/maximum and all the node values of the explored subtree. -/
  theorem dfs_bound (t : Tree) (mn mx res : Std.I64) (lo hi : Int)
      (h : Aegis.MaxAncestorDiff.dfs t mn mx = ok res)
      (hlo : lo ≤ mn.val) (hmn : mn.val ≤ mx.val) (hhi : mx.val ≤ hi)
      (ht : ∀ x ∈ values t, lo ≤ x ∧ x ≤ hi) :
      0 ≤ res.val ∧ res.val ≤ hi - lo := by
    induction t generalizing mn mx res lo hi with
    | Null =>
      rw [dfs_null] at h
      have hh : (mx - mn).match = Aeneas.Std.MatchResult.ok res := by rw [h]; simp
      have hs := IScalar.sub_equiv mx mn
      rw [hh] at hs
      have hres : res.val = mx.val - mn.val := hs.2.1
      constructor <;> omega
    | Node v l r ihl ihr =>
      have hvdef : values (.Node v l r) = v.val :: (values l ++ values r) := rfl
      have hmemv : v.val ∈ values (.Node v l r) := by
        rw [hvdef]; exact List.mem_cons_self
      have hv : lo ≤ v.val ∧ v.val ≤ hi := ht v.val hmemv
      have htl : ∀ x ∈ values l, lo ≤ x ∧ x ≤ hi := by
        intro x hx
        exact ht x (by rw [hvdef]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have htr : ∀ x ∈ values r, lo ≤ x ∧ x ≤ hi := by
        intro x hx
        exact ht x (by rw [hvdef]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      rw [dfs_node] at h
      obtain ⟨nmn, hnmn, h1⟩ := Result.bind_ok_elim h
      obtain ⟨nmx, hnmx, h2⟩ := Result.bind_ok_elim h1
      obtain ⟨a, ha, h3⟩ := Result.bind_ok_elim h2
      obtain ⟨b, hb, h4⟩ := Result.bind_ok_elim h3
      have hnmn_val : nmn.val = if v < mn then v.val else mn.val := ite_ok_val hnmn
      have hnmx_val : nmx.val = if v > mx then v.val else mx.val := ite_ok_val hnmx
      have hA : lo ≤ nmn.val := by
        rw [hnmn_val]; split <;> omega
      have hB : nmn.val ≤ nmx.val := by
        rw [hnmn_val, hnmx_val]; split <;> split <;> scalar_tac
      have hC : nmx.val ≤ hi := by
        rw [hnmx_val]; split <;> omega
      have ha' := ihl nmn nmx a lo hi ha hA hB hC htl
      have hb' := ihr nmn nmx b lo hi hb hA hB hC htr
      by_cases hab : a > b
      · rw [if_pos hab] at h4
        have hres : res = a := by simpa using h4.symm
        rw [hres]
        exact ha'
      · rw [if_neg hab] at h4
        have hres : res = b := by simpa using h4.symm
        rw [hres]
        exact hb'

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
  theorem spec_3 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        0 ≤ res.val ∧ res.val ≤ maxVal root - minVal root := by
    intro res h
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      rw [max_ancestor_diff_node] at h
      obtain ⟨a, ha, h1⟩ := Result.bind_ok_elim h
      obtain ⟨b, hb, h2⟩ := Result.bind_ok_elim h1
      have hvdef : values (.Node v l r) = v.val :: (values l ++ values r) := rfl
      have hmemv : v.val ∈ values (.Node v l r) := by
        rw [hvdef]; exact List.mem_cons_self
      have hlo : minVal (.Node v l r) ≤ v.val := minVal_le_of_mem hmemv
      have hhi : v.val ≤ maxVal (.Node v l r) := le_maxVal_of_mem hmemv
      have htl : ∀ x ∈ values l, minVal (.Node v l r) ≤ x ∧ x ≤ maxVal (.Node v l r) := by
        intro x hx
        have hmem : x ∈ values (.Node v l r) := by
          rw [hvdef]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
        exact ⟨minVal_le_of_mem hmem, le_maxVal_of_mem hmem⟩
      have htr : ∀ x ∈ values r, minVal (.Node v l r) ≤ x ∧ x ≤ maxVal (.Node v l r) := by
        intro x hx
        have hmem : x ∈ values (.Node v l r) := by
          rw [hvdef]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)
        exact ⟨minVal_le_of_mem hmem, le_maxVal_of_mem hmem⟩
      have hb_l := dfs_bound l v v a (minVal (.Node v l r)) (maxVal (.Node v l r))
        ha hlo (le_refl v.val) hhi htl
      have hb_r := dfs_bound r v v b (minVal (.Node v l r)) (maxVal (.Node v l r))
        hb hlo (le_refl v.val) hhi htr
      by_cases hab : a > b
      · rw [if_pos hab] at h2
        have hres : res = a := by simpa using h2.symm
        rw [hres]
        exact hb_l
      · rw [if_neg hab] at h2
        have hres : res = b := by simpa using h2.symm
        rw [hres]
        exact hb_r

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

  /-** spec_C2 [per-node]: the result is the maximum, over all nodes `b`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))` (and `0` for the root). -/
  theorem spec_C2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    sorry

  end AegisSpec.MaxAncestorDiff
