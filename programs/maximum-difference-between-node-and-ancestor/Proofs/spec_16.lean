import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_16` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary definitions and lemmas used for `spec_C1` -/

  /-- The lists of node values on the paths `dfs` walks: `acc` holds the values on the path to the
  current node (current node excluded); one list is produced for every null child reached. -/
  def nullPathsAux (acc : List Int) : Tree → List (List Int)
    | .Null => [acc]
    | .Node v l r => nullPathsAux (acc ++ [v.val]) l ++ nullPathsAux (acc ++ [v.val]) r

  /-- The value computed by `dfs`, as an integer recursion (no overflow, no `Result`). -/
  def dfsI : Tree → Int → Int → Int
    | .Null, mn, mx => mx - mn
    | .Node v l r, mn, mx =>
      max (dfsI l (min mn v.val) (max mx v.val)) (dfsI r (min mn v.val) (max mx v.val))

  /-- Maximum of `pathSpread` over a list of paths (`0` for the empty list). -/
  def foldSpread (L : List (List Int)) : Int :=
    L.foldr (fun p a => max (pathSpread p) a) 0

  /-! #### Lemmas about `listMax` / `listMin` -/

  theorem foldl_max_push (l : List Int) (y : Int) :
      List.foldl max (max 0 y) l = max y (List.foldl max 0 l) := by
    induction l generalizing y with
    | nil => simp only [List.foldl_nil, max_comm]
    | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [show max (max 0 y) c = max 0 (max y c) from by omega, ih, ih c]
      omega

  theorem foldl_min_push (l : List Int) (y : Int) :
      List.foldl min (min 100000 y) l = min y (List.foldl min 100000 l) := by
    induction l generalizing y with
    | nil => simp only [List.foldl_nil, min_comm]
    | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [show min (min 100000 y) c = min 100000 (min y c) from by omega, ih, ih c]
      omega

  theorem listMax_cons (c : Int) (l : List Int) : listMax (c :: l) = max c (listMax l) :=
    foldl_max_push l c

  theorem listMin_cons (c : Int) (l : List Int) : listMin (c :: l) = min c (listMin l) :=
    foldl_min_push l c

  theorem zero_le_listMax (l : List Int) : 0 ≤ listMax l := by
    induction l with
    | nil => simp [listMax]
    | cons c cs ih => rw [listMax_cons]; omega

  theorem listMin_le_bound (l : List Int) : listMin l ≤ 100000 := by
    induction l with
    | nil => simp [listMin]
    | cons c cs ih => rw [listMin_cons]; omega

  theorem listMax_append (a b : List Int) : listMax (a ++ b) = max (listMax a) (listMax b) := by
    induction a with
    | nil =>
      show listMax b = max 0 (listMax b)
      exact (max_eq_right (zero_le_listMax b)).symm
    | cons c cs ih => rw [List.cons_append, listMax_cons, listMax_cons, ih]; omega

  theorem listMin_append (a b : List Int) : listMin (a ++ b) = min (listMin a) (listMin b) := by
    induction a with
    | nil =>
      show listMin b = min 100000 (listMin b)
      exact (min_eq_right (listMin_le_bound b)).symm
    | cons c cs ih => rw [List.cons_append, listMin_cons, listMin_cons, ih]; omega

  theorem le_listMax {x : Int} {l : List Int} (h : x ∈ l) : x ≤ listMax l := by
    induction l with
    | nil => simp at h
    | cons c cs ih =>
      rw [listMax_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

  theorem listMin_le {x : Int} {l : List Int} (h : x ∈ l) : listMin l ≤ x := by
    induction l with
    | nil => simp at h
    | cons c cs ih =>
      rw [listMin_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

  theorem listMax_singleton_eq (x : Int) (hx : 0 ≤ x) : listMax [x] = x := by
    rw [listMax_cons]
    show max x 0 = x
    omega

  theorem listMin_singleton_eq (x : Int) (hx : x ≤ 100000) : listMin [x] = x := by
    rw [listMin_cons]
    show min x 100000 = x
    omega

  /-! #### Lemmas about `pathSpread` and `foldSpread` -/

  theorem pathSpread_nonneg {p : List Int} (hne : p ≠ [])
      (hlo : ∀ x ∈ p, 0 ≤ x) (hhi : ∀ x ∈ p, x ≤ 100000) : 0 ≤ pathSpread p := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ p := List.exists_mem_of_ne_nil p hne
    have h1 := listMin_le hx
    have h2 := le_listMax hx
    simp only [pathSpread]
    omega

  theorem pathSpread_isPrefix {p q : List Int} (h : p <+: q) : pathSpread p ≤ pathSpread q := by
    obtain ⟨r, rfl⟩ := h
    have h1 : listMax p ≤ listMax (p ++ r) := by rw [listMax_append]; exact le_max_left _ _
    have h2 : listMin (p ++ r) ≤ listMin p := by rw [listMin_append]; exact min_le_left _ _
    simp only [pathSpread]
    omega

  theorem foldSpread_cons (p : List Int) (L : List (List Int)) :
      foldSpread (p :: L) = max (pathSpread p) (foldSpread L) := rfl

  theorem zero_le_foldSpread (L : List (List Int)) : 0 ≤ foldSpread L := by
    induction L with
    | nil => simp [foldSpread]
    | cons p ps ih => rw [foldSpread_cons]; omega

  theorem foldSpread_push (L : List (List Int)) (x : Int) (hx : 0 ≤ x) :
      List.foldr (fun p a => max (pathSpread p) a) x L = max x (foldSpread L) := by
    induction L with
    | nil => simp [foldSpread]; omega
    | cons p ps ih =>
      show max (pathSpread p) (List.foldr (fun p a => max (pathSpread p) a) x ps)
        = max x (foldSpread (p :: ps))
      rw [ih, foldSpread_cons]
      omega

  theorem foldSpread_mem_le {p : List Int} {L : List (List Int)} (h : p ∈ L) :
      pathSpread p ≤ foldSpread L := by
    induction L with
    | nil => simp at h
    | cons q qs ih =>
      rw [foldSpread_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

  theorem foldSpread_singleton (p : List Int) : foldSpread [p] = max (pathSpread p) 0 := rfl

  theorem foldSpread_append (L₁ L₂ : List (List Int)) :
      foldSpread (L₁ ++ L₂) = max (foldSpread L₁) (foldSpread L₂) := by
    have h := foldSpread_push L₁ (foldSpread L₂) (zero_le_foldSpread L₂)
    simp only [foldSpread] at h ⊢
    rw [List.foldr_append, h, max_comm]

  /-! #### Membership in `nullPathsAux` and `rootLeafPathsAux` -/

  theorem nullPaths_prefix_mem (t : Tree) : ∀ (acc : List Int) (p : List Int),
      p ∈ nullPathsAux acc t →
      acc <+: p ∧ ∀ x ∈ p, x ∈ acc ∨ x ∈ values t := by
    induction t with
    | Null =>
      intro acc p h
      simp only [nullPathsAux, List.mem_singleton] at h
      subst h
      exact ⟨List.prefix_refl _, fun x hx => Or.inl hx⟩
    | Node v l r ihl ihr =>
      intro acc p h
      simp only [nullPathsAux, List.mem_append] at h
      have hvmem : v.val ∈ values (Tree.Node v l r) := by simp [values]
      have hpre : acc <+: acc ++ [v.val] := List.prefix_append acc [v.val]
      have hmemacc : ∀ x ∈ (acc ++ [v.val]), x ∈ acc ∨ x ∈ values (Tree.Node v l r) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact Or.inr hvmem
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := ihl (acc ++ [v.val]) p h
        refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
        intro x hx
        rcases h2 x hx with hx | hx
        · exact hmemacc x hx
        · exact Or.inr (by
            simp only [values]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      · obtain ⟨h1, h2⟩ := ihr (acc ++ [v.val]) p h
        refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
        intro x hx
        rcases h2 x hx with hx | hx
        · exact hmemacc x hx
        · exact Or.inr (by
            simp only [values]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))

  theorem rootLeafPaths_prefix_mem (t : Tree) : ∀ (acc : List Int) (p : List Int),
      p ∈ rootLeafPathsAux acc t →
      acc <+: p ∧ ∀ x ∈ p, x ∈ acc ∨ x ∈ values t := by
    induction t with
    | Null =>
      intro acc p h
      simp only [rootLeafPathsAux, List.not_mem_nil] at h
    | Node v l r ihl ihr =>
      intro acc p h
      have hvmem : v.val ∈ values (Tree.Node v l r) := by simp [values]
      have hpre : acc <+: acc ++ [v.val] := List.prefix_append acc [v.val]
      have hmemacc : ∀ x ∈ (acc ++ [v.val]), x ∈ acc ∨ x ∈ values (Tree.Node v l r) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact Or.inr hvmem
      have hleft : ∀ (q : Int), q ∈ values l → q ∈ values (Tree.Node v l r) := by
        intro q hq
        simp only [values]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
      have hright : ∀ (q : Int), q ∈ values r → q ∈ values (Tree.Node v l r) := by
        intro q hq
        simp only [values]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hq)
      rcases l with _ | ⟨wl, ll, rl⟩
      · rcases r with _ | ⟨wr, lr, rr⟩
        · simp only [rootLeafPathsAux, List.mem_singleton] at h
          subst h
          exact ⟨hpre, hmemacc⟩
        · simp only [rootLeafPathsAux, List.nil_append] at h
          obtain ⟨h1, h2⟩ := ihr (acc ++ [v.val]) p h
          refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
          intro x hx
          rcases h2 x hx with hx | hx
          · exact hmemacc x hx
          · exact Or.inr (hright x hx)
      · rcases r with _ | ⟨wr, lr, rr⟩
        · simp only [rootLeafPathsAux, List.append_nil, List.nil_append] at h
          obtain ⟨h1, h2⟩ := ihl (acc ++ [v.val]) p h
          refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
          intro x hx
          rcases h2 x hx with hx | hx
          · exact hmemacc x hx
          · exact Or.inr (hleft x hx)
        · simp only [rootLeafPathsAux, List.mem_append] at h
          rcases h with h | h
          · obtain ⟨h1, h2⟩ := ihl (acc ++ [v.val]) p h
            refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
            intro x hx
            rcases h2 x hx with hx | hx
            · exact hmemacc x hx
            · exact Or.inr (hleft x hx)
          · obtain ⟨h1, h2⟩ := ihr (acc ++ [v.val]) p h
            refine ⟨List.IsPrefix.trans hpre h1, ?_⟩
            intro x hx
            rcases h2 x hx with hx | hx
            · exact hmemacc x hx
            · exact Or.inr (hright x hx)

  theorem nullPaths_exists (t : Tree) : ∀ (acc : List Int), t ≠ Tree.Null →
      ∃ p, p ∈ nullPathsAux acc t := by
    induction t with
    | Null => intro acc h; exact absurd rfl h
    | Node v l r ihl ihr =>
      intro acc _
      rcases l with _ | ⟨wl, ll, rl⟩
      · exact ⟨acc ++ [v.val], by
          simp only [nullPathsAux]
          exact List.mem_append_left _ (List.mem_singleton_self _)⟩
      · obtain ⟨p, hp⟩ := ihl (acc ++ [v.val]) (by simp)
        exact ⟨p, by
          simp only [nullPathsAux]
          exact List.mem_append_left _ hp⟩

  theorem rootLeafPaths_exists (t : Tree) : ∀ (acc : List Int), t ≠ Tree.Null →
      ∃ p, p ∈ rootLeafPathsAux acc t := by
    induction t with
    | Null => intro acc h; exact absurd rfl h
    | Node v l r ihl ihr =>
      intro acc _
      rcases l with _ | ⟨wl, ll, rl⟩
      · rcases r with _ | ⟨wr, lr, rr⟩
        · exact ⟨acc ++ [v.val], by simp [rootLeafPathsAux]⟩
        · obtain ⟨p, hp⟩ := ihr (acc ++ [v.val]) (by simp)
          exact ⟨p, by
            simp only [rootLeafPathsAux, List.nil_append]
            exact hp⟩
      · rcases r with _ | ⟨wr, lr, rr⟩
        · obtain ⟨p, hp⟩ := ihl (acc ++ [v.val]) (by simp)
          exact ⟨p, by
            simp only [rootLeafPathsAux, List.append_nil]
            exact hp⟩
        · obtain ⟨p, hp⟩ := ihl (acc ++ [v.val]) (by simp)
          exact ⟨p, by
            simp only [rootLeafPathsAux]
            exact List.mem_append_left _ hp⟩

  /-! #### The maximum over `nullPathsAux` equals the maximum over `rootLeafPathsAux` -/

  theorem paths_max_eq (t : Tree) : ∀ (acc : List Int),
      acc ≠ [] → (∀ x ∈ acc, 0 ≤ x ∧ x ≤ 100000) →
      (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      (t ≠ Tree.Null ∨ listMin acc = listMax acc) →
      foldSpread (nullPathsAux acc t) = foldSpread (rootLeafPathsAux acc t) := by
    induction t with
    | Null =>
      intro acc hne hacc hv hdis
      rcases hdis with h | h
      · exact absurd rfl h
      · show foldSpread [acc] = foldSpread []
        rw [foldSpread_singleton]
        have hzero : pathSpread acc = 0 := by simp only [pathSpread]; omega
        rw [hzero]
        rfl
    | Node v l r ihl ihr =>
      intro acc hne hacc hv _
      have hvval : 0 ≤ v.val ∧ v.val ≤ 100000 := hv v.val (by simp [values])
      have hacc' : ∀ x ∈ acc ++ [v.val], 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact hvval
      have hne' : acc ++ [v.val] ≠ [] := by simp
      have hv_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hv_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hkey : ∀ (s : Tree), s ≠ Tree.Null →
          pathSpread (acc ++ [v.val]) ≤ foldSpread (rootLeafPathsAux (acc ++ [v.val]) s) := by
        intro s hs
        obtain ⟨p, hp⟩ := rootLeafPaths_exists s (acc ++ [v.val]) hs
        have hpre := (rootLeafPaths_prefix_mem s (acc ++ [v.val]) p hp).1
        exact le_trans (pathSpread_isPrefix hpre) (foldSpread_mem_le hp)
      rcases l with _ | ⟨wl, ll, rl⟩
      · rcases r with _ | ⟨wr, lr, rr⟩
        · show foldSpread ([acc ++ [v.val]] ++ [acc ++ [v.val]])
              = foldSpread [acc ++ [v.val]]
          rw [foldSpread_append, foldSpread_singleton]
          omega
        · show foldSpread ([acc ++ [v.val]] ++ nullPathsAux (acc ++ [v.val]) (Tree.Node wr lr rr))
              = foldSpread (rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wr lr rr))
          rw [foldSpread_append, foldSpread_singleton,
            ihr (acc ++ [v.val]) hne' hacc' hv_r (Or.inl (by simp))]
          have hh := hkey (Tree.Node wr lr rr) (by simp)
          have h0 := zero_le_foldSpread (rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wr lr rr))
          omega
      · rcases r with _ | ⟨wr, lr, rr⟩
        · have hRL : rootLeafPathsAux acc (Tree.Node v (Tree.Node wl ll rl) Tree.Null)
              = rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wl ll rl) := by
            simp only [rootLeafPathsAux, List.append_nil]
          rw [show nullPathsAux acc (Tree.Node v (Tree.Node wl ll rl) Tree.Null)
              = nullPathsAux (acc ++ [v.val]) (Tree.Node wl ll rl)
                ++ [acc ++ [v.val]] from rfl,
            hRL, foldSpread_append, foldSpread_singleton,
            ihl (acc ++ [v.val]) hne' hacc' hv_l (Or.inl (by simp))]
          have hh := hkey (Tree.Node wl ll rl) (by simp)
          have h0 := zero_le_foldSpread (rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wl ll rl))
          omega
        · rw [show nullPathsAux acc (Tree.Node v (Tree.Node wl ll rl) (Tree.Node wr lr rr))
              = nullPathsAux (acc ++ [v.val]) (Tree.Node wl ll rl)
                ++ nullPathsAux (acc ++ [v.val]) (Tree.Node wr lr rr) from rfl,
              show rootLeafPathsAux acc (Tree.Node v (Tree.Node wl ll rl) (Tree.Node wr lr rr))
              = rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wl ll rl)
                ++ rootLeafPathsAux (acc ++ [v.val]) (Tree.Node wr lr rr) from rfl,
              foldSpread_append, foldSpread_append,
              ihl (acc ++ [v.val]) hne' hacc' hv_l (Or.inl (by simp)),
              ihr (acc ++ [v.val]) hne' hacc' hv_r (Or.inl (by simp))]

  /-! #### Integer bounds and `Result` facts -/

  theorem ite_lt_val (v mn : Std.I64) : (if v < mn then v else mn).val = min mn.val v.val := by
    by_cases h : v < mn
    · rw [if_pos h]
      have hv : v.val ≤ mn.val := by simpa using le_of_lt h
      omega
    · rw [if_neg h]
      have hv : mn.val ≤ v.val := by simpa using h
      omega

  theorem ite_gt_val (v mx : Std.I64) : (if v > mx then v else mx).val = max mx.val v.val := by
    by_cases h : v > mx
    · rw [if_pos h]
      have hv : mx.val ≤ v.val := by simpa using le_of_lt h
      omega
    · rw [if_neg h]
      have hv : v.val ≤ mx.val := by simpa using h
      omega

  theorem spec_ok_exists {α : Type} {m : Result α} {p : WP.Post α} (h : WP.spec m p) :
      ∃ v, m = Result.ok v ∧ p v := by
    revert h
    refine Result.cases m ?_ ?_ ?_
    · intro v h
      exact ⟨v, rfl, by simpa using h⟩
    · intro eff k h
      cases eff with
      | fail e =>
        simp only [WP.spec_vis] at h
    · intro h
      simp only [WP.spec_div, iff_false, not_false_eq_true, false_implies] at h

  /-! #### `dfs` computes `dfsI` -/

  theorem dfs_spec (t : Tree) : ∀ (mn mx : Std.I64),
      0 ≤ mn.val → mn.val ≤ mx.val → mx.val ≤ 100000 →
      (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      ∃ res : Std.I64, dfs t mn mx = ok res ∧ res.val = dfsI t mn.val mx.val := by
    induction t with
    | Null =>
      intro mn mx h1 h2 h3 hv
      have hb1 : Std.I64.min ≤ mx.val - mn.val := by scalar_tac
      have hb2 : mx.val - mn.val ≤ Std.I64.max := by scalar_tac
      obtain ⟨res, hres, hval⟩ := spec_ok_exists (I64.sub_spec (x := mx) (y := mn) hb1 hb2)
      refine ⟨res, ?_, ?_⟩
      · rw [dfs.eq_1]; exact hres
      · rw [hval]
        show mx.val - mn.val = mx.val - mn.val
        rfl
    | Node v l r ihl ihr =>
      intro mn mx h1 h2 h3 hv
      set nmn : Std.I64 := if v < mn then v else mn with hnmn
      set nmx : Std.I64 := if v > mx then v else mx with hnmx
      have hmnval : nmn.val = min mn.val v.val := by rw [hnmn]; exact ite_lt_val v mn
      have hmxval : nmx.val = max mx.val v.val := by rw [hnmx]; exact ite_gt_val v mx
      have hvval : 0 ≤ v.val ∧ v.val ≤ 100000 := hv v.val (by simp [values])
      have hb1 : 0 ≤ nmn.val := by rw [hmnval]; omega
      have hb2 : nmn.val ≤ nmx.val := by rw [hmnval, hmxval]; omega
      have hb3 : nmx.val ≤ 100000 := by rw [hmxval]; omega
      have hv_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hv_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      obtain ⟨rl, hl, hvl⟩ := ihl nmn nmx hb1 hb2 hb3 hv_l
      obtain ⟨rr, hr, hvr⟩ := ihr nmn nmx hb1 hb2 hb3 hv_r
      have e1 : (if v < mn then (ok v : Result Std.I64) else ok mn) = ok nmn := by
        rw [hnmn]; by_cases h : v < mn <;> simp [h]
      have e2 : (if v > mx then (ok v : Result Std.I64) else ok mx) = ok nmx := by
        rw [hnmx]; by_cases h : v > mx <;> simp [h]
      have hl' : dfsI l (min mn.val v.val) (max mx.val v.val) = rl.val := by
        rw [← hmnval, ← hmxval, ← hvl]
      have hr' : dfsI r (min mn.val v.val) (max mx.val v.val) = rr.val := by
        rw [← hmnval, ← hmxval, ← hvr]
      refine ⟨if rl > rr then rl else rr, ?_, ?_⟩
      · rw [dfs.eq_2, e1]
        simp only [bind_ok]
        rw [e2]
        simp only [bind_ok]
        rw [hl]
        simp only [bind_ok]
        rw [hr]
        simp only [bind_ok]
        by_cases h : rl > rr <;> simp [h]
      · show (if rl > rr then rl else rr).val
          = dfsI (Tree.Node v l r) mn.val mx.val
        rw [show dfsI (Tree.Node v l r) mn.val mx.val
            = max (dfsI l (min mn.val v.val) (max mx.val v.val))
                  (dfsI r (min mn.val v.val) (max mx.val v.val)) from rfl]
        by_cases h : rl > rr
        · rw [if_pos h, hl', hr']
          have hlt : rr.val < rl.val := by simpa using h
          omega
        · rw [if_neg h, hl', hr']
          have hle : rl.val ≤ rr.val := by simpa using h
          omega

  /-! #### `dfsI` as a maximum over the paths of `nullPathsAux` -/

  theorem dfsI_eq_foldSpread (t : Tree) : ∀ (acc : List Int) (mn mx : Int),
      acc ≠ [] → (∀ x ∈ acc, 0 ≤ x ∧ x ≤ 100000) →
      (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      mn = listMin acc → mx = listMax acc →
      dfsI t mn mx = foldSpread (nullPathsAux acc t) := by
    induction t with
    | Null =>
      intro acc mn mx hne hacc hv hmn hmx
      have hpos : 0 ≤ pathSpread acc :=
        pathSpread_nonneg hne (fun x hx => (hacc x hx).1) (fun x hx => (hacc x hx).2)
      show mx - mn = foldSpread [acc]
      rw [foldSpread_singleton, hmn, hmx]
      exact (max_eq_left hpos).symm
    | Node v l r ihl ihr =>
      intro acc mn mx hne hacc hv hmn hmx
      have hvval : 0 ≤ v.val ∧ v.val ≤ 100000 := hv v.val (by simp [values])
      have hacc' : ∀ x ∈ acc ++ [v.val], 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact hvval
      have hne' : acc ++ [v.val] ≠ [] := by simp
      have hmn' : min mn v.val = listMin (acc ++ [v.val]) := by
        rw [hmn, listMin_append, listMin_cons]
        show min (listMin acc) v.val = min (listMin acc) (min v.val 100000)
        omega
      have hmx' : max mx v.val = listMax (acc ++ [v.val]) := by
        rw [hmx, listMax_append, listMax_cons]
        show max (listMax acc) v.val = max (listMax acc) (max v.val 0)
        omega
      have hv_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hv_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
        simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      rw [show dfsI (Tree.Node v l r) mn mx
          = max (dfsI l (min mn v.val) (max mx v.val))
                (dfsI r (min mn v.val) (max mx v.val)) from rfl]
      rw [show nullPathsAux acc (Tree.Node v l r)
          = nullPathsAux (acc ++ [v.val]) l ++ nullPathsAux (acc ++ [v.val]) r from rfl]
      rw [foldSpread_append,
        ihl (acc ++ [v.val]) (min mn v.val) (max mx v.val) hne' hacc' hv_l hmn' hmx',
        ihr (acc ++ [v.val]) (min mn v.val) (max mx v.val) hne' hacc' hv_r hmn' hmx']

  /-** spec_C1 [characterization]: the result is the maximum, over all root-to-leaf paths `P`,
  of `maxVal(P) - minVal(P)`. -/
  theorem spec_16 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = pathSpreadMax root := by
    intro res hres
    have hspread_of (v : Std.I64) (hv : 0 ≤ v.val ∧ v.val ≤ 100000) :
        pathSpread [v.val] = 0 := by
      simp only [pathSpread, listMax_singleton_eq v.val hv.1, listMin_singleton_eq v.val hv.2]
      omega
    rcases root with _ | ⟨v, l, r⟩
    · simp [size] at hsize_lo
    have hv : ∀ x ∈ values (Tree.Node v l r), 0 ≤ x ∧ x ≤ 100000 := hval
    have hvval : 0 ≤ v.val ∧ v.val ≤ 100000 := hv v.val (by simp [values])
    have hv_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
      simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
    have hv_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => hv x (by
      simp only [values]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx))
    -- `dfs` on the two children
    obtain ⟨rl, hldfs, hlv⟩ := dfs_spec l v v hvval.1 (le_refl _) hvval.2 hv_l
    obtain ⟨rr, hrdfs, hrv⟩ := dfs_spec r v v hvval.1 (le_refl _) hvval.2 hv_r
    -- the running minimum/maximum at the children is the min/max of `[v.val]`
    have hne1 : ([v.val] : List Int) ≠ [] := by simp
    have hrange1 : ∀ x ∈ ([v.val] : List Int), 0 ≤ x ∧ x ≤ 100000 := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hvval
    have hmn1 : v.val = listMin [v.val] := (listMin_singleton_eq v.val hvval.2).symm
    have hmx1 : v.val = listMax [v.val] := (listMax_singleton_eq v.val hvval.1).symm
    have hminmax : listMin [v.val] = listMax [v.val] := by rw [← hmn1, ← hmx1]
    have hlval : rl.val = foldSpread (rootLeafPathsAux [v.val] l) := by
      rw [hlv, dfsI_eq_foldSpread l [v.val] v.val v.val hne1 hrange1 hv_l hmn1 hmx1,
        paths_max_eq l [v.val] hne1 hrange1 hv_l (Or.inr hminmax)]
    have hrval : rr.val = foldSpread (rootLeafPathsAux [v.val] r) := by
      rw [hrv, dfsI_eq_foldSpread r [v.val] v.val v.val hne1 hrange1 hv_r hmn1 hmx1,
        paths_max_eq r [v.val] hne1 hrange1 hv_r (Or.inr hminmax)]
    -- compute `max_ancestor_diff`
    have hmad : max_ancestor_diff (Tree.Node v l r) = ok (if rl > rr then rl else rr) := by
      rw [max_ancestor_diff.eq_2, hldfs]
      simp only [bind_ok]
      rw [hrdfs]
      simp only [bind_ok]
      by_cases h : rl > rr <;> simp [h]
    have hresval : res.val = (if rl > rr then rl else rr).val := by
      rw [hmad] at hres
      simp only [Result.ok.injEq] at hres
      rw [← hres]
    have hmaxval : (if rl > rr then rl else rr).val = max rl.val rr.val := by
      by_cases h : rl > rr
      · rw [if_pos h]
        have hh : rr.val ≤ rl.val := by simpa using le_of_lt h
        omega
      · rw [if_neg h]
        have hh : rl.val ≤ rr.val := by simpa using h
        omega
    -- compute `pathSpreadMax`
    have hpsm : pathSpreadMax (Tree.Node v l r)
        = max (foldSpread (rootLeafPathsAux [v.val] l))
            (foldSpread (rootLeafPathsAux [v.val] r)) := by
      have hRLn : rootLeafPathsAux [v.val] Tree.Null = ([] : List (List Int)) := rfl
      have hnil : foldSpread ([] : List (List Int)) = 0 := rfl
      rcases l with _ | ⟨wl, ll, rl'⟩
      · rcases r with _ | ⟨wr, lr, rr'⟩
        · have h1 : pathSpreadMax (Tree.Node v Tree.Null Tree.Null) = foldSpread [[v.val]] := rfl
          rw [h1, foldSpread_singleton, hspread_of v hvval, hRLn, hnil, max_self]
        · have h1 : pathSpreadMax (Tree.Node v Tree.Null (Tree.Node wr lr rr'))
              = foldSpread (rootLeafPathsAux [v.val] (Tree.Node wr lr rr')) := rfl
          rw [h1, hRLn, hnil]
          exact (max_eq_right (zero_le_foldSpread _)).symm
      · rcases r with _ | ⟨wr, lr, rr'⟩
        · have h1 : pathSpreadMax (Tree.Node v (Tree.Node wl ll rl') Tree.Null)
              = foldSpread (rootLeafPathsAux [v.val] (Tree.Node wl ll rl') ++ []) := rfl
          rw [h1, List.append_nil, hRLn, hnil]
          exact (max_eq_left (zero_le_foldSpread _)).symm
        · have h1 : pathSpreadMax (Tree.Node v (Tree.Node wl ll rl') (Tree.Node wr lr rr'))
              = foldSpread (rootLeafPathsAux [v.val] (Tree.Node wl ll rl')
                  ++ rootLeafPathsAux [v.val] (Tree.Node wr lr rr')) := rfl
          rw [h1, foldSpread_append]
    rw [hpsm, ← hlval, ← hrval, hresval, hmaxval]

  /-** spec_C2 [per-node]: the result is the maximum, over all nodes `b`, of
  `max(value(b) - minAncestor(b), maxAncestor(b) - value(b))` (and `0` for the root). -/
  theorem spec_C2 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        res.val = nodeContribMax root := by
    sorry

  end AegisSpec.MaxAncestorDiff
