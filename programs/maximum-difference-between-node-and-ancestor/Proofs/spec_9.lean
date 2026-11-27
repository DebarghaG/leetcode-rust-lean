import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_9` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary lemmas for the shift-invariance specification `spec_S9` -/

  /-- `toI64` of an `I64`-representable integer has that integer as value. -/
  theorem toI64_val {x : Int} (h : -(2:Int)^63 ≤ x ∧ x < (2:Int)^63) : (toI64 x).val = x := by
    have h2 := BitVec.toInt_ofInt_eq_self (w := 64) (by norm_num) h.1 h.2
    show (BitVec.ofInt 64 x).toInt = x
    exact h2

  /-- `toI64` of an integer in `[0, 100000]` has that integer as value. -/
  theorem toI64_val_range {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 100000) : (toI64 x).val = x := by
    refine toI64_val ⟨?_, ?_⟩
    · have : (0:Int) ≤ (2:Int)^63 := by positivity
      omega
    · have : (100000:Int) < (2:Int)^63 := by norm_num
      omega

  /-- Subtracting two `I64` values of a tree (all in `[0, 100000]`) does not overflow and
  returns `toI64` of the difference of the integer values. -/
  theorem I64.sub_eq_toI64 {x y : Std.I64} (hx : 0 ≤ x.val ∧ x.val ≤ 100000)
      (hy : 0 ≤ y.val ∧ y.val ≤ 100000) : x - y = ok (toI64 (x.val - y.val)) := by
    have hin : IScalar.inBounds .I64 (x.val - y.val) := by
      simp only [IScalar.inBounds, IScalarTy.numBits]
      norm_num
      omega
    show IScalar.tryMk .I64 (x.val - y.val) = ok (toI64 (x.val - y.val))
    simp only [IScalar.tryMk, IScalar.tryMkOpt, Result.ofOption]
    rw [dif_pos (by rw [IScalar.check_bounds_eq_inBounds]; exact hin)]
    rfl

  /-- Node values of the left subtree are node values of the tree. -/
  theorem values_mem_left {v : Std.I64} {l r : Tree} {u : Int} (h : u ∈ values l) :
      u ∈ values (Tree.Node v l r) := by
    simp only [values, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl h)

  /-- Node values of the right subtree are node values of the tree. -/
  theorem values_mem_right {v : Std.I64} {l r : Tree} {u : Int} (h : u ∈ values r) :
      u ∈ values (Tree.Node v l r) := by
    simp only [values, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr h)

  /-- The root value is a node value of the tree. -/
  theorem values_mem_root {v : Std.I64} {l r : Tree} : v.val ∈ values (Tree.Node v l r) := by
    simp [values]

  /-- `ValuesIn` restricted to the left subtree. -/
  theorem ValuesIn.left {v : Std.I64} {l r : Tree} {lo hi : Int}
      (h : ValuesIn (Tree.Node v l r) lo hi) : ValuesIn l lo hi :=
    fun x hx => h x (values_mem_left hx)

  /-- `ValuesIn` restricted to the right subtree. -/
  theorem ValuesIn.right {v : Std.I64} {l r : Tree} {lo hi : Int}
      (h : ValuesIn (Tree.Node v l r) lo hi) : ValuesIn r lo hi :=
    fun x hx => h x (values_mem_right hx)

  /-- The node-value hypothesis restricted to the left subtree. -/
  theorem shift_bounds_left {v : Std.I64} {l r : Tree} {c : Int}
      (h : ∀ x ∈ values (Tree.Node v l r), 0 ≤ x + c ∧ x + c ≤ 100000) :
      ∀ x ∈ values l, 0 ≤ x + c ∧ x + c ≤ 100000 :=
    fun x hx => h x (values_mem_left hx)

  /-- The node-value hypothesis restricted to the right subtree. -/
  theorem shift_bounds_right {v : Std.I64} {l r : Tree} {c : Int}
      (h : ∀ x ∈ values (Tree.Node v l r), 0 ≤ x + c ∧ x + c ≤ 100000) :
      ∀ x ∈ values r, 0 ≤ x + c ∧ x + c ≤ 100000 :=
    fun x hx => h x (values_mem_right hx)

  /-- Shifting every node value by `c`, and shifting the running minimum and maximum by `c`,
  does not change the result of `dfs`. -/
  theorem dfs_shift (t : Tree) :
      ∀ (mn mx mn' mx' : Std.I64) (c : Int),
        mn'.val = mn.val + c → mx'.val = mx.val + c →
        0 ≤ mn.val → mn.val ≤ mx.val → mx.val ≤ 100000 →
        0 ≤ mn'.val → mn'.val ≤ mx'.val → mx'.val ≤ 100000 →
        ValuesIn t 0 100000 →
        (∀ x ∈ values t, 0 ≤ x + c ∧ x + c ≤ 100000) →
        dfs t mn mx = dfs (shift c t) mn' mx' := by
    induction t with
    | Null =>
      intro mn mx mn' mx' c hmn hmx h0 hle hhi h0' hle' hhi' hval hc
      rw [dfs.eq_1, show shift c Tree.Null = Tree.Null from rfl, dfs.eq_1]
      rw [I64.sub_eq_toI64 (x := mx) (y := mn) ⟨h0.trans hle, hhi⟩ ⟨h0, hle.trans hhi⟩,
          I64.sub_eq_toI64 (x := mx') (y := mn') ⟨h0'.trans hle', hhi'⟩ ⟨h0', hle'.trans hhi'⟩]
      have he : mx'.val - mn'.val = mx.val - mn.val := by rw [hmx, hmn]; omega
      rw [he]
    | Node v l r ihl ihr =>
      intro mn mx mn' mx' c hmn hmx h0 hle hhi h0' hle' hhi' hval hc
      have hvmem : v.val ∈ values (Tree.Node v l r) := values_mem_root
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val hvmem
      have hvc : 0 ≤ v.val + c ∧ v.val + c ≤ 100000 := hc v.val hvmem
      have hv' : (toI64 (v.val + c)).val = v.val + c := toI64_val_range hvc.1 hvc.2
      have hlt : (v < mn) ↔ (toI64 (v.val + c) < mn') := by
        rw [IScalar.lt_equiv, IScalar.lt_equiv, hv', hmn]
        omega
      have hgt : (v > mx) ↔ (toI64 (v.val + c) > mx') := by
        show mx < v ↔ mx' < toI64 (v.val + c)
        rw [IScalar.lt_equiv, IScalar.lt_equiv, hv', hmx]
        omega
      have hvalL : ValuesIn l 0 100000 := hval.left
      have hvalR : ValuesIn r 0 100000 := hval.right
      have hcL : ∀ x ∈ values l, 0 ≤ x + c ∧ x + c ≤ 100000 := shift_bounds_left hc
      have hcR : ∀ x ∈ values r, 0 ≤ x + c ∧ x + c ≤ 100000 := shift_bounds_right hc
      have hv'0 : 0 ≤ (toI64 (v.val + c)).val := by rw [hv']; exact hvc.1
      have hv'hi : (toI64 (v.val + c)).val ≤ 100000 := by rw [hv']; exact hvc.2
      rw [show shift c (Tree.Node v l r)
            = Tree.Node (toI64 (v.val + c)) (shift c l) (shift c r) from rfl]
      rw [dfs.eq_2, dfs.eq_2]
      by_cases h1 : v < mn
      · have h1' : toI64 (v.val + c) < mn' := hlt.mp h1
        by_cases h2 : v > mx
        · have h2' : toI64 (v.val + c) > mx' := hgt.mp h2
          simp only [if_pos h1, if_pos h1', if_pos h2, if_pos h2', bind_ok]
          rw [ihl v v _ _ c hv' hv' hv.1 le_rfl hv.2 hv'0 le_rfl hv'hi hvalL hcL,
              ihr v v _ _ c hv' hv' hv.1 le_rfl hv.2 hv'0 le_rfl hv'hi hvalR hcR]
        · have h2' : ¬ (toI64 (v.val + c) > mx') := fun hh => h2 (hgt.mpr hh)
          have hle2 : v.val ≤ mx.val := by
            have h : v ≤ mx := not_lt.mp h2
            simpa using h
          have hle2' : (toI64 (v.val + c)).val ≤ mx'.val := by
            have h : toI64 (v.val + c) ≤ mx' := not_lt.mp h2'
            simpa using h
          simp only [if_pos h1, if_pos h1', if_neg h2, if_neg h2', bind_ok]
          rw [ihl v mx _ _ c hv' hmx hv.1 hle2 hhi hv'0 hle2' hhi' hvalL hcL,
              ihr v mx _ _ c hv' hmx hv.1 hle2 hhi hv'0 hle2' hhi' hvalR hcR]
      · have h1' : ¬ (toI64 (v.val + c) < mn') := fun hh => h1 (hlt.mpr hh)
        have hle1 : mn.val ≤ v.val := by
          have h : mn ≤ v := not_lt.mp h1
          simpa using h
        have hle1' : mn'.val ≤ (toI64 (v.val + c)).val := by
          have h : mn' ≤ toI64 (v.val + c) := not_lt.mp h1'
          simpa using h
        by_cases h2 : v > mx
        · have h2' : toI64 (v.val + c) > mx' := hgt.mp h2
          simp only [if_neg h1, if_neg h1', if_pos h2, if_pos h2', bind_ok]
          rw [ihl mn v _ _ c hmn hv' h0 hle1 hv.2 h0' hle1' hv'hi hvalL hcL,
              ihr mn v _ _ c hmn hv' h0 hle1 hv.2 h0' hle1' hv'hi hvalR hcR]
        · have h2' : ¬ (toI64 (v.val + c) > mx') := fun hh => h2 (hgt.mpr hh)
          simp only [if_neg h1, if_neg h1', if_neg h2, if_neg h2', bind_ok]
          rw [ihl mn mx _ _ c hmn hmx h0 hle hhi h0' hle' hhi' hvalL hcL,
              ihr mn mx _ _ c hmn hmx h0 hle hhi h0' hle' hhi' hvalR hcR]

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
  theorem spec_9 (root : Tree) (c : Int)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hc : ∀ v ∈ values root, 0 ≤ v + c ∧ v + c ≤ 100000) :
      ∀ res res_c : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (shift c root) = ok res_c → res_c.val = res.val := by
    intro res res_c h1 h2
    cases root with
    | Null =>
      rw [max_ancestor_diff.eq_def] at h1
      rw [show shift c Tree.Null = Tree.Null from rfl, max_ancestor_diff.eq_def] at h2
      rw [h1] at h2
      have h : res = res_c := by simpa using h2
      rw [← h]
    | Node v l r =>
      have hvmem : v.val ∈ values (Tree.Node v l r) := values_mem_root
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val hvmem
      have hvc : 0 ≤ v.val + c ∧ v.val + c ≤ 100000 := hc v.val hvmem
      have hv' : (toI64 (v.val + c)).val = v.val + c := toI64_val_range hvc.1 hvc.2
      have hv'0 : 0 ≤ (toI64 (v.val + c)).val := by rw [hv']; exact hvc.1
      have hv'hi : (toI64 (v.val + c)).val ≤ 100000 := by rw [hv']; exact hvc.2
      have hvalL : ValuesIn l 0 100000 := hval.left
      have hvalR : ValuesIn r 0 100000 := hval.right
      have hcL : ∀ x ∈ values l, 0 ≤ x + c ∧ x + c ≤ 100000 := shift_bounds_left hc
      have hcR : ∀ x ∈ values r, 0 ≤ x + c ∧ x + c ≤ 100000 := shift_bounds_right hc
      have e1 : dfs l v v = dfs (shift c l) (toI64 (v.val + c)) (toI64 (v.val + c)) :=
        dfs_shift l v v (toI64 (v.val + c)) (toI64 (v.val + c)) c hv' hv'
          hv.1 le_rfl hv.2 hv'0 le_rfl hv'hi hvalL hcL
      have e2 : dfs r v v = dfs (shift c r) (toI64 (v.val + c)) (toI64 (v.val + c)) :=
        dfs_shift r v v (toI64 (v.val + c)) (toI64 (v.val + c)) c hv' hv'
          hv.1 le_rfl hv.2 hv'0 le_rfl hv'hi hvalR hcR
      rw [max_ancestor_diff.eq_def] at h1
      rw [show shift c (Tree.Node v l r)
            = Tree.Node (toI64 (v.val + c)) (shift c l) (shift c r) from rfl,
          max_ancestor_diff.eq_def] at h2
      simp only [] at h1 h2
      rw [e1, e2] at h1
      rw [h1] at h2
      have h : res = res_c := by simpa using h2
      rw [← h]

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
