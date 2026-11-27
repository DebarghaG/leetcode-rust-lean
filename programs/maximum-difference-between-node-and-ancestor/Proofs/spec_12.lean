import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_12` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary material for the proof of `spec_S12` -/

  /-- Supremum of `|a - x|` over the values of the list `acc` (`0` for the empty list). -/
  def supAcc : List Int → Int → Int
    | [], _ => 0
    | a :: l, x => max (absDiff a x) (supAcc l x)

  /-- Minimum of a list of values (`100000` for the empty list). -/
  def accMin : List Int → Int
    | [] => 100000
    | a :: l => min (accMin l) a

  /-- Maximum of a list of values (`0` for the empty list). -/
  def accMax : List Int → Int
    | [] => 0
    | a :: l => max (accMax l) a

  /-- Maximum of `|a - value b|` over the nodes `b` of `t` and the values `a` of `acc`. -/
  def treeSup (acc : List Int) : Tree → Int
    | .Null => 0
    | .Node v l r =>
      max (supAcc acc v.val) (max (treeSup (v.val :: acc) l) (treeSup (v.val :: acc) r))

  /-- Maximum of `|p.1 - p.2|` over a list of pairs (this is the body of `ancPairMax`). -/
  def pmax : List (Int × Int) → Int
    | [] => 0
    | p :: l => max (absDiff p.1 p.2) (pmax l)

  /-- The integer value computed by `dfs`, with the `Result` wrapper removed. -/
  def dfsVal (mn mx : Int) : Tree → Int
    | .Null => mx - mn
    | .Node v l r =>
      max (dfsVal (min mn v.val) (max mx v.val) l) (dfsVal (min mn v.val) (max mx v.val) r)

  theorem values_node (v : Std.I64) (l r : Tree) :
      values (.Node v l r) = v.val :: (values l ++ values r) := rfl

  theorem values_left {v : Std.I64} {l r : Tree} {x : Int} (h : x ∈ values l) :
      x ∈ values (.Node v l r) := by
    rw [values_node]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

  theorem values_right {v : Std.I64} {l r : Tree} {x : Int} (h : x ∈ values r) :
      x ∈ values (.Node v l r) := by
    rw [values_node]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

  theorem ValuesIn.left {v : Std.I64} {l r : Tree} {lo hi : Int}
      (h : ValuesIn (.Node v l r) lo hi) : ValuesIn l lo hi :=
    fun _ hx => h _ (values_left hx)

  theorem ValuesIn.right {v : Std.I64} {l r : Tree} {lo hi : Int}
      (h : ValuesIn (.Node v l r) lo hi) : ValuesIn r lo hi :=
    fun _ hx => h _ (values_right hx)

  theorem ValuesIn.node {v : Std.I64} {l r : Tree} {lo hi : Int}
      (hv : lo ≤ v.val ∧ v.val ≤ hi) (hl : ValuesIn l lo hi) (hr : ValuesIn r lo hi) :
      ValuesIn (.Node v l r) lo hi := by
    intro x hx
    rw [values_node] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hv
    · rcases List.mem_append.1 hx with hx | hx
      · exact hl x hx
      · exact hr x hx

  theorem absDiff_nonneg (a b : Int) : 0 ≤ absDiff a b := by
    unfold absDiff
    omega

  theorem pmax_nonneg : ∀ l : List (Int × Int), 0 ≤ pmax l
    | [] => by simp [pmax]
    | p :: l => by
      have h1 := absDiff_nonneg p.1 p.2
      have h2 := pmax_nonneg l
      simp only [pmax]
      omega

  theorem pmax_append : ∀ (xs ys : List (Int × Int)),
      pmax (xs ++ ys) = max (pmax xs) (pmax ys)
    | [], ys => by
      have h := pmax_nonneg ys
      simp only [List.nil_append, pmax]
      omega
    | p :: xs, ys => by
      have h := pmax_append xs ys
      simp only [List.cons_append, pmax, h]
      omega

  theorem pmax_map (x : Int) : ∀ l : List Int,
      pmax (l.map (fun a => (a, x))) = supAcc l x
    | [] => by simp [pmax, supAcc]
    | a :: l => by
      have h := pmax_map x l
      simp only [List.map_cons, pmax, supAcc, h]

  theorem supAcc_nonneg (acc : List Int) (x : Int) : 0 ≤ supAcc acc x := by
    induction acc with
    | nil => simp [supAcc]
    | cons a l ih =>
      have h := absDiff_nonneg a x
      simp only [supAcc]
      omega

  theorem treeSup_nonneg (acc : List Int) : ∀ t : Tree, 0 ≤ treeSup acc t
    | .Null => by simp [treeSup]
    | .Node v l r => by
      have h1 := supAcc_nonneg acc v.val
      have h2 := treeSup_nonneg (v.val :: acc) l
      have h3 := treeSup_nonneg (v.val :: acc) r
      simp only [treeSup]
      omega

  theorem pmax_ancPairsAux (t : Tree) :
      ∀ acc : List Int, pmax (ancPairsAux acc t) = treeSup acc t := by
    induction t with
    | Null => intro acc; rfl
    | Node v l r ihl ihr =>
      intro acc
      have h1 := ihl (v.val :: acc)
      have h2 := ihr (v.val :: acc)
      have h3 := pmax_map v.val acc
      simp only [ancPairsAux, treeSup, pmax_append, h1, h2, h3]
      omega

  theorem accMin_le_of_mem {a : Int} : ∀ {acc : List Int}, a ∈ acc → accMin acc ≤ a
    | [], h => by simp at h
    | b :: l, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [accMin]
        omega
      · have := accMin_le_of_mem h
        simp only [accMin]
        omega

  theorem le_accMax_of_mem {a : Int} : ∀ {acc : List Int}, a ∈ acc → a ≤ accMax acc
    | [], h => by simp at h
    | b :: l, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [accMax]
        omega
      · have := le_accMax_of_mem h
        simp only [accMax]
        omega

  theorem accMin_le_accMax (acc : List Int) (a : Int) (ha : a ∈ acc) :
      accMin acc ≤ accMax acc :=
    le_trans (accMin_le_of_mem ha) (le_accMax_of_mem ha)

  theorem accMin_cons (a : Int) (l : List Int) : accMin (a :: l) = min (accMin l) a := rfl

  theorem accMax_cons (a : Int) (l : List Int) : accMax (a :: l) = max (accMax l) a := rfl

  theorem accMin_singleton (a : Int) (h : a ≤ 100000) : accMin [a] = a := by
    simp only [accMin]
    omega

  theorem accMax_singleton (a : Int) (h : 0 ≤ a) : accMax [a] = a := by
    simp only [accMax]
    omega

  theorem supAcc_eq (acc : List Int) (x : Int) (ha : ∀ a ∈ acc, 0 ≤ a ∧ a ≤ 100000) :
      ∀ hne : acc ≠ [], supAcc acc x = max (x - accMin acc) (accMax acc - x) := by
    induction acc with
    | nil => intro hne; exact absurd rfl hne
    | cons a l ih =>
      intro _
      have haa := ha a (by simp)
      cases l with
      | nil =>
        have h1 : accMin [a] = a := accMin_singleton a haa.2
        have h2 : accMax [a] = a := accMax_singleton a haa.1
        have h3 : 0 ≤ absDiff a x := absDiff_nonneg a x
        simp only [supAcc, h1, h2]
        unfold absDiff
        omega
      | cons b l =>
        have hb : ∀ c ∈ b :: l, 0 ≤ c ∧ c ≤ 100000 := by
          intro c hc
          exact ha c (by simp only [List.mem_cons] at hc ⊢; tauto)
        have hih := ih hb (by simp)
        have h3 : 0 ≤ absDiff a x := absDiff_nonneg a x
        simp only [accMin, accMax] at hih ⊢
        have hs : supAcc (a :: b :: l) x = max (absDiff a x) (supAcc (b :: l) x) := rfl
        rw [hs, hih]
        simp only [absDiff]
        omega

  theorem accMin_le_accMax_of_ne : ∀ acc : List Int, acc ≠ [] → accMin acc ≤ accMax acc
    | [], h => absurd rfl h
    | [a], _ => by
      simp only [accMin, accMax]
      omega
    | a :: b :: l, _ => by
      have h := accMin_le_accMax_of_ne (b :: l) (by simp)
      simp only [accMin, accMax] at h ⊢
      omega

  /-- The arithmetic identity giving the spread of a one-node path extension. -/
  theorem spread_step (mn mx v : Int) (h : mn ≤ mx) :
      max mx v - min mn v = max (mx - mn) (max (v - mn) (mx - v)) := by omega

  theorem supAcc_singleton_self (a : Int) : supAcc [a] a = 0 := by
    have h := absDiff_nonneg a a
    simp only [supAcc]
    simp only [absDiff] at h ⊢
    omega

  theorem dfsVal_eq (t : Tree) :
      ∀ acc : List Int, acc ≠ [] → (∀ a ∈ acc, 0 ≤ a ∧ a ≤ 100000) →
        (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
        dfsVal (accMin acc) (accMax acc) t =
          max (accMax acc - accMin acc) (treeSup acc t) := by
    induction t with
    | Null =>
      intro acc hne hacc _
      have h1 := accMin_le_accMax_of_ne acc hne
      have h2 := treeSup_nonneg acc .Null
      simp only [dfsVal, treeSup]
      omega
    | Node v l r ihl ihr =>
      intro acc hne hacc ht
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 :=
        ht v.val (by rw [values_node]; exact List.mem_cons_self ..)
      have hacc' : ∀ a ∈ v.val :: acc, 0 ≤ a ∧ a ≤ 100000 := by
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hv
        · exact hacc a ha
      have hl := ValuesIn.left (lo := 0) (hi := 100000) ht
      have hr := ValuesIn.right (lo := 0) (hi := 100000) ht
      have ihl' := ihl (v.val :: acc) (by simp) hacc' hl
      have ihr' := ihr (v.val :: acc) (by simp) hacc' hr
      have hmn : accMin acc ≤ accMax acc := accMin_le_accMax_of_ne acc hne
      have hsup := supAcc_eq acc v.val hacc hne
      have key : accMax (v.val :: acc) - accMin (v.val :: acc) =
          max (accMax acc - accMin acc) (supAcc acc v.val) := by
        rw [accMax_cons, accMin_cons, hsup]
        exact spread_step _ _ _ hmn
      simp only [dfsVal, treeSup]
      rw [← accMin_cons v.val acc, ← accMax_cons v.val acc, ihl', ihr', key]
      omega

  theorem I64.sub_ok_val (x y : Std.I64) (hlo : -(2 ^ 62 : Int) ≤ x.val - y.val)
      (hhi : x.val - y.val ≤ 2 ^ 62) :
      ∃ z : Std.I64, x - y = ok z ∧ z.val = x.val - y.val := by
    have hb := IScalar.sub_equiv (ty := IScalarTy.I64) x y
    have hin : IScalar.inBounds IScalarTy.I64 (x.val - y.val) := by
      simp only [IScalar.inBounds, IScalarTy.I64_numBits_eq]
      constructor <;> norm_num <;> omega
    rcases hm : (x - y).match with z | dv | vs
    · rw [Result.match.isOk] at hm
      rw [hm] at hb
      simp only [Result.match.ok] at hb
      exact ⟨z, hm, hb.2.1⟩
    · rw [hm] at hb
      have hb2 : False := hb
      exact hb2.elim
    · rw [hm] at hb
      cases vs with
      | fail e =>
        have hb2 : ¬ IScalar.inBounds IScalarTy.I64 (x.val - y.val) := hb
        exact absurd hin hb2

  theorem dfs_node (v : Std.I64) (l r : Tree) (mn mx : Std.I64) :
      dfs (.Node v l r) mn mx =
        (do
          let nmn ← if v < mn then ok v else ok mn
          let nmx ← if v > mx then ok v else ok mx
          let a ← dfs l nmn nmx
          let b ← dfs r nmn nmx
          if a > b then ok a else ok b) := by
    rw [dfs.eq_def]

  theorem if_lt_val (a b : Std.I64) :
      ∃ c : Std.I64, (if a < b then ok a else ok b) = ok c ∧ c.val = min a.val b.val := by
    by_cases h : a < b
    · have h' : a.val < b.val := by simpa using h
      exact ⟨a, by rw [if_pos h], by rw [min_eq_left (le_of_lt h')]⟩
    · have h' : b.val ≤ a.val := by
        have h'' : ¬ a.val < b.val := by simpa using h
        omega
      exact ⟨b, by rw [if_neg h], by rw [min_eq_right h']⟩

  theorem if_gt_val (a b : Std.I64) :
      ∃ c : Std.I64, (if a > b then ok a else ok b) = ok c ∧ c.val = max a.val b.val := by
    by_cases h : a > b
    · have h' : a.val > b.val := by simpa using h
      exact ⟨a, by rw [if_pos h], by rw [max_eq_left (le_of_lt h')]⟩
    · have h' : a.val ≤ b.val := by
        have h'' : ¬ a.val > b.val := by simpa using h
        omega
      exact ⟨b, by rw [if_neg h], by rw [max_eq_right h']⟩

  theorem dfs_val_ex : ∀ (t : Tree) (hval : ValuesIn t 0 100000) (mn mx : Std.I64),
      0 ≤ mn.val → mn.val ≤ 100000 → 0 ≤ mx.val → mx.val ≤ 100000 →
        ∃ r : Std.I64, dfs t mn mx = ok r ∧ r.val = dfsVal mn.val mx.val t
    | .Null, _, mn, mx, h1, h2, h3, h4 => by
      obtain ⟨z, hz, hzv⟩ := I64.sub_ok_val mx mn (by omega) (by omega)
      refine ⟨z, ?_, ?_⟩
      · rw [dfs.eq_1]
        exact hz
      · rw [hzv]
        rfl
    | .Node v l r, hval, mn, mx, h1, h2, h3, h4 => by
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 :=
        hval v.val (by rw [values_node]; exact List.mem_cons_self ..)
      have hl : ValuesIn l 0 100000 := ValuesIn.left hval
      have hr : ValuesIn r 0 100000 := ValuesIn.right hval
      obtain ⟨nmn, hnmn, hnmnv⟩ := if_lt_val v mn
      obtain ⟨nmx, hnmx, hnmxv⟩ := if_gt_val v mx
      have hb1 : 0 ≤ nmn.val := by rw [hnmnv]; omega
      have hb2 : nmn.val ≤ 100000 := by rw [hnmnv]; omega
      have hb3 : 0 ≤ nmx.val := by rw [hnmxv]; omega
      have hb4 : nmx.val ≤ 100000 := by rw [hnmxv]; omega
      obtain ⟨ra, hra, hrav⟩ := dfs_val_ex l hl nmn nmx hb1 hb2 hb3 hb4
      obtain ⟨rb, hrb, hrbv⟩ := dfs_val_ex r hr nmn nmx hb1 hb2 hb3 hb4
      obtain ⟨res, hres, hresv⟩ := if_gt_val ra rb
      refine ⟨res, ?_, ?_⟩
      · rw [dfs_node]
        simp only [hnmn, hnmx, bind_ok, hra, hrb]
        exact hres
      · rw [hresv, hrav, hrbv, hnmnv, hnmxv]
        simp only [dfsVal]
        rw [min_comm v.val mn.val, max_comm v.val mx.val]

  theorem pmax_eq_foldr : ∀ l : List (Int × Int),
      pmax l = l.foldr (fun p acc => max (absDiff p.1 p.2) acc) 0
    | [] => rfl
    | p :: l => by
      have h := pmax_eq_foldr l
      simp only [pmax, List.foldr_cons, h]

  theorem ancPairMax_eq (t : Tree) : ancPairMax t = pmax (ancPairs t) := by
    show (ancPairs t).foldr (fun p acc => max (absDiff p.1 p.2) acc) 0 = pmax (ancPairs t)
    rw [pmax_eq_foldr]

  theorem ancPairMax_node (v : Std.I64) (l r : Tree) :
      ancPairMax (.Node v l r) = max (treeSup [v.val] l) (treeSup [v.val] r) := by
    have h1 : pmax (ancPairsAux ([] : List Int) (.Node v l r)) =
        treeSup ([] : List Int) (.Node v l r) := pmax_ancPairsAux _ _
    rw [ancPairMax_eq]
    show pmax (ancPairsAux ([] : List Int) (.Node v l r)) = _
    rw [h1]
    show max (supAcc ([] : List Int) v.val)
        (max (treeSup [v.val] l) (treeSup [v.val] r)) = _
    have h2 : supAcc ([] : List Int) v.val = 0 := rfl
    have h3 := treeSup_nonneg [v.val] l
    rw [h2]
    omega

  theorem dfsVal_eq_treeSup (t : Tree) (v : Std.I64) (h0 : 0 ≤ v.val) (h1 : v.val ≤ 100000)
      (ht : ValuesIn t 0 100000) : dfsVal v.val v.val t = treeSup [v.val] t := by
    have hacc : ∀ a ∈ [v.val], 0 ≤ a ∧ a ≤ 100000 := by
      intro a ha
      have ha' : a = v.val := by simpa using ha
      subst ha'
      exact ⟨h0, h1⟩
    have h := dfsVal_eq t [v.val] (by simp) hacc ht
    rw [accMin_singleton v.val h1, accMax_singleton v.val h0] at h
    rw [h]
    have h2 := treeSup_nonneg [v.val] t
    omega

  theorem max_ancestor_diff_val (root : Tree) (hval : ValuesIn root 0 100000)
      (r : Std.I64) (h : max_ancestor_diff root = ok r) : r.val = ancPairMax root := by
    cases root with
    | Null =>
      simp only [max_ancestor_diff] at h
      have hr0 : (0#i64 : Std.I64) = r := by simpa using h
      subst hr0
      rw [ancPairMax_eq]
      rfl
    | Node v l r' =>
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 :=
        hval v.val (by rw [values_node]; exact List.mem_cons_self ..)
      have hl : ValuesIn l 0 100000 := ValuesIn.left hval
      have hr' : ValuesIn r' 0 100000 := ValuesIn.right hval
      obtain ⟨ra, hra, hrav⟩ := dfs_val_ex l hl v v hv.1 hv.2 hv.1 hv.2
      obtain ⟨rb, hrb, hrbv⟩ := dfs_val_ex r' hr' v v hv.1 hv.2 hv.1 hv.2
      obtain ⟨res, hres, hresv⟩ := if_gt_val ra rb
      have h2 : (do
          let a ← dfs l v v
          let b ← dfs r' v v
          if a > b then ok a else ok b) = ok r := h
      rw [hra, hrb] at h2
      simp only [bind_ok] at h2
      rw [hres] at h2
      have hrr : res = r := by simpa using h2
      subst hrr
      rw [hresv, hrav, hrbv, dfsVal_eq_treeSup l v hv.1 hv.2 hl,
        dfsVal_eq_treeSup r' v hv.1 hv.2 hr', ancPairMax_node]

  theorem treeSup_prune : ∀ (t t' : Tree), PruneAt t t' → ∀ acc, treeSup acc t' ≤ treeSup acc t
    | .Null, t', hp, acc => by
      simp only [PruneAt] at hp
    | .Node v l r, t', hp, acc => by
      simp only [PruneAt] at hp
      rcases hp with h0 | ⟨l', hl', rfl⟩ | ⟨r', hr', rfl⟩
      · subst h0
        have h2 := supAcc_nonneg acc v.val
        have h3 := treeSup_nonneg (v.val :: acc) l
        have h4 := treeSup_nonneg (v.val :: acc) r
        simp only [treeSup]
        omega
      · have ih := treeSup_prune l l' hl' (v.val :: acc)
        simp only [treeSup]
        omega
      · have ih := treeSup_prune r r' hr' (v.val :: acc)
        simp only [treeSup]
        omega

  theorem ancPairMax_prune (t t' : Tree) (h : PruneAt t t') : ancPairMax t' ≤ ancPairMax t := by
    rw [ancPairMax_eq, ancPairMax_eq]
    show pmax (ancPairsAux ([] : List Int) t') ≤ pmax (ancPairsAux ([] : List Int) t)
    rw [pmax_ancPairsAux, pmax_ancPairsAux]
    exact treeSup_prune t t' h []

  /-** spec_S12 [relational]: deleting one node and all its descendants can only decrease the
  result. -/
  theorem spec_12 (root root' : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000)
      (hprune : PruneAt root root')
      (hsize'_lo : 2 ≤ size root') (hsize'_hi : size root' ≤ 5000)
      (hval' : ValuesIn root' 0 100000) :
      ∀ res res' : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff root' = ok res' → res'.val ≤ res.val := by
    intro res res' hres hres'
    have h1 := max_ancestor_diff_val root hval res hres
    have h2 := max_ancestor_diff_val root' hval' res' hres'
    rw [h1, h2]
    exact ancPairMax_prune root root' hprune

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
