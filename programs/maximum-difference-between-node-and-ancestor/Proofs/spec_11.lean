import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_11` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary material for `spec_S11` (invariance under value reversal) -/

  /-- The `I64` built from an integer of `[0, 100000]` has that integer as value. -/
  theorem toI64_val_eq {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 100000) : (toI64 x).val = x := by
    show (BitVec.ofInt 64 x).toInt = x
    rw [BitVec.toInt_ofInt_eq_self (by omega) (by omega) (by omega)]

  /-- If `x - y` is small, then the `I64` subtraction succeeds and its value is the integer
  difference. -/
  theorem isub_ok (x y : Std.I64) (h0 : -100000 ≤ x.val - y.val) (h1 : x.val - y.val ≤ 100000) :
      ∃ z : Std.I64, (x - y) = ok z ∧ z.val = x.val - y.val := by
    have key := IScalar.sub_equiv (ty := .I64) x y
    have hinb : IScalar.inBounds .I64 (x.val - y.val) := by
      show -2 ^ (64 - 1) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ (64 - 1)
      constructor <;> omega
    cases hm : (x - y).match with
    | ok z =>
      rw [hm] at key
      exact ⟨z, Result.match.isOk.mp hm, key.2.1⟩
    | div => rw [hm] at key; exact absurd key not_false
    | vis e k => rw [hm] at key; exact absurd hinb key

  /-- The value of the maximum of two `I64`s, as computed by the program's final comparison. -/
  theorem ite_val_max (a b : Std.I64) :
      ((if a > b then a else b) : Std.I64).val = max a.val b.val := by
    by_cases h : a > b
    · have h' : a.val > b.val := h
      simp only [h, ite_true]
      omega
    · have h' : ¬ (a.val > b.val) := h
      simp only [h, ite_false]
      omega

  /-- Pure counterpart of `dfs`, on mathematical integers. -/
  def dfsSpec : Tree → Int → Int → Int
    | .Null, mn, mx => mx - mn
    | .Node v l r, mn, mx =>
      max (dfsSpec l (min v.val mn) (max v.val mx))
        (dfsSpec r (min v.val mn) (max v.val mx))

  /-- `dfs` computes `dfsSpec`, provided the node values and the running bounds are all in
  `[0, 100000]` (so that no overflow can occur). -/
  theorem dfs_spec : ∀ (t : Tree) (mn mx : Std.I64), ValuesIn t 0 100000 →
      0 ≤ mn.val → mn.val ≤ 100000 → 0 ≤ mx.val → mx.val ≤ 100000 →
      ∃ r : Std.I64, dfs t mn mx = ok r ∧ r.val = dfsSpec t mn.val mx.val := by
    intro t
    induction t with
    | Null =>
      intro mn mx _ hmn0 hmn1 hmx0 hmx1
      obtain ⟨z, hz, hzv⟩ := isub_ok mx mn (by omega) (by omega)
      refine ⟨z, ?_, ?_⟩
      · rw [dfs.eq_def]; exact hz
      · show z.val = mx.val - mn.val
        omega
    | Node v l r ihl ihr =>
      intro mn mx hval hmn0 hmn1 hmx0 hmx1
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hvalL : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvalR : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      set nmn : Std.I64 := if v < mn then v else mn with hnmn
      set nmx : Std.I64 := if v > mx then v else mx with hnmx
      have hnmn_val : nmn.val = min v.val mn.val := by
        rw [hnmn]
        by_cases h : v < mn
        · have h' : v.val < mn.val := h
          simp only [h, ite_true]; omega
        · have h' : ¬ (v.val < mn.val) := h
          simp only [h, ite_false]; omega
      have hnmx_val : nmx.val = max v.val mx.val := by
        rw [hnmx]
        by_cases h : v > mx
        · have h' : v.val > mx.val := h
          simp only [h, ite_true]; omega
        · have h' : ¬ (v.val > mx.val) := h
          simp only [h, ite_false]; omega
      have hnmn0 : 0 ≤ nmn.val := by rw [hnmn_val]; omega
      have hnmn1 : nmn.val ≤ 100000 := by rw [hnmn_val]; omega
      have hnmx0 : 0 ≤ nmx.val := by rw [hnmx_val]; omega
      have hnmx1 : nmx.val ≤ 100000 := by rw [hnmx_val]; omega
      obtain ⟨ra, hra, hraval⟩ := ihl nmn nmx hvalL hnmn0 hnmn1 hnmx0 hnmx1
      obtain ⟨rb, hrb, hrbval⟩ := ihr nmn nmx hvalR hnmn0 hnmn1 hnmx0 hnmx1
      have h1 : (if v.val < mn.val then ok v else ok mn : Result Std.I64) = ok nmn := by
        rw [hnmn]
        by_cases h : v.val < mn.val <;> simp [h]
      have h2 : (if v.val > mx.val then ok v else ok mx : Result Std.I64) = ok nmx := by
        rw [hnmx]
        by_cases h : v.val > mx.val <;> simp [h]
      have hunf : dfs (.Node v l r) mn mx = (do
          let nmn ← (if v < mn then ok v else ok mn : Result Std.I64)
          let nmx ← (if v > mx then ok v else ok mx : Result Std.I64)
          let a ← dfs l nmn nmx
          let b ← dfs r nmn nmx
          if a > b then ok a else ok b) := by
        refine Eq.trans (dfs.eq_def (.Node v l r) mn mx) ?_
        rfl
      have hdfs : dfs (.Node v l r) mn mx = (if ra > rb then ok ra else ok rb) := by
        rw [hunf]
        simp [h1, h2, hra, hrb]
      refine ⟨if ra > rb then ra else rb, ?_, ?_⟩
      · rw [hdfs]
        by_cases h : ra > rb <;> simp [h]
      · show (if ra > rb then ra else rb).val
          = max (dfsSpec l (min v.val mn.val) (max v.val mx.val))
              (dfsSpec r (min v.val mn.val) (max v.val mx.val))
        rw [hnmn_val, hnmx_val] at hraval hrbval
        rw [ite_val_max]
        rw [hraval, hrbval]

  /-- The list of node values of `revValues t`, when `t` has its values in `[0, 100000]`. -/
  theorem values_revValues : ∀ (t : Tree), ValuesIn t 0 100000 →
      values (revValues t) = (values t).map (fun x => 100000 - x) := by
    intro t
    induction t with
    | Null => intro _; rfl
    | Node v l r ihl ihr =>
      intro hval
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hvalL : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvalR : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvl : (toI64 (100000 - v.val)).val = 100000 - v.val :=
        toI64_val_eq (by omega) (by omega)
      show (toI64 (100000 - v.val)).val :: (values (revValues l) ++ values (revValues r))
          = (v.val :: (values l ++ values r)).map (fun x => 100000 - x)
      rw [hvl, ihl hvalL, ihr hvalR]
      simp [List.map_append]

  /-- Reversing the values preserves the `[0, 100000]` range condition. -/
  theorem valuesIn_revValues {t : Tree} (h : ValuesIn t 0 100000) :
      ValuesIn (revValues t) 0 100000 := by
    intro x hx
    rw [values_revValues t h] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy' := h y hy
    constructor <;> omega

  /-- `dfsSpec` is invariant under value reversal. -/
  theorem dfsSpec_rev : ∀ (t : Tree) (mn mx : Int), ValuesIn t 0 100000 →
      0 ≤ mn → mn ≤ 100000 → 0 ≤ mx → mx ≤ 100000 →
      dfsSpec (revValues t) (100000 - mx) (100000 - mn) = dfsSpec t mn mx := by
    intro t
    induction t with
    | Null =>
      intro mn mx _ _ _ _ _
      show (100000 - mn) - (100000 - mx) = mx - mn
      omega
    | Node v l r ihl ihr =>
      intro mn mx hval hmn0 hmn1 hmx0 hmx1
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hvalL : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvalR : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvl : (toI64 (100000 - v.val)).val = 100000 - v.val :=
        toI64_val_eq (by omega) (by omega)
      have hmn' : min (100000 - v.val) (100000 - mx) = 100000 - max v.val mx := by omega
      have hmx' : max (100000 - v.val) (100000 - mn) = 100000 - min v.val mn := by omega
      have hL : dfsSpec (revValues l) (min (100000 - v.val) (100000 - mx))
            (max (100000 - v.val) (100000 - mn))
          = dfsSpec l (min v.val mn) (max v.val mx) := by
        rw [hmn', hmx']
        exact ihl (min v.val mn) (max v.val mx) hvalL (by omega) (by omega) (by omega)
          (by omega)
      have hR : dfsSpec (revValues r) (min (100000 - v.val) (100000 - mx))
            (max (100000 - v.val) (100000 - mn))
          = dfsSpec r (min v.val mn) (max v.val mx) := by
        rw [hmn', hmx']
        exact ihr (min v.val mn) (max v.val mx) hvalR (by omega) (by omega) (by omega)
          (by omega)
      show max (dfsSpec (revValues l) (min (toI64 (100000 - v.val)).val (100000 - mx))
              (max (toI64 (100000 - v.val)).val (100000 - mn)))
            (dfsSpec (revValues r) (min (toI64 (100000 - v.val)).val (100000 - mx))
              (max (toI64 (100000 - v.val)).val (100000 - mn)))
          = max (dfsSpec l (min v.val mn) (max v.val mx))
              (dfsSpec r (min v.val mn) (max v.val mx))
      rw [hvl, hL, hR]

  /-** spec_S11 [invariance]: replacing every node value `v` with `100000 - v` does not change
  the result. -/
  theorem spec_11 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res res_rev : Std.I64,
        max_ancestor_diff root = ok res →
          max_ancestor_diff (revValues root) = ok res_rev → res_rev.val = res.val := by
    intro res res_rev hres hres_rev
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hvalL : ValuesIn l 0 100000 := fun x hx => hval x (by simp [values, hx])
      have hvalR : ValuesIn r 0 100000 := fun x hx => hval x (by simp [values, hx])
      obtain ⟨ra, hra, hraval⟩ := dfs_spec l v v hvalL hv.1 hv.2 hv.1 hv.2
      obtain ⟨rb, hrb, hrbval⟩ := dfs_spec r v v hvalR hv.1 hv.2 hv.1 hv.2
      have hmad : max_ancestor_diff (.Node v l r) = (if ra > rb then ok ra else ok rb) := by
        have h0 : max_ancestor_diff (.Node v l r) = (do
            let a ← dfs l v v
            let b ← dfs r v v
            if a > b then ok a else ok b) := rfl
        rw [h0]
        simp [hra, hrb]
      have hresval : res.val = max (dfsSpec l v.val v.val) (dfsSpec r v.val v.val) := by
        rw [hmad] at hres
        by_cases h : ra > rb
        · simp only [h, ite_true] at hres
          have hres' : ra = res := by simpa using hres
          have h' : ra.val > rb.val := h
          rw [← hres', ← hraval, ← hrbval]
          omega
        · simp only [h, ite_false] at hres
          have hres' : rb = res := by simpa using hres
          have h' : ¬ (ra.val > rb.val) := h
          rw [← hres', ← hraval, ← hrbval]
          omega
      have hrev_root : revValues (.Node v l r)
          = .Node (toI64 (100000 - v.val)) (revValues l) (revValues r) := rfl
      have hvl : (toI64 (100000 - v.val)).val = 100000 - v.val :=
        toI64_val_eq (by omega) (by omega)
      have hvalL' : ValuesIn (revValues l) 0 100000 := valuesIn_revValues hvalL
      have hvalR' : ValuesIn (revValues r) 0 100000 := valuesIn_revValues hvalR
      have hv0 : 0 ≤ (toI64 (100000 - v.val)).val := by rw [hvl]; omega
      have hv1 : (toI64 (100000 - v.val)).val ≤ 100000 := by rw [hvl]; omega
      obtain ⟨ra', hra', hraval'⟩ :=
        dfs_spec (revValues l) (toI64 (100000 - v.val)) (toI64 (100000 - v.val))
          hvalL' hv0 hv1 hv0 hv1
      obtain ⟨rb', hrb', hrbval'⟩ :=
        dfs_spec (revValues r) (toI64 (100000 - v.val)) (toI64 (100000 - v.val))
          hvalR' hv0 hv1 hv0 hv1
      have hmad' : max_ancestor_diff (revValues (.Node v l r))
          = (if ra' > rb' then ok ra' else ok rb') := by
        have h0 : max_ancestor_diff (revValues (.Node v l r)) = (do
            let a ← dfs (revValues l) (toI64 (100000 - v.val)) (toI64 (100000 - v.val))
            let b ← dfs (revValues r) (toI64 (100000 - v.val)) (toI64 (100000 - v.val))
            if a > b then ok a else ok b) := by
          rw [hrev_root]
          rfl
        rw [h0]
        simp [hra', hrb']
      have hresval' : res_rev.val = max (dfsSpec l v.val v.val) (dfsSpec r v.val v.val) := by
        rw [hmad'] at hres_rev
        by_cases h : ra' > rb'
        · simp only [h, ite_true] at hres_rev
          have hres' : ra' = res_rev := by simpa using hres_rev
          rw [hvl] at hraval' hrbval'
          rw [dfsSpec_rev l v.val v.val hvalL hv.1 hv.2 hv.1 hv.2] at hraval'
          rw [dfsSpec_rev r v.val v.val hvalR hv.1 hv.2 hv.1 hv.2] at hrbval'
          have h' : ra'.val > rb'.val := h
          rw [← hres', ← hraval', ← hrbval']
          omega
        · simp only [h, ite_false] at hres_rev
          have hres' : rb' = res_rev := by simpa using hres_rev
          rw [hvl] at hraval' hrbval'
          rw [dfsSpec_rev l v.val v.val hvalL hv.1 hv.2 hv.1 hv.2] at hraval'
          rw [dfsSpec_rev r v.val v.val hvalR hv.1 hv.2 hv.1 hv.2] at hrbval'
          have h' : ¬ (ra'.val > rb'.val) := h
          rw [← hres', ← hraval', ← hrbval']
          omega
      rw [hresval', hresval]

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
