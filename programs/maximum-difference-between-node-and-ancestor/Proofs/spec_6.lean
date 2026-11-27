import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_6` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary lemmas used by `spec_S6` -/

  /-- If a bind produces `ok r`, then the first component produced an `ok` value. -/
  theorem Result_bind_ok_elim {α β : Type} {m : Result α} {k : α → Result β} {r : β}
      (h : (m >>= k) = ok r) : ∃ a, m = ok a ∧ k a = ok r := by
    revert h
    refine Result.cases (motive :=
      fun m => (m >>= k) = ok r → ∃ a, m = ok a ∧ k a = ok r) m ?_ ?_ ?_
    · intro a h
      exact ⟨a, rfl, by simpa using h⟩
    · intro i k' h
      simp at h
    · intro h
      simp at h

  /-- An `if` whose branches are `ok` values. -/
  theorem ite_ok_ite {α : Type} (c : Prop) [Decidable c] (a b : α) :
      ((if c then ok a else ok b) : Result α) = ok (if c then a else b) := by
    by_cases h : c <;> simp [h]

  /-- Value of the "min" `if`. -/
  theorem ite_min_eq_snd (v mn : Std.I64) (h : v.val = mn.val) :
      (if v < mn then v else mn).val = mn.val := by
    by_cases hlt : v < mn
    · rw [if_pos hlt]
      have : v.val < mn.val := by simpa using hlt
      omega
    · simp only [if_neg hlt]

  /-- Value of the "max" `if`. -/
  theorem ite_max_eq_snd (v mx : Std.I64) (h : v.val = mx.val) :
      (if v > mx then v else mx).val = mx.val := by
    by_cases hlt : v > mx
    · rw [if_pos hlt]
      have : mx.val < v.val := by simpa using hlt
      omega
    · simp only [if_neg hlt]

  /-- The "min" `if` is bounded by its second argument. -/
  theorem ite_min_le_snd (v mn : Std.I64) : (if v < mn then v else mn).val ≤ mn.val := by
    by_cases hlt : v < mn
    · rw [if_pos hlt]
      have : v.val < mn.val := by simpa using hlt
      omega
    · simp only [if_neg hlt]
      omega

  /-- The "min" `if` is bounded by its first argument. -/
  theorem ite_min_le_fst (v mn : Std.I64) : (if v < mn then v else mn).val ≤ v.val := by
    by_cases hlt : v < mn
    · simp only [if_pos hlt]
      omega
    · rw [if_neg hlt]
      have : ¬ (v.val < mn.val) := by simpa using hlt
      omega

  /-- The "max" `if` bounds its second argument. -/
  theorem ite_max_ge_snd (v mx : Std.I64) : mx.val ≤ (if v > mx then v else mx).val := by
    by_cases hlt : v > mx
    · rw [if_pos hlt]
      have : mx.val < v.val := by simpa using hlt
      omega
    · simp only [if_neg hlt]
      omega

  /-- The "max" `if` bounds its first argument. -/
  theorem ite_max_ge_fst (v mx : Std.I64) : v.val ≤ (if v > mx then v else mx).val := by
    by_cases hlt : v > mx
    · simp only [if_pos hlt]
      omega
    · rw [if_neg hlt]
      have : ¬ (mx.val < v.val) := by simpa using hlt
      omega

  /-- The "min" `if` is bounded by the "max" `if`. -/
  theorem ite_min_le_ite_max (v mn mx : Std.I64) (h : mn.val ≤ mx.val) :
      (if v < mn then v else mn).val ≤ (if v > mx then v else mx).val := by
    have h1 := ite_min_le_snd v mn
    have h2 := ite_max_ge_snd v mx
    omega

  /-- If the two `if`s have the same value, then everything is equal. -/
  theorem ite_min_eq_ite_max (v mn mx : Std.I64) (h : mn.val ≤ mx.val)
      (heq : (if v < mn then v else mn).val = (if v > mx then v else mx).val) :
      mn.val = mx.val ∧ v.val = mn.val ∧ (if v < mn then v else mn).val = mn.val := by
    have h1 := ite_min_le_snd v mn
    have h2 := ite_max_ge_snd v mx
    have h3 := ite_min_le_fst v mn
    have h4 := ite_max_ge_fst v mx
    omega

  /-- Value of a `max`-shaped `if` over `ok` values. -/
  theorem ite_max_ok (a b r : Std.I64)
      (h : (if a > b then ok a else ok b) = ok r) : r.val = max a.val b.val := by
    by_cases hab : a > b
    · rw [if_pos hab] at h
      have hra : r = a := by simpa using h.symm
      have h' : b.val < a.val := by simpa using hab
      rw [hra, max_eq_left (le_of_lt h')]
    · rw [if_neg hab] at h
      have hrb : r = b := by simpa using h.symm
      have h' : a.val ≤ b.val := by
        have h'' : ¬ (b.val < a.val) := by simpa using hab
        omega
      rw [hrb, max_eq_right h']

  /-- Characterization of the result of `dfs`. -/
  theorem dfs_ok_spec (t : Tree) :
      ∀ (mn mx res : Std.I64), mn.val ≤ mx.val → dfs t mn mx = ok res →
        0 ≤ res.val ∧
          (res.val = 0 ↔ (mn.val = mx.val ∧ ∀ x ∈ values t, x = mn.val)) := by
    induction t with
    | Null =>
      intro mn mx res hle hres
      simp only [dfs.eq_def] at hres
      have hsub := Std.IScalar.sub_equiv mx mn
      rw [hres] at hsub
      simp only [Result.match.ok] at hsub
      obtain ⟨-, hresval, -⟩ := hsub
      refine ⟨by omega, ?_⟩
      constructor
      · intro h0
        exact ⟨by omega, by simp [values]⟩
      · rintro ⟨hmn, -⟩
        omega
    | Node v l r ihl ihr =>
      intro mn mx res hle hres
      rw [dfs.eq_def (Tree.Node v l r) mn mx] at hres
      dsimp only at hres
      rw [ite_ok_ite, ite_ok_ite] at hres
      simp only [bind_ok] at hres
      obtain ⟨a, ha, hres⟩ := Result_bind_ok_elim hres
      obtain ⟨b, hb, hres⟩ := Result_bind_ok_elim hres
      have hmax : res.val = max a.val b.val := ite_max_ok a b res hres
      obtain ⟨ha0, haiff⟩ :=
        ihl (if v < mn then v else mn) (if v > mx then v else mx) a
          (ite_min_le_ite_max v mn mx hle) ha
      obtain ⟨hb0, hbiff⟩ :=
        ihr (if v < mn then v else mn) (if v > mx then v else mx) b
          (ite_min_le_ite_max v mn mx hle) hb
      refine ⟨?_, ?_⟩
      · have h1 := le_max_left a.val b.val
        have h2 := le_max_right a.val b.val
        omega
      · constructor
        · intro h0
          have ha0' : a.val = 0 := by
            have := le_max_left a.val b.val
            omega
          have hb0' : b.val = 0 := by
            have := le_max_right a.val b.val
            omega
          obtain ⟨hmne, hve, hmite⟩ := ite_min_eq_ite_max v mn mx hle (haiff.mp ha0').1
          refine ⟨hmne, ?_⟩
          intro x hx
          simp only [values, List.mem_cons, List.mem_append] at hx
          rcases hx with rfl | hx | hx
          · exact hve
          · exact ((haiff.mp ha0').2 x hx).trans hmite
          · exact ((hbiff.mp hb0').2 x hx).trans hmite
        · rintro ⟨hmne, hall⟩
          have hmem : ∀ {x : Int}, x ∈ values l ∨ x ∈ values r →
              x ∈ values (Tree.Node v l r) := by
            intro x hx
            simp only [values, List.mem_cons, List.mem_append]
            tauto
          have hve : v.val = mn.val := hall v.val (by simp [values])
          have hln : ∀ x ∈ values l, x = mn.val := fun x hx => hall x (hmem (Or.inl hx))
          have hrn : ∀ x ∈ values r, x = mn.val := fun x hx => hall x (hmem (Or.inr hx))
          have hmit : (if v < mn then v else mn).val = mn.val := ite_min_eq_snd v mn hve
          have hmat : (if v > mx then v else mx).val = mx.val :=
            ite_max_eq_snd v mx (hve.trans hmne)
          have heq : (if v < mn then v else mn).val = (if v > mx then v else mx).val := by
            rw [hmit, hmat, hmne]
          have ha0' : a.val = 0 :=
            haiff.mpr ⟨heq, fun x hx => (hln x hx).trans hmit.symm⟩
          have hb0' : b.val = 0 :=
            hbiff.mpr ⟨heq, fun x hx => (hrn x hx).trans hmit.symm⟩
          rw [hmax, ha0', hb0']
          simp

  /-** spec_S6 [edge]: the result is `0` if and only if every node of `root` has the same value. -/
  theorem spec_6 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        (res.val = 0 ↔ AllValuesEqual root) := by
    intro res hres
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      simp only [max_ancestor_diff] at hres
      obtain ⟨a, ha, hres⟩ := Result_bind_ok_elim hres
      obtain ⟨b, hb, hres⟩ := Result_bind_ok_elim hres
      have hmax : res.val = max a.val b.val := ite_max_ok a b res hres
      obtain ⟨ha0, haiff⟩ :=
        dfs_ok_spec l v v a (le_refl _) ha
      obtain ⟨hb0, hbiff⟩ :=
        dfs_ok_spec r v v b (le_refl _) hb
      simp only [true_and] at haiff hbiff
      constructor
      · intro h0
        have ha0' : a.val = 0 := by
          have := le_max_left a.val b.val
          omega
        have hb0' : b.val = 0 := by
          have := le_max_right a.val b.val
          omega
        refine ⟨v.val, ?_⟩
        intro x hx
        simp only [values, List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · rfl
        · exact haiff.mp ha0' x hx
        · exact hbiff.mp hb0' x hx
      · rintro ⟨c, hall⟩
        have hmem : ∀ {x : Int}, x ∈ values l ∨ x ∈ values r → x ∈ values (Tree.Node v l r) := by
          intro x hx
          simp only [values, List.mem_cons, List.mem_append]
          tauto
        have hvc : v.val = c := hall v.val (by simp [values])
        have hall' : ∀ x ∈ values (Tree.Node v l r), x = v.val := by
          intro x hx
          rw [hall x hx, ← hvc]
        have ha0' : a.val = 0 := haiff.mpr (fun x hx => hall' x (hmem (Or.inl hx)))
        have hb0' : b.val = 0 := hbiff.mpr (fun x hx => hall' x (hmem (Or.inr hx)))
        rw [hmax, ha0', hb0']
        simp

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
