import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_1` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary material for `spec_S1`

  The proof of `spec_S1` needs a `foldr`-based account of the extrema of lists
  (`listMax`/`listMin` are `foldl`-based), and an integer model of `dfs`. -/

  /-- `foldr` variant of `listMax`: the maximum of a list of integers, `0` for `[]`. -/
  def fmax (l : List Int) : Int := l.foldr max 0

  /-- `foldr` variant of `listMin`: the minimum of a list of integers, `100000` for `[]`. -/
  def fmin (l : List Int) : Int := l.foldr min 100000

  /-- All the entries of a list of integers lie in the interval `[0, 100000]`. -/
  def Bounded (l : List Int) : Prop := ∀ x ∈ l, 0 ≤ x ∧ x ≤ 100000

  theorem fmax_cons (a : Int) (l : List Int) : fmax (a :: l) = max a (fmax l) := rfl

  theorem fmin_cons (a : Int) (l : List Int) : fmin (a :: l) = min a (fmin l) := rfl

  theorem fmax_nonneg (l : List Int) : 0 ≤ fmax l := by
    induction l with
    | nil => simp [fmax]
    | cons a t ih =>
      rw [fmax_cons]
      omega

  theorem fmin_le (l : List Int) : fmin l ≤ 100000 := by
    induction l with
    | nil => simp [fmin]
    | cons a t ih =>
      rw [fmin_cons]
      omega

  theorem le_fmax {a : Int} {l : List Int} (h : a ∈ l) : a ≤ fmax l := by
    induction l with
    | nil => simp at h
    | cons b t ih =>
      rw [fmax_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

  theorem fmin_le_elem {a : Int} {l : List Int} (h : a ∈ l) : fmin l ≤ a := by
    induction l with
    | nil => simp at h
    | cons b t ih =>
      rw [fmin_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

  theorem fmax_le_of_forall {l : List Int} {c : Int} (h : ∀ x ∈ l, x ≤ c) (h0 : 0 ≤ c) :
      fmax l ≤ c := by
    induction l with
    | nil => simpa [fmax] using h0
    | cons a t ih =>
      rw [fmax_cons]
      exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

  theorem le_fmin_of_forall {l : List Int} {c : Int} (h : ∀ x ∈ l, c ≤ x) (h0 : c ≤ 100000) :
      c ≤ fmin l := by
    induction l with
    | nil => simpa [fmin] using h0
    | cons a t ih =>
      rw [fmin_cons]
      exact le_min (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

  /-- The maximum of a nonempty bounded list is attained. -/
  theorem fmax_eq_mem {l : List Int} (hne : l ≠ []) (h0 : ∀ x ∈ l, 0 ≤ x) :
      ∃ a ∈ l, a = fmax l := by
    induction l with
    | nil => exact absurd rfl hne
    | cons b t ih =>
      rw [fmax_cons]
      by_cases hbt : fmax t ≤ b
      · exact ⟨b, by simp, by omega⟩
      · push_neg at hbt
        have ht : t ≠ [] := by
          rintro rfl
          simp [fmax] at hbt
          have := h0 b (by simp)
          omega
        obtain ⟨a, ha, hav⟩ := ih ht (fun x hx => h0 x (by simp [hx]))
        exact ⟨a, by simp [ha], by omega⟩

  /-- The minimum of a nonempty bounded list is attained. -/
  theorem fmin_eq_mem {l : List Int} (hne : l ≠ []) (h100 : ∀ x ∈ l, x ≤ 100000) :
      ∃ a ∈ l, a = fmin l := by
    induction l with
    | nil => exact absurd rfl hne
    | cons b t ih =>
      rw [fmin_cons]
      by_cases hbt : b ≤ fmin t
      · exact ⟨b, by simp, by omega⟩
      · push_neg at hbt
        have ht : t ≠ [] := by
          rintro rfl
          simp [fmin] at hbt
          have := h100 b (by simp)
          omega
        obtain ⟨a, ha, hav⟩ := ih ht (fun x hx => h100 x (by simp [hx]))
        exact ⟨a, by simp [ha], by omega⟩

  theorem fmax_append (l₁ l₂ : List Int) : fmax (l₁ ++ l₂) = max (fmax l₁) (fmax l₂) := by
    induction l₁ with
    | nil =>
      have h : 0 ≤ fmax l₂ := fmax_nonneg l₂
      rw [List.nil_append]
      show fmax l₂ = max 0 (fmax l₂)
      omega
    | cons a t ih =>
      simp only [List.cons_append, fmax_cons, ih]
      omega

  theorem fmin_append (l₁ l₂ : List Int) : fmin (l₁ ++ l₂) = min (fmin l₁) (fmin l₂) := by
    induction l₁ with
    | nil =>
      have h : fmin l₂ ≤ 100000 := fmin_le l₂
      rw [List.nil_append]
      show fmin l₂ = min 100000 (fmin l₂)
      omega
    | cons a t ih =>
      simp only [List.cons_append, fmin_cons, ih]
      omega

  theorem listMax_eq_fmax (l : List Int) : listMax l = fmax l := by
    have key : ∀ (b : Int), 0 ≤ b → l.foldl max b = max b (fmax l) := by
      induction l with
      | nil => intro b hb; simp [fmax]; omega
      | cons a t ih =>
        intro b hb
        simp only [List.foldl_cons, fmax_cons]
        rw [ih (max b a) (by omega)]
        omega
    rw [listMax, key 0 (le_refl 0)]
    have h := fmax_nonneg l
    omega

  theorem listMin_eq_fmin (l : List Int) : listMin l = fmin l := by
    have key : ∀ (b : Int), b ≤ 100000 → l.foldl min b = min b (fmin l) := by
      induction l with
      | nil => intro b hb; simp [fmin]; omega
      | cons a t ih =>
        intro b hb
        simp only [List.foldl_cons, fmin_cons]
        rw [ih (min b a) (by omega)]
        omega
    rw [listMin, key 100000 (le_refl 100000)]
    have h := fmin_le l
    omega

  theorem listMax_cons (a : Int) (l : List Int) : listMax (a :: l) = max a (listMax l) := by
    rw [listMax_eq_fmax, listMax_eq_fmax]
    exact fmax_cons a l

  theorem listMin_cons (a : Int) (l : List Int) : listMin (a :: l) = min a (listMin l) := by
    rw [listMin_eq_fmin, listMin_eq_fmin]
    exact fmin_cons a l

  theorem listMin_le_listMax {l : List Int} (hne : l ≠ []) : listMin l ≤ listMax l := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l hne
    rw [listMin_eq_fmin, listMax_eq_fmax]
    exact le_trans (fmin_le_elem ha) (le_fmax ha)

  /-- The maximum of `absDiff p.1 p.2` over a list of pairs (`0` for the empty list). -/
  def pmax (l : List (Int × Int)) : Int :=
    l.foldr (fun p acc => max (absDiff p.1 p.2) acc) 0

  theorem ancPairMax_eq_pmax (t : Tree) : ancPairMax t = pmax (ancPairs t) := rfl

  theorem pmax_cons (p : Int × Int) (l : List (Int × Int)) :
      pmax (p :: l) = max (absDiff p.1 p.2) (pmax l) := rfl

  theorem pmax_nonneg (l : List (Int × Int)) : 0 ≤ pmax l := by
    induction l with
    | nil => simp [pmax]
    | cons p t ih =>
      rw [pmax_cons]
      omega

  theorem le_pmax {p : Int × Int} {l : List (Int × Int)} (h : p ∈ l) :
      absDiff p.1 p.2 ≤ pmax l := by
    induction l with
    | nil => simp at h
    | cons q t ih =>
      rw [pmax_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

  theorem pmax_le_of_forall {l : List (Int × Int)} {c : Int}
      (h : ∀ p ∈ l, absDiff p.1 p.2 ≤ c) (h0 : 0 ≤ c) : pmax l ≤ c := by
    induction l with
    | nil => simpa [pmax] using h0
    | cons p t ih =>
      rw [pmax_cons]
      exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

  theorem pmax_append (l₁ l₂ : List (Int × Int)) :
      pmax (l₁ ++ l₂) = max (pmax l₁) (pmax l₂) := by
    induction l₁ with
    | nil =>
      have h : 0 ≤ pmax l₂ := pmax_nonneg l₂
      rw [List.nil_append]
      show pmax l₂ = max 0 (pmax l₂)
      omega
    | cons p t ih =>
      simp only [List.cons_append, pmax_cons, ih]
      omega

  /-- `|a - x|`, maximized over the entries `a` of a nonempty bounded list. -/
  theorem pmax_map_pair (acc : List Int) (x : Int) (hne : acc ≠ []) (hb : Bounded acc) :
      pmax (acc.map (fun a => (a, x))) = max (listMax acc - x) (x - listMin acc) := by
    have hmM : listMin acc ≤ listMax acc := listMin_le_listMax hne
    rw [listMin_eq_fmin, listMax_eq_fmax] at hmM ⊢
    apply le_antisymm
    · apply pmax_le_of_forall
      · intro p hp
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
        have h1 : a ≤ fmax acc := le_fmax ha
        have h2 : fmin acc ≤ a := fmin_le_elem ha
        have h3 : max (a - x) (x - a) ≤ max (fmax acc - x) (x - fmin acc) := by omega
        simpa [absDiff] using h3
      · omega
    · obtain ⟨a, ha, hav⟩ := fmax_eq_mem hne (fun y hy => (hb y hy).1)
      obtain ⟨b, hbm, hbv⟩ := fmin_eq_mem hne (fun y hy => (hb y hy).2)
      have h1 : absDiff a x ≤ pmax (acc.map (fun a => (a, x))) :=
        le_pmax (List.mem_map.mpr ⟨a, ha, rfl⟩)
      have h2 : absDiff b x ≤ pmax (acc.map (fun a => (a, x))) :=
        le_pmax (List.mem_map.mpr ⟨b, hbm, rfl⟩)
      rw [← hav, ← hbv]
      simp only [absDiff] at h1 h2
      omega

  /-- An integer model of the value computed by `dfs t mn mx`: the maximum, over all
  root-to-`Null` extensions below `t`, of the difference between the maximum and the minimum
  of the values on the extended path (`acc` collects the values of the proper ancestors of `t`). -/
  def dfsSpec (acc : List Int) (t : Tree) : Int :=
    match t with
    | .Null => listMax acc - listMin acc
    | .Node v l r => max (dfsSpec (v.val :: acc) l) (dfsSpec (v.val :: acc) r)

  /-- `dfsSpec` only depends on the extrema of the ancestor values and on the ancestor pairs. -/
  theorem dfsSpec_eq : ∀ (t : Tree), (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      ∀ (acc : List Int), acc ≠ [] → Bounded acc →
        dfsSpec acc t = max (listMax acc - listMin acc) (pmax (ancPairsAux acc t)) := by
    intro t
    induction t with
    | Null =>
      intro ht acc hne hb
      have hmM : listMin acc ≤ listMax acc := listMin_le_listMax hne
      have h0 : pmax (ancPairsAux acc Tree.Null) = 0 := rfl
      simp only [dfsSpec]
      rw [h0]
      omega
    | Node v l r ihl ihr =>
      intro ht acc hne hb
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := ht v.val (by simp [values])
      have hl : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hr : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hb' : Bounded (v.val :: acc) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hb x hx
      have hne' : (v.val :: acc) ≠ [] := by simp
      have e1 := ihl hl (v.val :: acc) hne' hb'
      have e2 := ihr hr (v.val :: acc) hne' hb'
      have hmap := pmax_map_pair acc v.val hne hb
      have hmM : listMin acc ≤ listMax acc := listMin_le_listMax hne
      have hkey : listMax (v.val :: acc) - listMin (v.val :: acc)
          = max (listMax acc - listMin acc)
              (max (listMax acc - v.val) (v.val - listMin acc)) := by
        rw [listMax_cons, listMin_cons]
        omega
      have hsplit : ancPairsAux acc (Tree.Node v l r)
          = acc.map (fun a => (a, v.val)) ++ ancPairsAux (v.val :: acc) l
            ++ ancPairsAux (v.val :: acc) r := rfl
      have hp := pmax_nonneg (ancPairsAux (v.val :: acc) l)
      have hq := pmax_nonneg (ancPairsAux (v.val :: acc) r)
      show max (dfsSpec (v.val :: acc) l) (dfsSpec (v.val :: acc) r)
        = max (listMax acc - listMin acc) (pmax (ancPairsAux acc (Tree.Node v l r)))
      rw [e1, e2, hkey, hsplit, pmax_append, pmax_append, hmap]
      omega

  /-- The proper ancestor pairs of a root. -/
  theorem ancPairs_node (v : Std.I64) (l r : Tree) :
      ancPairs (Tree.Node v l r) = ancPairsAux [v.val] l ++ ancPairsAux [v.val] r := by
    simp [ancPairs, ancPairsAux]

  /-- The body of `max_ancestor_diff` on a nonempty tree. -/
  theorem max_ancestor_diff_node (v : Std.I64) (l r : Tree) :
      max_ancestor_diff (Tree.Node v l r) =
        (do let x ← dfs l v v
            let y ← dfs r v v
            if x > y then Result.ok x else Result.ok y) := by
    rw [max_ancestor_diff.eq_def]

  /-- A subtraction of a nonnegative `I64` from a bounded `I64` does not overflow and returns
  the expected value. -/
  theorem i64_sub_ok {x y : Std.I64} (h1 : y.val ≤ x.val) (h2 : x.val ≤ 100000)
      (h3 : 0 ≤ y.val) :
      ∃ z : Std.I64, x - y = ok z ∧ z.val = x.val - y.val := by
    have hb : IScalar.inBounds IScalarTy.I64 (x.val - y.val) := by
      have hx := IScalar.hBounds x
      have hy := IScalar.hBounds y
      simp only [IScalar.inBounds, IScalarTy.numBits]
      constructor <;> omega
    have hcb : IScalar.check_bounds IScalarTy.I64 (x.val - y.val) :=
      (IScalar.check_bounds_eq_inBounds _ _).mpr hb
    refine ⟨IScalar.ofIntCore (x.val - y.val) (IScalar.check_bounds_imp_inBounds hcb), ?_, ?_⟩
    · rw [show (x - y : Result Std.I64) = IScalar.tryMk IScalarTy.I64 (x.val - y.val) from rfl,
        IScalar.tryMk, IScalar.tryMkOpt, dif_pos hcb]
      simp [Result.ofOption]
    · exact IScalar.ofInt_val_eq _

  /-- The body of `dfs` on a nonempty tree. -/
  theorem dfs_node (v : Std.I64) (l r : Tree) (mn mx : Std.I64) :
      dfs (Tree.Node v l r) mn mx =
        (do let nmn ← (if v < mn then Result.ok v else Result.ok mn)
            let nmx ← (if v > mx then Result.ok v else Result.ok mx)
            let a ← dfs l nmn nmx
            let b ← dfs r nmn nmx
            if a > b then Result.ok a else Result.ok b) := by
    rw [dfs.eq_def]

  /-- `dfs t mn mx`, where `mn`/`mx` are the minimum/maximum of the values of the proper
  ancestors of `t`, computes `dfsSpec acc t`. -/
  theorem dfs_spec : ∀ (t : Tree), (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      ∀ (acc : List Int) (mn mx : Std.I64), acc ≠ [] → Bounded acc →
        mn.val = listMin acc → mx.val = listMax acc →
        ∃ res, dfs t mn mx = ok res ∧ res.val = dfsSpec acc t := by
    intro t
    induction t with
    | Null =>
      intro ht acc mn mx hne hb hmn hmx
      have hmn0 : 0 ≤ mn.val := by
        rw [hmn, listMin_eq_fmin]
        exact le_fmin_of_forall (fun x hx => (hb x hx).1) (by norm_num)
      have hmx0 : mx.val ≤ 100000 := by
        rw [hmx, listMax_eq_fmax]
        exact fmax_le_of_forall (fun x hx => (hb x hx).2) (by norm_num)
      have hmM : mn.val ≤ mx.val := by
        rw [hmn, hmx, listMin_eq_fmin, listMax_eq_fmax]
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil acc hne
        exact le_trans (fmin_le_elem ha) (le_fmax ha)
      obtain ⟨res, hres, hresv⟩ := i64_sub_ok hmM hmx0 hmn0
      refine ⟨res, ?_, ?_⟩
      · rw [dfs.eq_def]
        exact hres
      · rw [hresv, hmn, hmx]
        rfl
    | Node v l r ihl ihr =>
      intro ht acc mn mx hne hb hmn hmx
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := ht v.val (by simp [values])
      have hl : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hr : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hb' : Bounded (v.val :: acc) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hb x hx
      have hne' : (v.val :: acc) ≠ [] := by simp
      set nmn : Std.I64 := if v < mn then v else mn with hnmn
      set nmx : Std.I64 := if v > mx then v else mx with hnmx
      have hmn' : nmn.val = listMin (v.val :: acc) := by
        rw [listMin_cons, hnmn]
        by_cases hc : v < mn
        · rw [if_pos hc]
          have hcv : v.val < mn.val := by simpa using hc
          rw [hmn] at hcv
          omega
        · rw [if_neg hc]
          have hcv : mn.val ≤ v.val := by
            have h1 : ¬ (v.val < mn.val) := fun h2 => hc (by simpa using h2)
            omega
          rw [hmn]
          omega
      have hmx' : nmx.val = listMax (v.val :: acc) := by
        rw [listMax_cons, hnmx]
        by_cases hc : v > mx
        · rw [if_pos hc]
          have hcv : mx.val < v.val := by simpa using hc
          rw [hmx] at hcv
          omega
        · rw [if_neg hc]
          have hcv : v.val ≤ mx.val := by
            have h1 : ¬ (mx.val < v.val) := fun h2 => hc (by simpa using h2)
            omega
          rw [hmx]
          omega
      obtain ⟨a, ha, haval⟩ := ihl hl (v.val :: acc) nmn nmx hne' hb' hmn' hmx'
      obtain ⟨b, hb2, hbval⟩ := ihr hr (v.val :: acc) nmn nmx hne' hb' hmn' hmx'
      have hstep1 : (if v < mn then Result.ok v else Result.ok mn) = Result.ok nmn := by
        rw [hnmn]
        by_cases hc : v < mn
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
      have hstep2 : (if v > mx then Result.ok v else Result.ok mx) = Result.ok nmx := by
        rw [hnmx]
        by_cases hc : v > mx
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
      have hres : dfs (Tree.Node v l r) mn mx = Result.ok (if a > b then a else b) := by
        rw [dfs_node]
        simp only [hstep1, hstep2, bind_ok, ha, hb2]
        by_cases hc : a > b
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
      refine ⟨if a > b then a else b, hres, ?_⟩
      have hmaxab : (if a > b then a else b).val = max a.val b.val := by
        by_cases hc : a > b
        · rw [if_pos hc]
          have hcv : b.val < a.val := by simpa using hc
          omega
        · rw [if_neg hc]
          have hcv : a.val ≤ b.val := by
            have h1 : ¬ (b.val < a.val) := fun h2 => hc (by simpa using h2)
            omega
          omega
      rw [hmaxab, haval, hbval]
      rfl

  /-! ## Specifications -/

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry

  /-** spec_S1 (MAIN) [functional]: the result is the maximum, over all pairs of nodes `(a, b)` of
  `root` such that `a` is a proper ancestor of `b`, of `|value a - value b|`. -/
  theorem spec_1 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∃ res : Std.I64, max_ancestor_diff root = ok res ∧ res.val = ancPairMax root := by
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      have ht : ∀ x ∈ values (Tree.Node v l r), 0 ≤ x ∧ x ≤ 100000 := hval
      have hl : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hr : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := fun x hx => ht x (by simp [values, hx])
      have hv : 0 ≤ v.val ∧ v.val ≤ 100000 := ht v.val (by simp [values])
      have hb1 : Bounded [v.val] := by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx]
        exact hv
      have hne1 : ([v.val] : List Int) ≠ [] := by simp
      have hmin1 : listMin [v.val] = v.val := by
        rw [listMin_cons]
        show min v.val 100000 = v.val
        omega
      have hmax1 : listMax [v.val] = v.val := by
        rw [listMax_cons]
        show max v.val 0 = v.val
        omega
      obtain ⟨a, ha, haval⟩ := dfs_spec l hl [v.val] v v hne1 hb1 (by rw [hmin1]) (by rw [hmax1])
      obtain ⟨b, hb2, hbval⟩ := dfs_spec r hr [v.val] v v hne1 hb1 (by rw [hmin1]) (by rw [hmax1])
      refine ⟨if a > b then a else b, ?_, ?_⟩
      · rw [max_ancestor_diff_node]
        simp only [ha, hb2, bind_ok]
        by_cases hc : a > b
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
      · have hmaxab : (if a > b then a else b).val = max a.val b.val := by
          by_cases hc : a > b
          · rw [if_pos hc]
            have hcv : b.val < a.val := by simpa using hc
            omega
          · rw [if_neg hc]
            have hcv : a.val ≤ b.val := by
              have h1 : ¬ (b.val < a.val) := fun h2 => hc (by simpa using h2)
              omega
            omega
        rw [hmaxab, haval, hbval]
        rw [dfsSpec_eq l hl [v.val] hne1 hb1, dfsSpec_eq r hr [v.val] hne1 hb1]
        rw [ancPairMax_eq_pmax, ancPairs_node, pmax_append, hmax1, hmin1]
        have hp := pmax_nonneg (ancPairsAux [v.val] l)
        have hq := pmax_nonneg (ancPairsAux [v.val] r)
        omega

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
