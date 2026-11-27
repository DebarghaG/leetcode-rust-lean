import Aegis.MaxAncestorDiff.Code.Funs

/-
Proof of `AegisSpec.MaxAncestorDiff.spec_4` (maximum-difference-between-node-and-ancestor).
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

  /-! ### Auxiliary definitions and lemmas, used in the proof of `spec_S4` -/

  /-- The pairs `(a, b)` of elements of a list, viewed as a chain of ancestors: the lists of
  ancestor values are ordered from the nearest ancestor to the farthest, so `a` must occur
  strictly further in the list (hence higher in the tree) than `b`. -/
  def pairsWithin : List Int → List (Int × Int)
    | [] => []
    | a :: t => t.map (fun b => (b, a)) ++ pairsWithin t

  /-- All pairs of `ancPairsAux acc t`, together with the ancestor pairs inside the ancestor list
  `acc` itself. -/
  def allPairs (acc : List Int) (t : Tree) : List (Int × Int) :=
    pairsWithin acc ++ ancPairsAux acc t

  /-- Semantic value of `dfs t mn mx`, where `mn` and `mx` are the minimum and the maximum of the
  values of the ancestors of the current node. -/
  def dfsVal (mn mx : Int) : Tree → Int
    | .Null => mx - mn
    | .Node v l r =>
      max (dfsVal (min v.val mn) (max v.val mx) l) (dfsVal (min v.val mn) (max v.val mx) r)

  /-! #### Elementary facts about `listMax`, `listMin` -/

  theorem le_foldl_max (a : Int) (l : List Int) : a ≤ l.foldl max a := by
    induction l generalizing a with
    | nil => simp
    | cons x t ih =>
      simp only [List.foldl]
      exact le_trans (le_max_left a x) (ih (max a x))

  theorem foldl_max_mono {a b : Int} (h : a ≤ b) (l : List Int) :
      l.foldl max a ≤ l.foldl max b := by
    induction l generalizing a b with
    | nil => simpa using h
    | cons x t ih =>
      simp only [List.foldl]
      exact ih (max_le_max h le_rfl)

  theorem foldl_max_eq_max {a : Int} (ha : 0 ≤ a) (l : List Int) :
      l.foldl max a = max a (l.foldl max 0) := by
    induction l generalizing a with
    | nil => simp [max_eq_left ha]
    | cons x t ih =>
      simp only [List.foldl]
      rw [ih (le_trans ha (le_max_left a x)), ih (le_max_left 0 x)]
      omega

  theorem foldl_min_le (a : Int) (l : List Int) : l.foldl min a ≤ a := by
    induction l generalizing a with
    | nil => simp
    | cons x t ih =>
      simp only [List.foldl]
      exact le_trans (ih (min a x)) (min_le_left a x)

  theorem foldl_min_mono {a b : Int} (h : a ≤ b) (l : List Int) :
      l.foldl min a ≤ l.foldl min b := by
    induction l generalizing a b with
    | nil => simpa using h
    | cons x t ih =>
      simp only [List.foldl]
      exact ih (min_le_min h le_rfl)

  theorem foldl_min_eq_min {a : Int} (ha : a ≤ 100000) (l : List Int) :
      l.foldl min a = min a (l.foldl min 100000) := by
    induction l generalizing a with
    | nil => simp [min_eq_left ha]
    | cons x t ih =>
      simp only [List.foldl]
      rw [ih (a := min a x) (le_trans (min_le_left a x) ha),
        ih (a := min 100000 x) (min_le_left 100000 x)]
      omega

  theorem listMax_nonneg (l : List Int) : 0 ≤ listMax l := le_foldl_max 0 l

  theorem listMin_le_hi (l : List Int) : listMin l ≤ 100000 := foldl_min_le 100000 l

  theorem listMax_cons (x : Int) (l : List Int) : listMax (x :: l) = max x (listMax l) := by
    have h : listMax (x :: l) = max (max 0 x) (listMax l) :=
      foldl_max_eq_max (le_max_left 0 x) l
    rw [h]
    have := listMax_nonneg l
    omega

  theorem listMin_cons (x : Int) (l : List Int) : listMin (x :: l) = min x (listMin l) := by
    have h : listMin (x :: l) = min (min 100000 x) (listMin l) :=
      foldl_min_eq_min (min_le_left 100000 x) l
    rw [h]
    have := listMin_le_hi l
    omega

  theorem le_listMax (l : List Int) {x : Int} (hx : x ∈ l) : x ≤ listMax l := by
    induction l with
    | nil => simp at hx
    | cons y t ih =>
      rw [listMax_cons]
      rcases List.mem_cons.1 hx with hxy | hx
      · rw [hxy]; exact le_max_left y (listMax t)
      · exact le_trans (ih hx) (le_max_right y (listMax t))

  theorem listMin_le (l : List Int) {x : Int} (hx : x ∈ l) : listMin l ≤ x := by
    induction l with
    | nil => simp at hx
    | cons y t ih =>
      rw [listMin_cons]
      rcases List.mem_cons.1 hx with hxy | hx
      · rw [hxy]; exact min_le_left y (listMin t)
      · exact le_trans (min_le_right y (listMin t)) (ih hx)

  theorem listMin_le_listMax (l : List Int) (hne : l ≠ []) : listMin l ≤ listMax l := by
    cases l with
    | nil => exact absurd rfl hne
    | cons x t =>
      exact le_trans (listMin_le _ (x := x) (by simp)) (le_listMax _ (by simp))

  theorem listMax_mem (l : List Int) (hne : l ≠ []) (hbd : ∀ x ∈ l, 0 ≤ x) :
      listMax l ∈ l := by
    induction l with
    | nil => exact absurd rfl hne
    | cons y t ih =>
      cases t with
      | nil =>
        have hy : 0 ≤ y := hbd y (by simp)
        have hval : listMax [y] = y := by simp [listMax, max_eq_right hy]
        rw [hval]
        simp
      | cons z t' =>
        rw [listMax_cons]
        by_cases hle : listMax (z :: t') ≤ y
        · rw [max_eq_left hle]
          simp
        · rw [max_eq_right (le_of_lt (not_le.1 hle))]
          exact List.mem_cons_of_mem y (ih (by simp) (fun x hx => hbd x (by simp [hx])))

  theorem listMin_mem (l : List Int) (hne : l ≠ []) (hbd : ∀ x ∈ l, x ≤ 100000) :
      listMin l ∈ l := by
    induction l with
    | nil => exact absurd rfl hne
    | cons y t ih =>
      cases t with
      | nil =>
        have hy : y ≤ 100000 := hbd y (by simp)
        have hval : listMin [y] = y := by simp [listMin, min_eq_right hy]
        rw [hval]
        simp
      | cons z t' =>
        rw [listMin_cons]
        by_cases hle : y ≤ listMin (z :: t')
        · rw [min_eq_left hle]
          simp
        · rw [min_eq_right (le_of_lt (not_le.1 hle))]
          exact List.mem_cons_of_mem y (ih (by simp) (fun x hx => hbd x (by simp [hx])))

  /-! #### Extrema of a list vs. the ancestor pairs -/

  theorem pairsWithin_spread (acc : List Int) (hne : acc ≠ [])
      (hbd : ∀ x ∈ acc, 0 ≤ x ∧ x ≤ 100000) :
      listMax acc - listMin acc = 0 ∨
        ∃ p ∈ pairsWithin acc, listMax acc - listMin acc = absDiff p.1 p.2 := by
    induction acc with
    | nil => exact absurd rfl hne
    | cons x t ih =>
      have hbdT : ∀ y ∈ t, 0 ≤ y ∧ y ≤ 100000 := fun y hy => hbd y (by simp [hy])
      cases t with
      | nil =>
        refine Or.inl ?_
        rw [listMax_cons, listMin_cons]
        have hx := hbd x (by simp)
        simp only [listMax, listMin, List.foldl]
        omega
      | cons y t' =>
        have hne' : (y :: t') ≠ [] := by simp
        by_cases hin : listMin (y :: t') ≤ x ∧ x ≤ listMax (y :: t')
        · have hMeq : listMax (x :: y :: t') - listMin (x :: y :: t') =
              listMax (y :: t') - listMin (y :: t') := by
            rw [listMax_cons, listMin_cons]
            omega
          rcases ih hne' hbdT with h0 | ⟨p, hp, hval⟩
          · exact Or.inl (hMeq.trans h0)
          · refine Or.inr ⟨p, ?_, hMeq.trans hval⟩
            simp only [pairsWithin]
            exact List.mem_append_right _ hp
        · have hxout : x < listMin (y :: t') ∨ listMax (y :: t') < x := by
            rcases not_and_or.1 hin with h | h
            · exact Or.inl (not_le.1 h)
            · exact Or.inr (not_le.1 h)
          have hLU : listMin (y :: t') ≤ listMax (y :: t') := listMin_le_listMax _ hne'
          rcases hxout with hlt | hgt
          · refine Or.inr ⟨(listMax (y :: t'), x), ?_, ?_⟩
            · simp only [pairsWithin]
              refine List.mem_append_left _ (List.mem_map.2 ⟨listMax (y :: t'), ?_, rfl⟩)
              exact listMax_mem _ hne' (fun z hz => (hbdT z hz).1)
            · rw [listMax_cons, listMin_cons, absDiff]
              omega
          · refine Or.inr ⟨(listMin (y :: t'), x), ?_, ?_⟩
            · simp only [pairsWithin]
              refine List.mem_append_left _ (List.mem_map.2 ⟨listMin (y :: t'), ?_, rfl⟩)
              exact listMin_mem _ hne' (fun z hz => (hbdT z hz).2)
            · rw [listMax_cons, listMin_cons, absDiff]
              omega

  theorem mem_allPairs_push (v : Std.I64) (acc : List Int) (t u : Tree) :
      ∀ p ∈ allPairs (v.val :: acc) t, p ∈ allPairs acc (.Node v t u) := by
    intro p hp
    simp only [allPairs, pairsWithin, ancPairsAux, List.mem_append, List.mem_map] at hp ⊢
    rcases hp with (⟨a, ha, rfl⟩ | hp) | hp
    · exact Or.inr (Or.inl (Or.inl ⟨a, ha, rfl⟩))
    · exact Or.inl hp
    · exact Or.inr (Or.inl (Or.inr hp))

  theorem mem_allPairs_push_r (v : Std.I64) (acc : List Int) (t u : Tree) :
      ∀ p ∈ allPairs (v.val :: acc) u, p ∈ allPairs acc (.Node v t u) := by
    intro p hp
    simp only [allPairs, pairsWithin, ancPairsAux, List.mem_append, List.mem_map] at hp ⊢
    rcases hp with (⟨a, ha, rfl⟩ | hp) | hp
    · exact Or.inr (Or.inl (Or.inl ⟨a, ha, rfl⟩))
    · exact Or.inl hp
    · exact Or.inr (Or.inr hp)

  theorem mem_ancPairs_aux_left (v : Std.I64) (l r : Tree) :
      ∀ p ∈ ancPairsAux [v.val] l, p ∈ ancPairs (.Node v l r) := by
    intro p hp
    exact List.mem_append_left _ hp

  theorem mem_ancPairs_aux_right (v : Std.I64) (l r : Tree) :
      ∀ p ∈ ancPairsAux [v.val] r, p ∈ ancPairs (.Node v l r) := by
    intro p hp
    exact List.mem_append_right _ hp

  theorem mem_allPairs_root_left (v : Std.I64) (l r : Tree) :
      ∀ p ∈ allPairs [v.val] l, p ∈ ancPairs (.Node v l r) := by
    intro p hp
    simp only [allPairs] at hp
    rcases List.mem_append.1 hp with hp1 | hp2
    · simp [pairsWithin] at hp1
    · exact mem_ancPairs_aux_left v l r p hp2

  theorem mem_allPairs_root_right (v : Std.I64) (l r : Tree) :
      ∀ p ∈ allPairs [v.val] r, p ∈ ancPairs (.Node v l r) := by
    intro p hp
    simp only [allPairs] at hp
    rcases List.mem_append.1 hp with hp1 | hp2
    · simp [pairsWithin] at hp1
    · exact mem_ancPairs_aux_right v l r p hp2

  theorem mem_ancPairs_node_left (v w : Std.I64) (k1 k2 r : Tree) :
      (v.val, w.val) ∈ ancPairs (.Node v (.Node w k1 k2) r) := by
    simp only [ancPairs, ancPairsAux, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr (Or.inl (Or.inl ⟨v.val, by simp, by simp⟩)))

  theorem mem_ancPairs_node_right (v w : Std.I64) (k1 k2 l : Tree) :
      (v.val, w.val) ∈ ancPairs (.Node v l (.Node w k1 k2)) := by
    simp only [ancPairs, ancPairsAux, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl (Or.inl ⟨v.val, by simp, by simp⟩))

  theorem ancPairsAux_fst' (acc : List Int) (t : Tree) :
      ∀ p ∈ ancPairsAux acc t, p.1 ∈ acc ∨ p.1 ∈ values t := by
    induction t generalizing acc with
    | Null => intro p hp; simp [ancPairsAux] at hp
    | Node v l r ihl ihr =>
      intro p hp
      simp only [ancPairsAux, List.mem_append, List.mem_map] at hp
      rcases hp with (⟨a, ha, rfl⟩ | hp) | hp
      · exact Or.inl ha
      · rcases ihl (v.val :: acc) p hp with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr (by rw [h]; simp [values])
          · exact Or.inl h
        · exact Or.inr (by simp [values, h])
      · rcases ihr (v.val :: acc) p hp with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr (by rw [h]; simp [values])
          · exact Or.inl h
        · exact Or.inr (by simp [values, h])

  theorem ancPairsAux_fst (acc : List Int) (t : Tree) :
      ∀ p ∈ ancPairsAux acc t, p.1 ∈ acc ++ values t := by
    intro p hp
    rw [List.mem_append]
    exact ancPairsAux_fst' acc t p hp

  theorem ancPairsAux_snd (acc : List Int) (t : Tree) :
      ∀ p ∈ ancPairsAux acc t, p.2 ∈ values t := by
    induction t generalizing acc with
    | Null => intro p hp; simp [ancPairsAux] at hp
    | Node v l r ihl ihr =>
      intro p hp
      simp only [ancPairsAux, List.mem_append, List.mem_map] at hp
      rcases hp with (⟨a, ha, rfl⟩ | hp) | hp
      · simp [values]
      · have := ihl (v.val :: acc) p hp
        simp only [values, List.mem_append, List.mem_cons] at this ⊢
        tauto
      · have := ihr (v.val :: acc) p hp
        simp only [values, List.mem_append, List.mem_cons] at this ⊢
        tauto

  /-! #### The value of `dfs` -/

  theorem i64_sub_val {x y z : Std.I64} (h : x - y = ok z) : z.val = x.val - y.val := by
    have h' := IScalar.sub_equiv (ty := IScalarTy.I64) x y
    rw [h] at h'
    exact h'.right.left

  /-- The result of the body of `dfs` on a node, in terms of the two recursive calls. -/
  theorem two_call_max {f g : Result Std.I64} {res : Std.I64}
      (h : (do let a ← f
               let b ← g
               if a > b then ok a else ok b) = ok res) :
      ∃ a b, f = ok a ∧ g = ok b ∧ res.val = max a.val b.val := by
    have key : ∀ (x y : Std.I64), (if x > y then ok x else ok y) = ok res →
        res.val = max x.val y.val := by
      intro x y hxy
      by_cases hc : x > y
      · simp only [hc, ↓reduceIte] at hxy
        rw [← Result.ok_injective hxy]
        scalar_tac
      · simp only [hc, ↓reduceIte] at hxy
        rw [← Result.ok_injective hxy]
        scalar_tac
    cases hf : f using Result.cases with
    | ret a =>
      simp only [hf, Aeneas.Std.bind_ok] at h
      cases hg : g using Result.cases with
      | ret b =>
        simp only [hg, Aeneas.Std.bind_ok] at h
        exact ⟨a, b, rfl, rfl, key a b h⟩
      | vis e k => simp only [hg, Aeneas.Std.bind_vis] at h; simp at h
      | div => simp only [hg, Aeneas.Std.bind_div] at h; simp at h
    | vis e k => simp only [hf, Aeneas.Std.bind_vis] at h; simp at h
    | div => simp only [hf, Aeneas.Std.bind_div] at h; simp at h

  /-- The two recursive calls of `dfs` on a node. -/
  theorem dfs_node_val {v : Std.I64} {l r : Tree} {mn mx res : Std.I64}
      (h : dfs (.Node v l r) mn mx = ok res) :
      ∃ (a b : Std.I64),
        dfs l (if v < mn then v else mn) (if v > mx then v else mx) = ok a ∧
        dfs r (if v < mn then v else mn) (if v > mx then v else mx) = ok b ∧
        res.val = max a.val b.val := by
    rw [dfs.eq_def] at h
    dsimp only at h
    by_cases hv1 : v < mn <;> by_cases hv2 : v > mx
    · simp only [hv1, hv2, ↓reduceIte, Aeneas.Std.bind_ok] at h
      obtain ⟨a, b, ha, hb, hres⟩ := two_call_max h
      exact ⟨a, b, by simpa only [hv1, hv2, ↓reduceIte] using ha,
        by simpa only [hv1, hv2, ↓reduceIte] using hb, hres⟩
    · simp only [hv1, hv2, ↓reduceIte, Aeneas.Std.bind_ok] at h
      obtain ⟨a, b, ha, hb, hres⟩ := two_call_max h
      exact ⟨a, b, by simpa only [hv1, hv2, ↓reduceIte] using ha,
        by simpa only [hv1, hv2, ↓reduceIte] using hb, hres⟩
    · simp only [hv1, hv2, ↓reduceIte, Aeneas.Std.bind_ok] at h
      obtain ⟨a, b, ha, hb, hres⟩ := two_call_max h
      exact ⟨a, b, by simpa only [hv1, hv2, ↓reduceIte] using ha,
        by simpa only [hv1, hv2, ↓reduceIte] using hb, hres⟩
    · simp only [hv1, hv2, ↓reduceIte, Aeneas.Std.bind_ok] at h
      obtain ⟨a, b, ha, hb, hres⟩ := two_call_max h
      exact ⟨a, b, by simpa only [hv1, hv2, ↓reduceIte] using ha,
        by simpa only [hv1, hv2, ↓reduceIte] using hb, hres⟩

  theorem dfsVal_nonneg (acc : List Int) (t : Tree) (mn mx : Int) (hne : acc ≠ [])
      (hmn : mn = listMin acc) (hmx : mx = listMax acc) : 0 ≤ dfsVal mn mx t := by
    induction t generalizing acc mn mx with
    | Null =>
      have h := listMin_le_listMax acc hne
      simp only [dfsVal]
      omega
    | Node v l r ihl ihr =>
      have hne' : (v.val :: acc) ≠ [] := by simp
      have hmn' : min v.val mn = listMin (v.val :: acc) := by rw [hmn, listMin_cons]
      have hmx' : max v.val mx = listMax (v.val :: acc) := by rw [hmx, listMax_cons]
      simp only [dfsVal]
      exact le_trans (ihl (v.val :: acc) _ _ hne' hmn' hmx') (le_max_left _ _)

  theorem dfsVal_zero (acc : List Int) (t : Tree) (mn mx : Int) (hne : acc ≠ [])
      (hmn : mn = listMin acc) (hmx : mx = listMax acc) (h : dfsVal mn mx t = 0) :
      ∃ c, (∀ x ∈ acc, x = c) ∧ ∀ x ∈ values t, x = c := by
    induction t generalizing acc mn mx with
    | Null =>
      refine ⟨listMin acc, ?_, ?_⟩
      · intro x hx
        have h1 := listMin_le acc hx
        have h2 := le_listMax acc hx
        simp only [dfsVal] at h
        omega
      · intro x hx
        simp [values] at hx
    | Node v l r ihl ihr =>
      have hne' : (v.val :: acc) ≠ [] := by simp
      have hmn' : min v.val mn = listMin (v.val :: acc) := by rw [hmn, listMin_cons]
      have hmx' : max v.val mx = listMax (v.val :: acc) := by rw [hmx, listMax_cons]
      have hA : 0 ≤ dfsVal (min v.val mn) (max v.val mx) l :=
        dfsVal_nonneg _ l _ _ hne' hmn' hmx'
      have hB : 0 ≤ dfsVal (min v.val mn) (max v.val mx) r :=
        dfsVal_nonneg _ r _ _ hne' hmn' hmx'
      simp only [dfsVal] at h
      have hAl : dfsVal (min v.val mn) (max v.val mx) l = 0 := by omega
      have hAr : dfsVal (min v.val mn) (max v.val mx) r = 0 := by omega
      obtain ⟨c1, hacc1, hval1⟩ := ihl (v.val :: acc) _ _ hne' hmn' hmx' hAl
      obtain ⟨c2, hacc2, hval2⟩ := ihr (v.val :: acc) _ _ hne' hmn' hmx' hAr
      have hv1 : v.val = c1 := hacc1 v.val (by simp)
      have hv2 : v.val = c2 := hacc2 v.val (by simp)
      refine ⟨c1, ?_, ?_⟩
      · intro x hx
        exact hacc1 x (List.mem_cons_of_mem v.val hx)
      · intro x hx
        simp only [values, List.mem_append, List.mem_cons] at hx
        rcases hx with hx1 | hx2 | hx3
        · rw [hx1]; exact hv1
        · exact hval1 x hx2
        · rw [hval2 x hx3]; exact hv2.symm.trans hv1

  /-- Value of `dfs` and a witness among the ancestor pairs. -/
  theorem dfsVal_val (t : Tree) : ∀ (acc : List Int) (mn mx res : Std.I64),
      acc ≠ [] → (∀ x ∈ acc, 0 ≤ x ∧ x ≤ 100000) →
      (∀ x ∈ values t, 0 ≤ x ∧ x ≤ 100000) →
      mn.val = listMin acc → mx.val = listMax acc →
      dfs t mn mx = ok res →
      res.val = dfsVal mn.val mx.val t ∧ 0 ≤ res.val ∧
        (res.val = 0 ∨ ∃ p ∈ allPairs acc t, res.val = absDiff p.1 p.2) := by
    induction t with
    | Null =>
      intro acc mn mx res hne hbnd hbndT hmn hmx h
      rw [dfs.eq_def] at h
      dsimp only at h
      have hsub : res.val = mx.val - mn.val := i64_sub_val h
      have hv : dfsVal mn.val mx.val .Null = mx.val - mn.val := rfl
      have hle : listMin acc ≤ listMax acc := listMin_le_listMax acc hne
      refine ⟨by rw [hv, hsub], by rw [hsub]; omega, ?_⟩
      rcases pairsWithin_spread acc hne hbnd with h0 | ⟨p, hp, hval⟩
      · exact Or.inl (by rw [hsub, hmx, hmn]; exact h0)
      · exact Or.inr ⟨p, by
          simp only [allPairs, ancPairsAux, List.mem_append]
          exact Or.inl hp, by rw [hsub, hmx, hmn]; exact hval⟩
    | Node v l r ihl ihr =>
      intro acc mn mx res hne hbnd hbndT hmn hmx h
      have hv_bnd : 0 ≤ v.val ∧ v.val ≤ 100000 := hbndT v.val (by simp [values])
      have hbndT_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        apply hbndT
        simp only [values, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hx)
      have hbndT_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        apply hbndT
        simp only [values, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hx)
      have hbnd' : ∀ x ∈ v.val :: acc, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        rcases List.mem_cons.1 hx with hx1 | hx2
        · rw [hx1]; exact hv_bnd
        · exact hbnd x hx2
      have hmn' : (if v < mn then v else mn).val = listMin (v.val :: acc) := by
        rw [listMin_cons, ← hmn]
        by_cases hv : v < mn
        · have hv' : v.val < mn.val := hv
          simp only [hv, ↓reduceIte]
          omega
        · have hv' : ¬ (v.val < mn.val) := hv
          simp only [hv, ↓reduceIte]
          omega
      have hmx' : (if v > mx then v else mx).val = listMax (v.val :: acc) := by
        rw [listMax_cons, ← hmx]
        by_cases hv : v > mx
        · have hv' : v.val > mx.val := hv
          simp only [hv, ↓reduceIte]
          omega
        · have hv' : ¬ (v.val > mx.val) := hv
          simp only [hv, ↓reduceIte]
          omega
      have hmn'' : (if v < mn then v else mn).val = min v.val mn.val := by
        rw [hmn', listMin_cons, hmn]
      have hmx'' : (if v > mx then v else mx).val = max v.val mx.val := by
        rw [hmx', listMax_cons, hmx]
      obtain ⟨a, b, ha, hb, hres⟩ := dfs_node_val h
      obtain ⟨haval, ha0, hawit⟩ :=
        ihl (v.val :: acc) _ _ a (by simp) hbnd' hbndT_l hmn' hmx' ha
      obtain ⟨hbval, hb0, hbwit⟩ :=
        ihr (v.val :: acc) _ _ b (by simp) hbnd' hbndT_r hmn' hmx' hb
      have haval' : a.val = dfsVal (min v.val mn.val) (max v.val mx.val) l := by
        rw [hmn'', hmx''] at haval
        exact haval
      have hbval' : b.val = dfsVal (min v.val mn.val) (max v.val mx.val) r := by
        rw [hmn'', hmx''] at hbval
        exact hbval
      refine ⟨?_, ?_, ?_⟩
      · simp only [dfsVal]
        rw [hres, haval', hbval']
      · rw [hres]
        exact le_trans ha0 (le_max_left _ _)
      · rcases le_total b.val a.val with hle | hle
        · have hres' : res.val = a.val := by
            rw [hres]
            exact max_eq_left hle
          rcases hawit with h0 | ⟨p, hp, hval⟩
          · exact Or.inl (by rw [hres']; exact h0)
          · exact Or.inr ⟨p, mem_allPairs_push v acc l r p hp, by rw [hres']; exact hval⟩
        · have hres' : res.val = b.val := by
            rw [hres]
            exact max_eq_right hle
          rcases hbwit with h0 | ⟨p, hp, hval⟩
          · exact Or.inl (by rw [hres']; exact h0)
          · exact Or.inr ⟨p, mem_allPairs_push_r v acc l r p hp, by rw [hres']; exact hval⟩

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
  theorem spec_4 (root : Tree)
      (hsize_lo : 2 ≤ size root) (hsize_hi : size root ≤ 5000)
      (hval : ValuesIn root 0 100000) :
      ∀ res : Std.I64, max_ancestor_diff root = ok res →
        ∃ p ∈ ancPairs root, res.val = absDiff p.1 p.2 := by
    intro res h
    cases root with
    | Null => simp [size] at hsize_lo
    | Node v l r =>
      have hv_bnd : 0 ≤ v.val ∧ v.val ≤ 100000 := hval v.val (by simp [values])
      have hbndT_l : ∀ x ∈ values l, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        apply hval
        simp only [values, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hx)
      have hbndT_r : ∀ x ∈ values r, 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        apply hval
        simp only [values, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hx)
      have hsingle : ∀ x ∈ [v.val], 0 ≤ x ∧ x ≤ 100000 := by
        intro x hx
        rcases List.mem_cons.1 hx with hx1 | hx2
        · rw [hx1]; exact hv_bnd
        · simp at hx2
      have hv_min : v.val = listMin [v.val] := by
        simp only [listMin, List.foldl]
        omega
      have hv_max : v.val = listMax [v.val] := by
        simp only [listMax, List.foldl]
        omega
      rw [max_ancestor_diff.eq_def] at h
      dsimp only at h
      obtain ⟨a, b, ha, hb, hres⟩ := two_call_max h
      obtain ⟨haval, ha0, hawit⟩ :=
        dfsVal_val l [v.val] v v a (by simp) hsingle hbndT_l hv_min hv_max ha
      obtain ⟨hbval, hb0, hbwit⟩ :=
        dfsVal_val r [v.val] v v b (by simp) hsingle hbndT_r hv_min hv_max hb
      by_cases hzero : res.val = 0
      · -- the whole tree has a constant value: every ancestor pair witnesses `0`
        have hmax0 : max a.val b.val = 0 := by rw [← hres]; exact hzero
        have ha_val : a.val = 0 := by
          have h := le_max_left a.val b.val
          omega
        have hb_val : b.val = 0 := by
          have h := le_max_right a.val b.val
          omega
        obtain ⟨c1, hc1acc, hc1val⟩ :=
          dfsVal_zero [v.val] l v.val v.val (by simp) hv_min hv_max (by rw [← haval]; exact ha_val)
        obtain ⟨c2, hc2acc, hc2val⟩ :=
          dfsVal_zero [v.val] r v.val v.val (by simp) hv_min hv_max (by rw [← hbval]; exact hb_val)
        have hv1 : v.val = c1 := hc1acc v.val (by simp)
        have hv2 : v.val = c2 := hc2acc v.val (by simp)
        have hlr : ¬ (l = .Null ∧ r = .Null) := by
          rintro ⟨h1, h2⟩
          rw [h1, h2] at hsize_lo
          simp [size] at hsize_lo
        rcases l with _ | ⟨w, k1, k2⟩
        · rcases r with _ | ⟨w, k1, k2⟩
          · exact absurd ⟨rfl, rfl⟩ hlr
          · have hw : w.val = v.val := by
              have h := hc2val w.val (by simp [values])
              rw [h, hv2]
            refine ⟨(v.val, w.val), mem_ancPairs_node_right v w k1 k2 .Null, ?_⟩
            rw [hzero, hw]
            simp [absDiff]
        · have hw : w.val = v.val := by
            have h := hc1val w.val (by simp [values])
            rw [h, hv1]
          refine ⟨(v.val, w.val), mem_ancPairs_node_left v w k1 k2 r, ?_⟩
          rw [hzero, hw]
          simp [absDiff]
      · -- the maximum is positive and is attained by one of the two recursive values
        rcases le_total b.val a.val with hle | hle
        · have hres' : res.val = a.val := by
            rw [hres]
            exact max_eq_left hle
          have ha_pos : a.val ≠ 0 := by omega
          rcases hawit with h0 | ⟨p, hp, hpair⟩
          · exact absurd h0 ha_pos
          · exact ⟨p, mem_allPairs_root_left v l r p hp, by rw [hres']; exact hpair⟩
        · have hres' : res.val = b.val := by
            rw [hres]
            exact max_eq_right hle
          have hb_pos : b.val ≠ 0 := by omega
          rcases hbwit with h0 | ⟨p, hp, hpair⟩
          · exact absurd h0 hb_pos
          · exact ⟨p, mem_allPairs_root_right v l r p hp, by rw [hres']; exact hpair⟩

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
