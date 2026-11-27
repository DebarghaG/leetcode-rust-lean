import Aegis.IsPrintable.Code.Funs

/-
Proof of `AegisSpec.IsPrintable.spec_3` (strange-printer-ii).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsPrintable

  namespace AegisSpec.IsPrintable

  /-! ## Helper notions

  The extracted function `Aegis.IsPrintable.is_printable` takes a
  `Slice (Vec I64)`: a slice of rows, each row a `Vec` of `i64`.
  So `targetGrid.val : List (Vec I64)` and for a row `row`, `row.val : List I64`.
  Scalar values are read through `.val`, giving `Int` (`ℤ`). -/

  /-- The type of the extracted `targetGrid` argument: a slice of rows of `i64`. -/
  abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

  /-- The entries of row `i` as a list of integers (`[]` when `i` is out of bounds). -/
  def rowVals (g : Grid) (i : ℕ) : List ℤ :=
    (g.val[i]?).map (fun r => r.val.map (fun x => x.val)) |>.getD []

  /-- The number of columns, i.e. `len(targetGrid[0])` (and `0` for the empty grid,
  in which case the function never reads a column). -/
  def numCols (g : Grid) : ℕ :=
    (g.val.head?.map (fun r => r.val.length)).getD 0

  /-- The value at cell `(i, j)`; `0` (never a valid color) when out of bounds.  The
  specifications only evaluate it at in-bounds positions. -/
  def cellVal (g : Grid) (i j : ℕ) : ℤ :=
    (rowVals g i)[j]?.getD 0

  /-- The color `c` occurs in the grid. -/
  def Occurs (g : Grid) (c : ℤ) : Prop :=
    ∃ row ∈ g.val, c ∈ row.val.map (fun x => x.val)

  /-- The (ascending) list of rows containing an occurrence of color `c`. -/
  def occRows (g : Grid) (c : ℤ) : List ℕ :=
    (List.range g.val.length).filter (fun i => c ∈ rowVals g i)

  /-- The (ascending) list of columns containing an occurrence of color `c`. -/
  def occCols (g : Grid) (c : ℤ) : List ℕ :=
    (List.range (numCols g)).filter
      (fun j => ∃ i, i < g.val.length ∧ j < (rowVals g i).length ∧ cellVal g i j = c)

  /-- `minRow(c)`: the least row index of a cell of color `c` (the rows are filtered
  from `range m`, so the first element of `occRows` is the minimum). -/
  def minRow (g : Grid) (c : ℤ) : ℕ := (occRows g c).headD 0

  /-- `maxRow(c)`: the greatest row index of a cell of color `c`. -/
  def maxRow (g : Grid) (c : ℤ) : ℕ := (occRows g c).getLastD 0

  /-- `minCol(c)`: the least column index of a cell of color `c`. -/
  def minCol (g : Grid) (c : ℤ) : ℕ := (occCols g c).headD 0

  /-- `maxCol(c)`: the greatest column index of a cell of color `c`. -/
  def maxCol (g : Grid) (c : ℤ) : ℕ := (occCols g c).getLastD 0

  /-- Cell `(i, j)` lies in the bounding box of color `c`, i.e.
  `minRow(c) ≤ i ≤ maxRow(c)` and `minCol(c) ≤ j ≤ maxCol(c)`. -/
  def InBBox (g : Grid) (c : ℤ) (i j : ℕ) : Prop :=
    minRow g c ≤ i ∧ i ≤ maxRow g c ∧ minCol g c ≤ j ∧ j ≤ maxCol g c

  /-- The bounding box of color `c` contains at least one cell whose color is `c'`. -/
  def BoxHasColor (g : Grid) (c c' : ℤ) : Prop :=
    ∃ i j, InBBox g c i j ∧ cellVal g i j = c'

  /-- `cs` is a finite list containing exactly the distinct colors occurring in `g`,
  each of them once (i.e. `cs` is a repetition-free listing of the color set). -/
  def IsColorList (g : Grid) (cs : List ℤ) : Prop :=
    cs.Nodup ∧ ∀ c, c ∈ cs ↔ Occurs g c

  /-- `cs` is *ordered* for printability in the sense of spec S1: whenever a cell of the
  bounding box of the `p`-th color has a different color, that other color occurs later in
  the list. -/
  def OrderedColorList (g : Grid) (cs : List ℤ) : Prop :=
    ∀ (p : ℕ) (c : ℤ), cs[p]? = some c →
      ∀ i j, InBBox g c i j → cellVal g i j ≠ c →
        ∃ q, p < q ∧ cs[q]? = some (cellVal g i j)

  /-- There is a directed cycle of length `k ≥ 2` of bounding-box containments between
  distinct occurring colors: `cs = [c_1, …, c_k]` has pairwise distinct entries, all of
  which occur in `g`, and the bounding box of `c_p` contains a cell of color `c_{p+1}`
  (indices modulo `k`, so `c_{k+1} = c_1`). -/
  def HasBoxCycle (g : Grid) : Prop :=
    ∃ (k : ℕ) (cs : List ℤ),
      2 ≤ k ∧ cs.length = k ∧ cs.Nodup ∧
        (∀ c, c ∈ cs → Occurs g c) ∧
        ∀ (p : ℕ) (c c' : ℤ), p < k → cs[p]? = some c → cs[(p + 1) % k]? = some c' →
          BoxHasColor g c c'

  /-- `g'` is the same-shaped grid obtained from `g` by applying `f` to every entry. -/
  def Relabel (g g' : Grid) (f : ℤ → ℤ) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g → cellVal g' i j = f (cellVal g i j)

  /-- `g'` is the transpose of `g`: `g'` has `n` rows and `m` columns, with
  `g'[j][i] = g[i][j]`. -/
  def TransposeOf (g g' : Grid) : Prop :=
    g'.val.length = numCols g ∧ numCols g' = g.val.length ∧
      ∀ i j, i < g.val.length → j < numCols g → cellVal g' j i = cellVal g i j

  /-- `g'` is `g` rotated by 180 degrees: `g'[i][j] = g[m-1-i][n-1-j]`. -/
  def Rotate180Of (g g' : Grid) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g →
        cellVal g' i j = cellVal g (g.val.length - 1 - i) (numCols g - 1 - j)

  /-- `g'` is `g` mirrored horizontally: `g'[i][j] = g[i][n-1-j]`. -/
  def MirrorOf (g g' : Grid) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g →
        cellVal g' i j = cellVal g i (numCols g - 1 - j)

  /-! ## Auxiliary notions for the constant-grid edge case -/

  /-- `g` is a constant grid of value `c`: every row has length `ncols` and every
  in-bounds entry equals `c`. -/
  def CstGrid (g : Grid) (c : ℤ) (ncols : ℕ) : Prop :=
    (∀ i, i < g.val.length → (g.val[i]!).val.length = ncols) ∧
      (∀ i j, i < g.val.length → j < ncols → ((g.val[i]!).val[j]!).val = c)

  /-- All entries of the `k × k` Boolean matrix `adj` are `false`. -/
  def AllFalseMat (adj : alloc.vec.Vec (alloc.vec.Vec Bool)) (k : ℕ) : Prop :=
    adj.val.length = k ∧
      ∀ i, i < k → (adj.val[i]!).val.length = k ∧ ∀ j, j < k → ((adj.val[i]!).val[j]!) = false

  /-- From a partial specification with a singleton postcondition we get the value. -/
  lemma spec_eq_ok {α : Type} {x : Result α} {v : α} (h : WP.spec x (fun r => r = v)) :
      x = ok v := by
    cases x with
    | ret a =>
      have ha : a = v := by simpa [WP.spec_ok] using h
      rw [ha]
    | vis eff k => exact absurd h (by simp [WP.spec_vis])
    | div => exact absurd h (by simp [WP.spec_div])

  /-! ## Auxiliary specifications of the individual loops, for the constant grid -/

  /-- The inner (column) loop of the maximum-colour loop: if the row has `ncols` entries, all
  equal to `cv`, and the running maximum is `≤ cv`, the loop returns `cv` (the row being
  non-empty, at least one entry is read). -/
  private lemma loop0_loop0_spec (n : Std.Usize) (row : alloc.vec.Vec Std.I64) (cv : ℤ)
      (ncols : ℕ) (hn : n.val = ncols) (hrowlen : row.val.length = ncols)
      (hn1 : 1 ≤ ncols) (hval : ∀ j, j < ncols → (row.val[j]!).val = cv)
      (mc : Std.I64) (hmc : mc.val ≤ cv) :
      WP.spec (is_printable_loop0_loop0 n mc row 0#usize) (fun r => r.val = cv) := by
    unfold is_printable_loop0_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : Std.I64 × Std.Usize => n.val - p.2.val)
      (fun p : Std.I64 × Std.Usize =>
        p.2.val ≤ n.val ∧ p.1.val ≤ cv ∧ (p.2.val = 0 ∨ p.1.val = cv))
      (fun r : Std.I64 => r.val = cv) _ (mc, 0#usize)
    · rintro ⟨m, j⟩ ⟨hjle, hmle, hdisj⟩
      dsimp only at *
      unfold is_printable_loop0_loop0.body
      by_cases hjn : j < n
      · rw [ite_eq_left hjn]
        step
        have hi : i.val = cv := by
          rw [i_post, List.Inhabited_getElem_eq_getElem!]
          · exact hval j.val (by scalar_tac)
          · scalar_tac
        by_cases hlt : i > m
        · rw [ite_eq_left hlt]
          step
          refine ⟨by scalar_tac, by scalar_tac, Or.inr hi, by scalar_tac⟩
        · rw [ite_eq_right hlt]
          step
          have hm' : m.val = cv := by scalar_tac
          exact ⟨by scalar_tac, hmle, Or.inr hm', by scalar_tac⟩
      · rw [ite_eq_right hjn]
        simp only [WP.spec_ok]
        have hne : j.val ≠ 0 := by scalar_tac
        rcases hdisj with h | h
        · exact absurd h hne
        · exact h
    · exact ⟨by simp, hmc, Or.inl rfl⟩

  /-- The maximum-colour loop returns `c` when all entries are `c`. -/
  lemma maxColor_spec (g : Grid) (m n : Std.Usize) (cv : ℤ) (ncols : ℕ)
      (hm : m.val = g.val.length) (hm1 : 1 ≤ m.val) (hn : n.val = ncols)
      (hg : CstGrid g cv ncols) (hn1 : 1 ≤ ncols) (hcv1 : 1 ≤ cv) :
      WP.spec (is_printable_loop0 g m n 0#i64 0#usize) (fun r => r.val = cv) := by
    unfold is_printable_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : Std.I64 × Std.Usize => m.val - p.2.val)
      (fun p : Std.I64 × Std.Usize =>
        p.2.val ≤ m.val ∧ p.1.val ≤ cv ∧ (p.2.val = 0 ∨ p.1.val = cv))
      (fun r : Std.I64 => r.val = cv) _ (0#i64, 0#usize)
    · rintro ⟨mc, i⟩ ⟨hile, hmcle, hdisj⟩
      dsimp only at *
      unfold is_printable_loop0.body
      by_cases him : i < m
      · rw [ite_eq_left him]
        step
        have hl : i.val < g.val.length := by scalar_tac
        have hrowlen : row.val.length = ncols := by
          rw [row_post, List.Inhabited_getElem_eq_getElem!]
          · exact hg.1 i.val hl
          · exact hl
        have hrowval : ∀ j, j < ncols → (row.val[j]!).val = cv := by
          intro j hj
          rw [row_post, List.Inhabited_getElem_eq_getElem!]
          · exact hg.2 i.val j hl hj
          · exact hl
        apply WP.spec_bind (loop0_loop0_spec n row cv ncols hn hrowlen hn1 hrowval mc hmcle)
        intro max_color1 hmax1
        step
        refine ⟨by scalar_tac, by scalar_tac, Or.inr hmax1, by scalar_tac⟩
      · rw [ite_eq_right him]
        simp only [WP.spec_ok]
        have hne : i.val ≠ 0 := by scalar_tac
        rcases hdisj with h | h
        · exact absurd h hne
        · exact h
    · exact ⟨by scalar_tac, by scalar_tac, Or.inl rfl⟩

  /-- The initialisation loop fills the five arrays with their default values. -/
  lemma initArrays_spec (m n k : Std.Usize) (hk : k.val < Std.Usize.max) :
      WP.spec (is_printable_loop1 m n k (alloc.vec.Vec.new Bool) (alloc.vec.Vec.new Std.Usize)
        (alloc.vec.Vec.new Std.Usize) (alloc.vec.Vec.new Std.Usize) (alloc.vec.Vec.new Std.Usize)
        0#usize)
      (fun r => r.1.val = List.replicate k.val false ∧ r.2.1.val = List.replicate k.val m ∧
        r.2.2.1.val = List.replicate k.val n ∧ r.2.2.2.1.val = List.replicate k.val 0#usize ∧
        r.2.2.2.2.val = List.replicate k.val 0#usize) := by
    unfold is_printable_loop1
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun s : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize ×
          alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize ×
          Std.Usize => k.val - s.2.2.2.2.2.val)
      (inv := fun s : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize ×
          alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize ×
          Std.Usize =>
        s.1.val = List.replicate s.2.2.2.2.2.val false ∧
        s.2.1.val = List.replicate s.2.2.2.2.2.val m ∧
        s.2.2.1.val = List.replicate s.2.2.2.2.2.val n ∧
        s.2.2.2.1.val = List.replicate s.2.2.2.2.2.val 0#usize ∧
        s.2.2.2.2.1.val = List.replicate s.2.2.2.2.2.val 0#usize ∧
        s.2.2.2.2.2.val ≤ k.val)
    · rintro ⟨p, mr, mc, xr, xc, c⟩ hs
      dsimp only at hs
      obtain ⟨hp, hmr, hmc, hxr, hxc, hc⟩ := hs
      dsimp only [is_printable_loop1.body]
      split
      · rename_i hlt
        have hpl : p.val.length < Std.Usize.max := by
          have h1 : p.val.length = c.val := by rw [hp]; simp
          omega
        step*
        have hk1 : c.val + 1 ≤ k.val := by scalar_tac
        refine ⟨?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
        · rw [present1_post, hp, c1_post, List.replicate_succ']
        · rw [min_r1_post, hmr, c1_post, List.replicate_succ']
        · rw [min_c1_post, hmc, c1_post, List.replicate_succ']
        · rw [max_r1_post, hxr, c1_post, List.replicate_succ']
        · rw [max_c1_post, hxc, c1_post, List.replicate_succ']
      · rename_i hlt
        simp only [Aeneas.Std.WP.spec_ok]
        have hck : c.val = k.val := by
          have h1 : k.val ≤ c.val := by scalar_tac
          omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hp, hck]
        · rw [hmr, hck]
        · rw [hmc, hck]
        · rw [hxr, hck]
        · rw [hxc, hck]
    · simp [alloc.vec.Vec.new]

  /-! ### Auxiliary lemmas and invariants for the grid-scanning loop -/

  lemma scan_set_get {α : Type} [Inhabited α] (l : List α) (i : ℕ) (x : α) (h : i < l.length) :
      (l.set i x)[i]! = x := by
    simp [List.length_set, h, getElem!_pos]

  lemma scan_set_get_ne {α : Type} [Inhabited α] (l : List α) (i j : ℕ) (x : α) (h : i ≠ j) :
      (l.set i x)[j]! = l[j]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h, ← List.getElem!_eq_getElem?_getD]

  lemma scan_set_others_false (l : List Bool) (cc : ℕ) (b : Bool) (k : ℕ)
      (h : ∀ t, t < k → t ≠ cc → l[t]! = false) :
      ∀ t, t < k → t ≠ cc → (l.set cc b)[t]! = false := by
    intro t ht hne
    rw [scan_set_get_ne l cc t b (Ne.symm hne)]
    exact h t ht hne

  /-- Reading the `cc`-entry of a list after a write at index `col.val = cc`. -/
  lemma scan_cc_get {α : Type} [Inhabited α] (l : List α) (col : Std.Usize) (cc : ℕ)
      (hc : col.val = cc) (x : α) (h : cc < l.length) : (l.set col.val x)[cc]! = x := by
    rw [hc]; exact scan_set_get l cc x h

  lemma scan_cc_get_ne {α : Type} [Inhabited α] (l : List α) (col : Std.Usize) (cc t : ℕ)
      (hc : col.val = cc) (x : α) (h : t ≠ cc) : (l.set col.val x)[t]! = l[t]! := by
    rw [hc]; exact scan_set_get_ne l cc t x (Ne.symm h)

  lemma scan_getBang_eq {α : Type} [Inhabited α] (l : List α) (i : ℕ) (h : i < l.length) :
      l[i]! = l[i]'h := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
    simp

  lemma scan_replicate_getBang {α : Type} [Inhabited α] (kk : ℕ) (x : α) (cc : ℕ)
      (h : cc < kk) : (List.replicate kk x)[cc]! = x := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate_of_lt h]
    rfl

  /-- Invariant of the inner (row-scanning) loop: the five vectors carry the values obtained
  after visiting the first `i` rows and the first `j` cells of row `i`. -/
  def RowInv (m n k : Std.Usize) (cc ncols : ℕ) (i : Std.Usize)
      (p : alloc.vec.Vec Bool) (mr mc xr xc : alloc.vec.Vec Std.Usize) (j : Std.Usize) : Prop :=
    p.val.length = k.val ∧ mr.val.length = k.val ∧ mc.val.length = k.val ∧
    xr.val.length = k.val ∧ xc.val.length = k.val ∧
    (∀ t, t < k.val → t ≠ cc → p.val[t]! = false) ∧
    p.val[cc]! = decide (1 ≤ i.val + j.val) ∧
    (mr.val[cc]!).val = (if i.val + j.val = 0 then m.val else 0) ∧
    (mc.val[cc]!).val = (if i.val + j.val = 0 then ncols else 0) ∧
    (xr.val[cc]!).val = (if i.val = 0 then 0 else (if j.val = 0 then i.val - 1 else i.val)) ∧
    (xc.val[cc]!).val = (if i.val = 0 then (if j.val = 0 then 0 else j.val - 1) else ncols - 1) ∧
    j.val ≤ ncols

  /-- Postcondition of the row-scanning loop for the row of index `i`. -/
  def RowPost (k : Std.Usize) (cc ncols : ℕ) (i : Std.Usize)
      (p : alloc.vec.Vec Bool) (mr mc xr xc : alloc.vec.Vec Std.Usize) : Prop :=
    p.val.length = k.val ∧ mr.val.length = k.val ∧ mc.val.length = k.val ∧
    xr.val.length = k.val ∧ xc.val.length = k.val ∧
    (∀ t, t < k.val → t ≠ cc → p.val[t]! = false) ∧
    p.val[cc]! = true ∧
    (mr.val[cc]!).val = 0 ∧ (mc.val[cc]!).val = 0 ∧
    (xr.val[cc]!).val = i.val ∧ (xc.val[cc]!).val = ncols - 1

  /-- Invariant of the outer (grid-scanning) loop: the five vectors carry the values obtained
  after visiting the first `i` full rows. -/
  def ScanInv (m n k : Std.Usize) (cc ncols : ℕ) (i : Std.Usize)
      (p : alloc.vec.Vec Bool) (mr mc xr xc : alloc.vec.Vec Std.Usize) : Prop :=
    p.val.length = k.val ∧ mr.val.length = k.val ∧ mc.val.length = k.val ∧
    xr.val.length = k.val ∧ xc.val.length = k.val ∧
    (∀ t, t < k.val → t ≠ cc → p.val[t]! = false) ∧
    p.val[cc]! = decide (1 ≤ i.val) ∧
    (mr.val[cc]!).val = (if i.val = 0 then m.val else 0) ∧
    (mc.val[cc]!).val = (if i.val = 0 then ncols else 0) ∧
    (xr.val[cc]!).val = (if i.val = 0 then 0 else i.val - 1) ∧
    (xc.val[cc]!).val = (if i.val = 0 then 0 else ncols - 1) ∧
    i.val ≤ m.val

  /-- Specification of the row-scanning loop, for a row whose cells are all equal to `cc`. -/
  lemma loop0_spec (n : Std.Usize) (i : Std.Usize) (row : alloc.vec.Vec Std.I64)
      (m k : Std.Usize) (cc ncols : ℕ) (hnn : n.val = ncols) (hn1 : 1 ≤ ncols)
      (hk : k.val = cc + 1) (hcc1 : 1 ≤ cc) (hcc60 : cc ≤ 60) (hm1 : 1 ≤ m.val)
      (hrowlen : row.val.length = ncols)
      (hrowval : ∀ t, t < ncols → (row.val[t]!).val = (cc : ℤ))
      (p0 : alloc.vec.Vec Bool) (mr0 mc0 xr0 xc0 : alloc.vec.Vec Std.Usize) (j0 : Std.Usize)
      (hinv0 : RowInv m n k cc ncols i p0 mr0 mc0 xr0 xc0 j0) :
      WP.spec (is_printable_loop2_loop0 n i p0 mr0 mc0 xr0 xc0 row j0)
        (fun r => RowPost k cc ncols i r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
    apply loop.spec_decr_nat
      (fun s : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize ×
               alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize × Std.Usize =>
        ncols - s.2.2.2.2.2.val)
      (fun s => RowInv m n k cc ncols i s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
      (fun r => RowPost k cc ncols i r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)
      (fun s => is_printable_loop2_loop0.body n i row s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1
        s.2.2.2.2.2)
      (p0, mr0, mc0, xr0, xc0, j0)
    · intro s hinv
      obtain ⟨pa, mra, mca, xra, xca, ja⟩ := s
      simp only [RowInv] at hinv
      obtain ⟨hpl, hmrl, hmcl, hxrl, hxcl, hfalse, hpcc, hmrcc, hmccc, hxrcc, hxccc, hjle⟩ := hinv
      unfold is_printable_loop2_loop0.body
      simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
      by_cases hjn : ja < n
      · rw [if_pos hjn]
        have hjn' : ja.val < ncols := by rw [← hnn]; exact hjn
        have hjb : ja.val < row.val.length := by rw [hrowlen]; exact hjn'
        have hcck : cc < k.val := by rw [hk]; omega
        have hbp : cc < pa.val.length := by rw [hpl]; exact hcck
        have hbmr : cc < mra.val.length := by rw [hmrl]; exact hcck
        have hbmc : cc < mca.val.length := by rw [hmcl]; exact hcck
        have hbxr : cc < xra.val.length := by rw [hxrl]; exact hcck
        have hbxc : cc < xca.val.length := by rw [hxcl]; exact hcck
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec row ja hjb)
        intro i1 hi1
        have hi1v : i1.val = (cc : ℤ) := by
          have h := hrowval ja.val hjn'
          rw [scan_getBang_eq row.val ja.val hjb] at h
          rw [hi1]; exact h
        have hbnd : 0 ≤ (i1.val : ℤ) ∧ (i1.val : ℤ) ≤ (UScalar.max .Usize : ℤ) := by
          have hmax : (60 : ℤ) ≤ (UScalar.max .Usize : ℤ) := by scalar_tac
          constructor <;> omega
        apply WP.spec_bind (IScalar.hcast_inBounds_spec .Usize i1 hbnd)
        rintro col hcol
        have hcolv : col.val = cc := by
          have h1 : (col.val : ℤ) = (i1.val : ℤ) := hcol
          rw [hi1v] at h1
          omega
        have hbpc : col.val < pa.val.length := by rw [hcolv]; exact hbp
        have hbmrc : col.val < mra.val.length := by rw [hcolv]; exact hbmr
        have hbmcc : col.val < mca.val.length := by rw [hcolv]; exact hbmc
        have hbxrc : col.val < xra.val.length := by rw [hcolv]; exact hbxr
        have hbxcc : col.val < xca.val.length := by rw [hcolv]; exact hbxc
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec pa col hbpc)
        rintro ⟨b, back⟩ ⟨hb, hback⟩
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec mra col hbmrc)
        intro i2 hi2
        have hi2v : i2.val = (mra.val[cc]!).val := by
          have h1 : i2.val = (mra.val[col.val]!).val := by
            rw [hi2, scan_getBang_eq mra.val col.val hbmrc]
          rw [hcolv] at h1; exact h1
        apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize) =>
          r.1 = pa.set col true ∧ r.1.val.length = pa.val.length ∧
          r.2.val.length = mra.val.length ∧
          (r.2.val[cc]!).val =
            (if i.val < (mra.val[cc]!).val then i.val else (mra.val[cc]!).val))
        · by_cases hlt : i.val < i2.val
          · have hlt2 : i.val < (mra.val[cc]!).val := by rw [← hi2v]; exact hlt
            rw [if_pos (show i < i2 from hlt), if_pos hlt2]
            apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec mra col hbmrc)
            rintro ⟨b1, back1⟩ ⟨hb1, hback1⟩
            change WP.spec (ok (back true, back1 i)) _
            rw [WP.spec_ok]
            refine ⟨?_, ?_, ?_, ?_⟩
            · show back true = pa.set col true; rw [hback]
            · show (back true).val.length = pa.val.length
              rw [hback]; simp [List.length_set]
            · show (back1 i).val.length = mra.val.length
              rw [hback1]; simp [List.length_set]
            · show ((back1 i).val[cc]!).val = i.val
              rw [hback1, alloc.vec.Vec.set_val_eq,
                scan_cc_get mra.val col cc hcolv i hbmr]
          · have hlt2 : ¬ (i.val < (mra.val[cc]!).val) := by rw [← hi2v]; exact hlt
            rw [if_neg (show ¬ (i < i2) from hlt), if_neg hlt2]
            rw [WP.spec_ok]
            dsimp only
            refine ⟨?_, ?_, ?_, ?_⟩
            · show back true = pa.set col true; rw [hback]
            · show (back true).val.length = pa.val.length
              rw [hback]; simp [List.length_set]
            · rfl
            · rfl
        rintro ⟨p1, mr1⟩ ⟨hp1, hp1len, hmr1len, hmr1⟩
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec xra col hbxrc)
        intro i3 hi3
        have hi3v : i3.val = (xra.val[cc]!).val := by
          have h1 : i3.val = (xra.val[col.val]!).val := by
            rw [hi3, scan_getBang_eq xra.val col.val hbxrc]
          rw [hcolv] at h1; exact h1
        apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec Std.Usize) =>
          r.val.length = xra.val.length ∧
          (r.val[cc]!).val = (if (xra.val[cc]!).val < i.val then i.val else (xra.val[cc]!).val))
        · by_cases hlt : i3.val < i.val
          · have hlt2 : (xra.val[cc]!).val < i.val := by rw [← hi3v]; exact hlt
            rw [if_pos (show i > i3 from hlt), if_pos hlt2]
            apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec xra col hbxrc)
            rintro ⟨b1, back1⟩ ⟨hb1, hback1⟩
            change WP.spec (ok (back1 i)) _
            rw [WP.spec_ok]
            refine ⟨?_, ?_⟩
            · show (back1 i).val.length = xra.val.length
              rw [hback1]; simp [List.length_set]
            · show ((back1 i).val[cc]!).val = i.val
              rw [hback1, alloc.vec.Vec.set_val_eq,
                scan_cc_get xra.val col cc hcolv i hbxr]
          · have hlt2 : ¬ ((xra.val[cc]!).val < i.val) := by rw [← hi3v]; exact hlt
            rw [if_neg (show ¬ (i > i3) from hlt), if_neg hlt2]
            rw [WP.spec_ok]
            exact ⟨rfl, rfl⟩
        rintro xr1 ⟨hxr1len, hxr1⟩
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec mca col hbmcc)
        intro i4 hi4
        have hi4v : i4.val = (mca.val[cc]!).val := by
          have h1 : i4.val = (mca.val[col.val]!).val := by
            rw [hi4, scan_getBang_eq mca.val col.val hbmcc]
          rw [hcolv] at h1; exact h1
        apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec Std.Usize) =>
          r.val.length = mca.val.length ∧
          (r.val[cc]!).val = (if ja.val < (mca.val[cc]!).val then ja.val else (mca.val[cc]!).val))
        · by_cases hlt : ja.val < i4.val
          · have hlt2 : ja.val < (mca.val[cc]!).val := by rw [← hi4v]; exact hlt
            rw [if_pos (show ja < i4 from hlt), if_pos hlt2]
            apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec mca col hbmcc)
            rintro ⟨b1, back1⟩ ⟨hb1, hback1⟩
            change WP.spec (ok (back1 ja)) _
            rw [WP.spec_ok]
            refine ⟨?_, ?_⟩
            · show (back1 ja).val.length = mca.val.length
              rw [hback1]; simp [List.length_set]
            · show ((back1 ja).val[cc]!).val = ja.val
              rw [hback1, alloc.vec.Vec.set_val_eq,
                scan_cc_get mca.val col cc hcolv ja hbmc]
          · have hlt2 : ¬ (ja.val < (mca.val[cc]!).val) := by rw [← hi4v]; exact hlt
            rw [if_neg (show ¬ (ja < i4) from hlt), if_neg hlt2]
            rw [WP.spec_ok]
            exact ⟨rfl, rfl⟩
        rintro mc1 ⟨hmc1len, hmc1⟩
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec xca col hbxcc)
        intro i5 hi5
        have hi5v : i5.val = (xca.val[cc]!).val := by
          have h1 : i5.val = (xca.val[col.val]!).val := by
            rw [hi5, scan_getBang_eq xca.val col.val hbxcc]
          rw [hcolv] at h1; exact h1
        apply WP.spec_bind (Pₘ := fun (r : alloc.vec.Vec Std.Usize) =>
          r.val.length = xca.val.length ∧
          (r.val[cc]!).val = (if (xca.val[cc]!).val < ja.val then ja.val else (xca.val[cc]!).val))
        · by_cases hlt : i5.val < ja.val
          · have hlt2 : (xca.val[cc]!).val < ja.val := by rw [← hi5v]; exact hlt
            rw [if_pos (show ja > i5 from hlt), if_pos hlt2]
            apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec xca col hbxcc)
            rintro ⟨b1, back1⟩ ⟨hb1, hback1⟩
            change WP.spec (ok (back1 ja)) _
            rw [WP.spec_ok]
            refine ⟨?_, ?_⟩
            · show (back1 ja).val.length = xca.val.length
              rw [hback1]; simp [List.length_set]
            · show ((back1 ja).val[cc]!).val = ja.val
              rw [hback1, alloc.vec.Vec.set_val_eq,
                scan_cc_get xca.val col cc hcolv ja hbxc]
          · have hlt2 : ¬ ((xca.val[cc]!).val < ja.val) := by rw [← hi5v]; exact hlt
            rw [if_neg (show ¬ (ja > i5) from hlt), if_neg hlt2]
            rw [WP.spec_ok]
            exact ⟨rfl, rfl⟩
        rintro xc1 ⟨hxc1len, hxc1⟩
        have hmaxj : ja.val + 1 ≤ Usize.max := by
          have h1 : ncols ≤ Usize.max := by rw [← hnn]; scalar_tac
          omega
        apply WP.spec_bind (Usize.add_spec (x := ja) (y := 1#usize) (by simpa using hmaxj))
        intro j1 hj1
        have hj1' : j1.val = ja.val + 1 := by simpa using hj1
        rw [WP.spec_ok]
        refine ⟨?_, ?_⟩
        · simp only [RowInv]
          have hp1' : p1 = pa.set col true := hp1
          have hp1len' : p1.val.length = pa.val.length := hp1len
          have hmr1len' : mr1.val.length = mra.val.length := hmr1len
          have hmr1' : (mr1.val[cc]!).val =
              (if i.val < (mra.val[cc]!).val then i.val else (mra.val[cc]!).val) := hmr1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hp1len', hpl]
          · rw [hmr1len', hmrl]
          · rw [hmc1len, hmcl]
          · rw [hxr1len, hxrl]
          · rw [hxc1len, hxcl]
          · intro t ht hne
            rw [hp1', alloc.vec.Vec.set_val_eq, scan_cc_get_ne pa.val col cc t hcolv true hne]
            exact hfalse t ht hne
          · rw [hp1', alloc.vec.Vec.set_val_eq, scan_cc_get pa.val col cc hcolv true hbp, hj1']
            have h1 : 1 ≤ i.val + (ja.val + 1) := by omega
            simp [h1]
          · rw [hmr1', hj1']
            have hX := hmrcc
            have hz : ¬ (i.val + (ja.val + 1) = 0) := by omega
            rw [if_neg hz]
            by_cases h0 : i.val + ja.val = 0
            · rw [if_pos h0] at hX; rw [hX]; split <;> omega
            · rw [if_neg h0] at hX; rw [hX]; split <;> omega
          · rw [hmc1, hj1']
            have hX := hmccc
            have hz : ¬ (i.val + (ja.val + 1) = 0) := by omega
            rw [if_neg hz]
            by_cases h0 : i.val + ja.val = 0
            · rw [if_pos h0] at hX; rw [hX]; split <;> omega
            · rw [if_neg h0] at hX; rw [hX]; split <;> omega
          · rw [hxr1, hj1']
            have hX := hxrcc
            have hz : ¬ (ja.val + 1 = 0) := by omega
            rw [if_neg hz]
            by_cases hi0 : i.val = 0
            · rw [if_pos hi0] at hX ⊢
              rw [hX]; split <;> omega
            · rw [if_neg hi0] at hX ⊢
              by_cases hj0 : ja.val = 0
              · rw [if_pos hj0] at hX; rw [hX]; split <;> omega
              · rw [if_neg hj0] at hX; rw [hX]; split <;> omega
          · rw [hxc1, hj1']
            have hX := hxccc
            have hz : ¬ (ja.val + 1 = 0) := by omega
            rw [if_neg hz]
            rw [show ja.val + 1 - 1 = ja.val from by omega]
            by_cases hi0 : i.val = 0
            · rw [if_pos hi0] at hX ⊢
              rw [hX]
              by_cases hj0 : ja.val = 0
              · rw [if_pos hj0]; split <;> omega
              · rw [if_neg hj0]; split <;> omega
            · rw [if_neg hi0] at hX ⊢
              rw [hX]; split <;> omega
          · rw [hj1']; omega
        · rw [hj1']; omega
      · rw [if_neg hjn]
        rw [WP.spec_ok]
        simp only [RowPost]
        have hje : ja.val = ncols := by
          have h1 : n.val ≤ ja.val := not_lt.mp hjn
          omega
        refine ⟨hpl, hmrl, hmcl, hxrl, hxcl, hfalse, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpcc]
          have h1 : 1 ≤ i.val + ja.val := by omega
          simp [h1]
        · rw [hmrcc]
          have h1 : ¬ (i.val + ja.val = 0) := by omega
          rw [if_neg h1]
        · rw [hmccc]
          have h1 : ¬ (i.val + ja.val = 0) := by omega
          rw [if_neg h1]
        · rw [hxrcc]
          have hj0 : ¬ (ja.val = 0) := by omega
          rw [if_neg hj0]
          by_cases hi0 : i.val = 0
          · rw [if_pos hi0]; omega
          · rw [if_neg hi0]
        · rw [hxccc]
          have hj0 : ¬ (ja.val = 0) := by omega
          rw [if_neg hj0]
          by_cases hi0 : i.val = 0
          · rw [if_pos hi0]; omega
          · rw [if_neg hi0]
    · exact hinv0

  /-- The scanning loop records, for the colour `cc`, its presence and its bounding box. -/
  lemma scanGrid_spec (g : Grid) (m n k : Std.Usize) (cv : ℤ) (cc ncols : ℕ)
      (present : alloc.vec.Vec Bool) (minr minc maxr maxc : alloc.vec.Vec Std.Usize)
      (hm : m.val = g.val.length) (hn : n.val = ncols)
      (hg : CstGrid g cv ncols) (hcv : cv = cc) (hm1 : 1 ≤ m.val) (hn1 : 1 ≤ ncols)
      (hk : k.val = cc + 1) (hcc1 : 1 ≤ cc) (hcc60 : cc ≤ 60)
      (hp : present.val = List.replicate k.val false)
      (hmr : minr.val = List.replicate k.val m) (hmc : minc.val = List.replicate k.val n)
      (hxr : maxr.val = List.replicate k.val 0#usize) (hxc : maxc.val = List.replicate k.val 0#usize) :
      WP.spec (is_printable_loop2 g m n 0#usize present minr minc maxr maxc)
        (fun r => r.1.val.length = k.val ∧ r.2.1.val.length = k.val ∧
          r.2.2.1.val.length = k.val ∧ r.2.2.2.1.val.length = k.val ∧
          r.2.2.2.2.val.length = k.val ∧ r.1.val[cc]! = true ∧
          (∀ j, j < k.val → j ≠ cc → r.1.val[j]! = false) ∧
          (r.2.1.val[cc]!).val = 0 ∧ (r.2.2.1.val[cc]!).val = 0 ∧
          (r.2.2.2.1.val[cc]!).val = m.val - 1 ∧ (r.2.2.2.2.val[cc]!).val = ncols - 1) := by
    have hkcc : cc < k.val := by rw [hk]; omega
    apply loop.spec_decr_nat
      (fun s : Std.Usize × alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize ×
                alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize =>
        m.val - s.1.val)
      (fun s => ScanInv m n k cc ncols s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
      _
      (fun s => is_printable_loop2.body g m n s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
      (0#usize, present, minr, minc, maxr, maxc)
    · intro s hinv
      obtain ⟨ia, pa, mra, mca, xra, xca⟩ := s
      simp only [ScanInv] at hinv
      obtain ⟨hpl, hmrl, hmcl, hxrl, hxcl, hfalse, hpcc, hmrcc, hmccc, hxrcc, hxccc, hille⟩ := hinv
      unfold is_printable_loop2.body
      by_cases hin : ia < m
      · rw [if_pos hin]
        have hltm : ia.val < m.val := hin
        have hib : ia.val < g.val.length := by rw [← hm]; exact hin
        apply WP.spec_bind (Slice.index_usize_spec g ia hib)
        intro row hrow
        have hlen1 : (g.val[ia.val]'hib).val.length = ncols := by
          have h := hg.1 ia.val hib
          simpa [scan_getBang_eq g.val ia.val hib] using h
        have hrowlen : row.val.length = ncols := by
          rw [hrow]; exact hlen1
        have hrowval : ∀ t, t < ncols → (row.val[t]!).val = (cc : ℤ) := by
          intro t ht
          have ht' : t < (g.val[ia.val]'hib).val.length := by rw [hlen1]; exact ht
          have h2 : (((g.val[ia.val]'hib).val)[t]!).val = cv := by
            have h := hg.2 ia.val t hib ht
            simpa [scan_getBang_eq g.val ia.val hib,
              scan_getBang_eq (g.val[ia.val]'hib).val t ht'] using h
          rw [← hrow] at h2
          rw [h2, hcv]
        have hinvj : RowInv m n k cc ncols ia pa mra mca xra xca 0#usize := by
          simp only [RowInv]
          refine ⟨hpl, hmrl, hmcl, hxrl, hxcl, hfalse, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa using hpcc
          · simpa using hmrcc
          · simpa using hmccc
          · simpa using hxrcc
          · simpa using hxccc
          · simp
        apply WP.spec_bind (loop0_spec n ia row m k cc ncols hn hn1 hk hcc1 hcc60 hm1
          hrowlen hrowval pa mra mca xra xca 0#usize hinvj)
        rintro ⟨p1, mr1, mc1, xr1, xc1⟩
          ⟨hp1l, hmr1l, hmc1l, hxr1l, hxc1l, hf1, hp1, hmr1, hmc1, hxr1, hxc1⟩
        have hp1l' : p1.val.length = k.val := hp1l
        have hmr1l' : mr1.val.length = k.val := hmr1l
        have hmc1l' : mc1.val.length = k.val := hmc1l
        have hxr1l' : xr1.val.length = k.val := hxr1l
        have hxc1l' : xc1.val.length = k.val := hxc1l
        have hp1' : p1.val[cc]! = true := hp1
        have hmr1' : (mr1.val[cc]!).val = 0 := hmr1
        have hmc1' : (mc1.val[cc]!).val = 0 := hmc1
        have hxr1'' : (xr1.val[cc]!).val = ia.val := hxr1
        have hxc1' : (xc1.val[cc]!).val = ncols - 1 := hxc1
        have hmax : ia.val + 1#usize.val ≤ Usize.max := by
          have h1 : ia.val + 1 ≤ m.val := by omega
          have h2 : m.val ≤ Usize.max := by rw [hm]; exact Slice.length_ineq g
          show ia.val + 1 ≤ Usize.max
          omega
        apply WP.spec_bind (Usize.add_spec (x := ia) (y := 1#usize) hmax)
        intro i1 hi1
        have hi1' : i1.val = ia.val + 1 := by simpa using hi1
        change WP.spec (ok (ControlFlow.cont (i1, p1, mr1, mc1, xr1, xc1))) _
        rw [WP.spec_ok]
        dsimp only
        refine ⟨?_, ?_⟩
        · simp only [ScanInv]
          refine ⟨hp1l', hmr1l', hmc1l', hxr1l', hxc1l', hf1, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hp1']
            have h1 : 1 ≤ i1.val := by omega
            simp [h1]
          · rw [hmr1']
            have h1 : ¬ (i1.val = 0) := by omega
            rw [if_neg h1]
          · rw [hmc1']
            have h1 : ¬ (i1.val = 0) := by omega
            rw [if_neg h1]
          · rw [hxr1'']
            have h1 : ¬ (i1.val = 0) := by omega
            rw [if_neg h1]
            omega
          · rw [hxc1']
            have h1 : ¬ (i1.val = 0) := by omega
            rw [if_neg h1]
          · omega
        · omega
      · rw [if_neg hin]
        change WP.spec (ok (ControlFlow.done (pa, mra, mca, xra, xca))) _
        rw [WP.spec_ok]
        dsimp only
        have hgem : m.val ≤ ia.val := by simpa using (not_lt.mp hin)
        have hie : ia.val = m.val := by omega
        refine ⟨hpl, hmrl, hmcl, hxrl, hxcl, ?_, hfalse, ?_, ?_, ?_, ?_⟩
        · rw [hpcc]
          have h1 : 1 ≤ ia.val := by omega
          simp [h1]
        · rw [hmrcc]
          have h1 : ¬ (ia.val = 0) := by omega
          rw [if_neg h1]
        · rw [hmccc]
          have h1 : ¬ (ia.val = 0) := by omega
          rw [if_neg h1]
        · rw [hxrcc]
          have h1 : ¬ (ia.val = 0) := by omega
          rw [if_neg h1]
          omega
        · rw [hxccc]
          have h1 : ¬ (ia.val = 0) := by omega
          rw [if_neg h1]
    · simp only [ScanInv]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hp]; simp
      · rw [hmr]; simp
      · rw [hmc]; simp
      · rw [hxr]; simp
      · rw [hxc]; simp
      · intro t ht hne
        rw [hp]; simp [ht]
      · rw [hp]; simp
      · rw [hmr]; rw [scan_replicate_getBang k.val m cc hkcc]; simp
      · rw [hmc]; rw [scan_replicate_getBang k.val n cc hkcc]; simp [hn]
      · rw [hxr]; rw [scan_replicate_getBang k.val 0#usize cc hkcc]; simp
      · rw [hxc]; rw [scan_replicate_getBang k.val 0#usize cc hkcc]; simp
      · simp

  /-- The row-filling loop `is_printable_loop3_loop0` pushes `k.val` `false`s, so it turns a
  row containing `d.val` `false`s into one containing `k.val` `false`s. -/
  lemma loop3_loop0_spec (k : Std.Usize) (hk : k.val < Std.Usize.max)
      (row : alloc.vec.Vec Bool) (d : Std.Usize) (hd : d.val ≤ k.val)
      (hrow : row.val = List.replicate d.val false) :
      WP.spec (is_printable_loop3_loop0 k row d)
        (fun (v : alloc.vec.Vec Bool) => v.val = List.replicate k.val false) := by
    unfold is_printable_loop3_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : alloc.vec.Vec Bool × Std.Usize => k.val - p.2.val)
      (fun p : alloc.vec.Vec Bool × Std.Usize =>
        p.1.val = List.replicate p.2.val false ∧ p.2.val ≤ k.val)
      (fun (v : alloc.vec.Vec Bool) => v.val = List.replicate k.val false)
    · rintro ⟨row', d'⟩ ⟨hx1, hx2⟩
      dsimp only at hx1 hx2 ⊢
      unfold is_printable_loop3_loop0.body
      split
      · step as ⟨row_adj1, h1⟩
        step as ⟨d1, h2⟩
        refine ⟨?_, by scalar_tac, by scalar_tac⟩
        rw [h1, hx1, h2, List.replicate_succ']
      · simp only [WP.spec_ok]
        have hdk : d'.val = k.val := by scalar_tac
        rw [← hdk]
        exact hx1
    · exact ⟨hrow, hd⟩

  /-- The initialisation of the adjacency matrix gives the all-`false` matrix. -/
  lemma initAdj_spec (k : Std.Usize) (hk : k.val < Std.Usize.max) :
      WP.spec (is_printable_loop3 k 0#usize (alloc.vec.Vec.new (alloc.vec.Vec Bool))
        (alloc.vec.Vec.new Std.I64))
      (fun r => AllFalseMat r.1 k.val ∧ r.2.val = List.replicate k.val 0#i64) := by
    unfold is_printable_loop3
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : Std.Usize × alloc.vec.Vec (alloc.vec.Vec Bool) × alloc.vec.Vec Std.I64 =>
        k.val - p.1.val)
      (fun p : Std.Usize × alloc.vec.Vec (alloc.vec.Vec Bool) × alloc.vec.Vec Std.I64 =>
        p.2.1.val.length = p.1.val ∧
          (∀ i, i < p.1.val → (p.2.1.val[i]!).val = List.replicate k.val false) ∧
          p.2.2.val = List.replicate p.1.val 0#i64 ∧ p.1.val ≤ k.val)
      (fun r : alloc.vec.Vec (alloc.vec.Vec Bool) × alloc.vec.Vec Std.I64 =>
        AllFalseMat r.1 k.val ∧ r.2.val = List.replicate k.val 0#i64)
    · rintro ⟨c, adj, indeg⟩ ⟨hinv1, hinv2, hinv3, hinv4⟩
      dsimp only at hinv1 hinv2 hinv3 hinv4 ⊢
      unfold is_printable_loop3.body
      split
      · rename_i hclt
        have hloop :=
          loop3_loop0_spec k hk (alloc.vec.Vec.new Bool) 0#usize (by simp) (by simp)
        step with hloop as ⟨row_adj, hrow_adj⟩
        step as ⟨adj1, hadj1⟩
        step as ⟨indeg1, hindeg1⟩
        step as ⟨c1, hc1⟩
        refine ⟨?_, ?_, ?_, by scalar_tac, by scalar_tac⟩
        · rw [hadj1, List.length_append, hinv1, hc1]
          simp
        · intro i hi
          rw [hadj1]
          by_cases hic : i < adj.val.length
          · rw [List.getElem!_append_left _ _ _ hic]
            exact hinv2 i (by rw [← hinv1]; exact hic)
          · have hle : adj.val.length ≤ i := by omega
            rw [List.getElem!_append_right _ _ _ hle]
            have h0 : i - adj.val.length = 0 := by omega
            rw [h0]
            simpa using hrow_adj
        · rw [hindeg1, hinv3, hc1, List.replicate_succ']
      · rename_i hcnlt
        simp only [WP.spec_ok]
        unfold AllFalseMat
        have hck : c.val = k.val := by scalar_tac
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hinv1, hck]
        · intro i hi
          have hi2 := hinv2 i (by rw [hck]; exact hi)
          refine ⟨?_, ?_⟩
          · rw [hi2]; simp
          · intro j hj; rw [hi2]; exact List.getElem!_replicate _ hj
        · rw [hinv3, hck]
    · dsimp only
      refine ⟨by simp, by simp, by simp, by simp⟩

  /-! ### Auxiliary lemmas for the adjacency loop -/

  /-- Casting a (non-negative, small) `i64` to `usize` preserves its value. -/
  lemma hcast_I64_Usize_val (i : Std.I64) (h0 : 0 ≤ i.val) (hmax : i.val ≤ 60) :
      ((IScalar.hcast .Usize i).val : ℤ) = i.val := by
    rw [IScalar.hcast_val_eq]
    cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

  /-- Casting the `i64` value `cc` to `usize` gives the `usize` value `cc`. -/
  lemma hcast_I64_Usize_eq (i : Std.I64) (c : Std.Usize) (cc : ℕ)
      (hi : i.val = (cc : ℤ)) (hc : c.val = cc) (hmax : cc ≤ 60) :
      IScalar.hcast .Usize i = c := by
    apply UScalar.eq_of_val_eq
    have h0 : 0 ≤ i.val := by rw [hi]; positivity
    have hmax' : i.val ≤ 60 := by rw [hi]; omega
    have h := hcast_I64_Usize_val i h0 hmax'
    rw [hi] at h
    have h2 : (IScalar.hcast .Usize i).val = cc := by omega
    rw [h2, hc]

  /-- The innermost loop of the adjacency construction (`for jj in c0..=c1`) does nothing when
  every entry of the row equals the colour `cc`. -/
  lemma buildAdj_row_spec (c c1 c0 : Std.Usize) (row : alloc.vec.Vec Std.I64)
      (adj : alloc.vec.Vec (alloc.vec.Vec Bool)) (indeg : alloc.vec.Vec Std.I64)
      (cc ncols : ℕ) (hc : c.val = cc) (hcc60 : cc ≤ 60)
      (hc1 : c1.val = ncols - 1) (hn1 : 1 ≤ ncols)
      (hrowlen : row.val.length = ncols)
      (hrow : ∀ j, j < ncols → (row.val[j]!).val = (cc : ℤ))
      (hc0 : c0.val = 0) :
      WP.spec (is_printable_loop4_loop0_loop0 c adj indeg c1 row c0)
        (fun r => r.1 = adj ∧ r.2 = indeg) := by
    simp only [is_printable_loop4_loop0_loop0]
    apply loop.spec_decr_nat
      (fun (s : alloc.vec.Vec (alloc.vec.Vec Bool) × alloc.vec.Vec Std.I64 ×
        Std.Usize) => ncols - s.2.2.val)
      (fun s => s.2.2.val ≤ ncols ∧ s.1 = adj ∧ s.2.1 = indeg) _ _ _
      ?_ ⟨by rw [hc0]; simp, rfl, rfl⟩
    rintro ⟨adjw, indegw, jj⟩ ⟨hjle, hadjw, hindegw⟩
    simp only at hjle
    subst hadjw hindegw
    simp only [is_printable_loop4_loop0_loop0.body]
    split
    · rename_i hjle'
      have hjjn : jj.val < ncols := by
        have h1 : jj.val ≤ c1.val := hjle'
        omega
      have hidx : jj.val < row.val.length := by rw [hrowlen]; exact hjjn
      step
      step
      have hrow' : (row.val[jj.val]).val = (cc : ℤ) := by
        rw [← show row.val[jj.val]! = row.val[jj.val] from by simp [hidx]]
        exact hrow jj.val hjjn
      have hi : i.val = (cc : ℤ) := by rw [i_post]; exact hrow'
      have hdc : d = c := by rw [d_post]; exact hcast_I64_Usize_eq i c cc hi hc hcc60
      rw [if_neg (by simp [hdc])]
      step
      omega
    · simp [WP.spec_ok]

  /-- The middle loop of the adjacency construction (`for ii in r0..=r1`) does nothing when the
  grid is constant of colour `cc`. -/
  lemma buildAdj_grid_spec (g : Grid) (m : Std.Usize) (c : Std.Usize)
      (r0 r1 c0 c1 : Std.Usize) (adj : alloc.vec.Vec (alloc.vec.Vec Bool))
      (indeg : alloc.vec.Vec Std.I64) (cc ncols : ℕ)
      (hm : m.val = g.val.length) (hg : CstGrid g (cc : ℤ) ncols)
      (hc : c.val = cc) (hcc60 : cc ≤ 60)
      (hr0 : r0.val = 0) (hr1 : r1.val = m.val - 1)
      (hc0 : c0.val = 0) (hc1 : c1.val = ncols - 1)
      (hm1 : 1 ≤ m.val) (hn1 : 1 ≤ ncols) :
      WP.spec (is_printable_loop4_loop0 g c adj indeg r1 c0 c1 r0)
        (fun r => r.1 = adj ∧ r.2 = indeg) := by
    simp only [is_printable_loop4_loop0]
    apply loop.spec_decr_nat
      (fun (s : alloc.vec.Vec (alloc.vec.Vec Bool) × alloc.vec.Vec Std.I64 ×
        Std.Usize) => m.val - s.2.2.val)
      (fun s => s.2.2.val ≤ m.val ∧ s.1 = adj ∧ s.2.1 = indeg) _ _ _
      ?_ ⟨by rw [hr0]; simp, rfl, rfl⟩
    rintro ⟨adjw, indegw, ii⟩ ⟨hile, hadjw, hindegw⟩
    simp only at hile
    subst hadjw hindegw
    simp only [is_printable_loop4_loop0.body]
    split
    · rename_i hile'
      have hiil : ii.val < m.val := by
        have h1 : ii.val ≤ r1.val := hile'
        omega
      have hidx : ii.val < g.val.length := by rw [← hm]; exact hiil
      step
      have hge : g.val[ii.val] = g.val[ii.val]! := by simp [hidx]
      have hrowlen : row.val.length = ncols := by
        rw [row_post, hge]; exact hg.1 ii.val hidx
      have hrow : ∀ j, j < ncols → (row.val[j]!).val = (cc : ℤ) := by
        intro j hj
        rw [row_post, hge]
        exact hg.2 ii.val j hidx hj
      apply WP.spec_bind
        (buildAdj_row_spec c c1 c0 row adjw indegw cc ncols hc hcc60 hc1 hn1 hrowlen hrow hc0)
      rintro ⟨adj1, indeg1⟩ ⟨h1, h2⟩
      subst h1 h2
      step
      omega
    · simp [WP.spec_ok]

  /-- The adjacency loop does nothing when the grid is a constant colour. -/
  lemma buildAdj_spec (g : Grid) (m k : Std.Usize) (cv : ℤ) (cc ncols : ℕ)
      (present : alloc.vec.Vec Bool) (minr minc maxr maxc : alloc.vec.Vec Std.Usize)
      (adj : alloc.vec.Vec (alloc.vec.Vec Bool)) (indeg : alloc.vec.Vec Std.I64)
      (hm : m.val = g.val.length) (hg : CstGrid g cv ncols) (hcv : cv = cc)
      (hm1 : 1 ≤ m.val) (hn1 : 1 ≤ ncols) (hk : k.val = cc + 1)
      (hcc1 : 1 ≤ cc) (hcc60 : cc ≤ 60)
      (hplen : present.val.length = k.val) (hp : present.val[cc]! = true)
      (hpfalse : ∀ j, j < k.val → j ≠ cc → present.val[j]! = false)
      (hmrlen : minr.val.length = k.val) (hmr : (minr.val[cc]!).val = 0)
      (hmclen : minc.val.length = k.val) (hmc : (minc.val[cc]!).val = 0)
      (hxrlen : maxr.val.length = k.val) (hxr : (maxr.val[cc]!).val = m.val - 1)
      (hxclen : maxc.val.length = k.val) (hxc : (maxc.val[cc]!).val = ncols - 1) :
      WP.spec (is_printable_loop4 g k present minr minc maxr maxc 0#usize adj indeg)
        (fun r => r.1 = adj ∧ r.2 = indeg) := by
    simp only [is_printable_loop4]
    apply loop.spec_decr_nat
      (fun (s : Std.Usize × alloc.vec.Vec (alloc.vec.Vec Bool) ×
        alloc.vec.Vec Std.I64) => k.val - s.1.val)
      (fun s => s.1.val ≤ k.val ∧ s.2.1 = adj ∧ s.2.2 = indeg) _ _ _
      ?_ ⟨by simp, rfl, rfl⟩
    rintro ⟨cw, adjw, indegw⟩ ⟨hkle, hadjw, hindegw⟩
    simp only at hkle
    subst hadjw hindegw
    simp only [is_printable_loop4.body]
    split
    · rename_i hclt
      step
      split
      · rename_i hbtrue
        have hplenb : cw.val < present.val.length := by rw [hplen]; exact hclt
        have hb2 : present.val[cw.val]! = b := by
          rw [b_post]
          simp [hplenb]
        have hpres : present.val[cw.val]! = true := by rw [hb2]; exact hbtrue
        have hcwcc : cw.val = cc := by
          by_contra hne
          have hf := hpfalse cw.val hclt hne
          rw [hf] at hpres
          exact Bool.noConfusion hpres
        have h1 : cw.val < minr.val.length := by rw [hmrlen, hk, hcwcc]; omega
        have h2 : cw.val < minc.val.length := by rw [hmclen, hk, hcwcc]; omega
        have h3 : cw.val < maxr.val.length := by rw [hxrlen, hk, hcwcc]; omega
        have h4 : cw.val < maxc.val.length := by rw [hxclen, hk, hcwcc]; omega
        step
        step
        step
        step
        have hr0 : r0.val = 0 := by
          rw [r0_post]
          rw [← show minr.val[cw.val]! = minr.val[cw.val] from by simp [h1]]
          rw [hcwcc]
          exact hmr
        have hc0' : c0.val = 0 := by
          rw [c0_post]
          rw [← show minc.val[cw.val]! = minc.val[cw.val] from by simp [h2]]
          rw [hcwcc]
          exact hmc
        have hr1 : r1.val = m.val - 1 := by
          rw [r1_post]
          rw [← show maxr.val[cw.val]! = maxr.val[cw.val] from by simp [h3]]
          rw [hcwcc]
          exact hxr
        have hc1' : c1.val = ncols - 1 := by
          rw [c1_post]
          rw [← show maxc.val[cw.val]! = maxc.val[cw.val] from by simp [h4]]
          rw [hcwcc]
          exact hxc
        apply WP.spec_bind
          (buildAdj_grid_spec g m cw r0 r1 c0 c1 adjw indegw cc ncols hm
            (hcv ▸ hg) hcwcc hcc60 hr0 hr1 hc0' hc1' hm1 hn1)
        rintro ⟨adj1, indeg1⟩ ⟨hq1, hq2⟩
        subst hq1 hq2
        step
        scalar_tac
      · rename_i hnb
        step
        scalar_tac
    · simp [WP.spec_ok]

  /-- The counting loop returns `1` when only the colour `cc` is present. -/
  lemma countPresent_spec (k : Std.Usize) (present : alloc.vec.Vec Bool) (cc : ℕ)
      (hk : k.val = cc + 1) (hp : present.val = (List.replicate k.val false).set cc true) :
      WP.spec (is_printable_loop5 k present 0#usize 0#i64) (fun r => r.val = 1) := by
    have hval : ∀ j : ℕ, j < k.val → present.val[j]! = (if j = cc then true else false) := by
      intro j hj
      rw [hp]
      by_cases h : j = cc
      · rw [if_pos h]
        exact List.set_getElem!_eq (List.replicate k.val false) cc j true
          ⟨by rw [h, List.length_replicate]; omega, h.symm⟩
      · rw [if_neg h, List.set_getElem!_ne (List.replicate k.val false) cc j true (by omega)]
        exact List.getElem!_replicate false hj
    unfold is_printable_loop5
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : Std.Usize × Std.I64 => k.val - p.1.val)
      (fun p : Std.Usize × Std.I64 => p.1.val ≤ k.val ∧
        p.2.val = (if cc < p.1.val then (1:ℤ) else 0))
      (fun r : Std.I64 => r.val = 1)
      (fun p : Std.Usize × Std.I64 => is_printable_loop5.body k present p.1 p.2)
      (0#usize, 0#i64)
    · rintro ⟨c, total⟩ ⟨hc, htot⟩
      unfold Aegis.IsPrintable.is_printable_loop5.body
      by_cases hck : c.val < k.val
      · rw [if_pos (show c < k from hck)]
        have hlen : c.val < present.val.length := by
          rw [hp, List.length_set, List.length_replicate]; omega
        step as ⟨b, hb⟩
        have hgf : present.val[c.val]! = present.val[c.val]'hlen := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]; rfl
        have hbc : b = (if c.val = cc then true else false) := by
          rw [hb, ← hgf]; exact hval c.val hck
        by_cases hcc : c.val = cc
        · have hb1 : b = true := by rw [hbc, if_pos hcc]
          rw [if_pos hb1]
          step as ⟨total1, htotal1⟩
          step as ⟨c1, hc1⟩
          have hc' : c.val ≤ k.val := hc
          have htot' : total.val = (if cc < c.val then (1:ℤ) else 0) := htot
          refine ⟨by omega, ?_, by omega⟩
          rw [htotal1, htot', ← hcc, hc1]
          simp
        · have hb1 : ¬ (b = true) := by rw [hbc, if_neg hcc]; decide
          rw [if_neg hb1]
          simp only [bind_ok]
          step as ⟨c1, hc1⟩
          have hc' : c.val ≤ k.val := hc
          have htot' : total.val = (if cc < c.val then (1:ℤ) else 0) := htot
          refine ⟨by omega, ?_, by omega⟩
          have h1 : ¬ (cc < c.val) := by omega
          have h2 : ¬ (cc < c1.val) := by omega
          rw [htot', if_neg h1, if_neg h2]
      · rw [if_neg (show ¬ c < k from by omega)]
        simp only [WP.spec_ok]
        have hc' : c.val ≤ k.val := hc
        have htot' : total.val = (if cc < c.val then (1:ℤ) else 0) := htot
        rw [htot', if_pos (by omega)]
    · refine ⟨?_, ?_⟩
      · simp
      · simp

  /-- The queue is initialised with the single colour `cc`. -/
  lemma buildQueue_spec (k : Std.Usize) (present : alloc.vec.Vec Bool)
      (indeg : alloc.vec.Vec Std.I64) (cc : ℕ) (hk : k.val = cc + 1)
      (hp : present.val = (List.replicate k.val false).set cc true)
      (hindeg : indeg.val = List.replicate k.val 0#i64) :
      WP.spec (is_printable_loop6 k present 0#usize indeg (alloc.vec.Vec.new Std.Usize))
        (fun r => r.val.length = 1 ∧ (r.val[0]!).val = cc) := by
    have hval : ∀ j : ℕ, j < k.val → present.val[j]! = (if j = cc then true else false) := by
      intro j hj
      rw [hp]
      by_cases h : j = cc
      · rw [if_pos h]
        exact List.set_getElem!_eq (List.replicate k.val false) cc j true
          ⟨by rw [h, List.length_replicate]; omega, h.symm⟩
      · rw [if_neg h, List.set_getElem!_ne (List.replicate k.val false) cc j true (by omega)]
        exact List.getElem!_replicate false hj
    have hind : ∀ j : ℕ, j < k.val → indeg.val[j]! = 0#i64 := by
      intro j hj
      rw [hindeg]
      exact List.getElem!_replicate 0#i64 hj
    unfold is_printable_loop6
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : Std.Usize × alloc.vec.Vec Std.Usize => k.val - p.1.val)
      (fun p : Std.Usize × alloc.vec.Vec Std.Usize =>
        p.1.val ≤ k.val ∧ p.2.val.length = (if cc < p.1.val then 1 else 0) ∧
          (0 < p.2.val.length → (p.2.val[0]!).val = cc))
      (fun r : alloc.vec.Vec Std.Usize => r.val.length = 1 ∧ (r.val[0]!).val = cc)
      (fun p : Std.Usize × alloc.vec.Vec Std.Usize => is_printable_loop6.body k present indeg p.1 p.2)
      (0#usize, alloc.vec.Vec.new Std.Usize)
    · rintro ⟨c, q⟩ ⟨hc, hql, hq0⟩
      dsimp only at *
      unfold Aegis.IsPrintable.is_printable_loop6.body
      by_cases hck : c.val < k.val
      · rw [if_pos (show c < k from hck)]
        have hlen : c.val < present.val.length := by
          rw [hp, List.length_set, List.length_replicate]; omega
        step as ⟨b, hb⟩
        have hgf : present.val[c.val]! = present.val[c.val]'hlen := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]; rfl
        have hbc : b = (if c.val = cc then true else false) := by
          rw [hb, ← hgf]; exact hval c.val hck
        have hleni : c.val < indeg.val.length := by
          rw [hindeg, List.length_replicate]; omega
        have hgfi : indeg.val[c.val]! = indeg.val[c.val]'hleni := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hleni]; rfl
        by_cases hcc : c.val = cc
        · have hb1 : b = true := by rw [hbc, if_pos hcc]
          rw [if_pos hb1]
          step as ⟨i, hi⟩
          have hi0 : i = 0#i64 := by rw [hi, ← hgfi]; exact hind c.val hck
          rw [if_pos hi0]
          step as ⟨q1, hq1⟩
          step as ⟨c1, hc1⟩
          have hqold : q.val.length = 0 := by rw [hql, if_neg (by omega)]
          refine ⟨by omega, ?_, ?_, by omega⟩
          · rw [hq1, List.length_append, hqold, hc1]
            rw [if_pos (by omega : cc < c.val + 1)]
            simp
          · intro _
            have hqnil : q.val = [] := by
              cases hh : q.val with
              | nil => rfl
              | cons a l => rw [hh] at hqold; simp at hqold
            rw [hq1, hqnil]
            simp only [List.nil_append]
            rw [← hcc]
            simp
        · have hb1 : ¬ (b = true) := by rw [hbc, if_neg hcc]; decide
          rw [if_neg hb1]
          simp only [bind_ok]
          step as ⟨c1, hc1⟩
          refine ⟨by omega, ?_, ?_, by omega⟩
          · rw [hql, hc1]
            by_cases hlt : cc < c.val
            · rw [if_pos hlt, if_pos (by omega)]
            · rw [if_neg hlt, if_neg (by omega)]
          · intro hpos
            exact hq0 (by omega)
      · rw [if_neg (show ¬ c < k from by omega)]
        simp only [WP.spec_ok]
        refine ⟨?_, ?_⟩
        · rw [hql, if_pos (by omega : cc < c.val)]
        · have hpos : 0 < q.val.length := by
            rw [hql, if_pos (by omega : cc < c.val)]; omega
          exact hq0 hpos
    · refine ⟨by simp, ?_, by simp⟩
      simp

  /-- The topological-sort loop pops exactly one colour, hence returns `1`. -/
  lemma toposort_spec (k : Std.Usize) (adj : alloc.vec.Vec (alloc.vec.Vec Bool))
      (indeg : alloc.vec.Vec Std.I64) (queue : alloc.vec.Vec Std.Usize)
      (present : alloc.vec.Vec Bool) (hadj : AllFalseMat adj k.val) (hq : queue.val.length = 1)
      (hq0 : (queue.val[0]!).val < k.val) :
      WP.spec (is_printable_loop7 k adj indeg queue 0#usize 0#i64) (fun r => r.val = 1) := by
    have inner : ∀ (color : Std.Usize), color.val < k.val →
        WP.spec (is_printable_loop7_loop0 k adj indeg queue color 0#usize)
          (fun r => r.1 = indeg ∧ r.2 = queue) := by
      intro color hcolor
      simp only [is_printable_loop7_loop0]
      apply Aeneas.Std.loop.spec_decr_nat
        (fun s : alloc.vec.Vec Std.I64 × alloc.vec.Vec Std.Usize × Std.Usize => k.val - s.2.2.val)
        (fun s => s.2.2.val ≤ k.val ∧ s.1 = indeg ∧ s.2.1 = queue)
        (fun r : alloc.vec.Vec Std.I64 × alloc.vec.Vec Std.Usize => r.1 = indeg ∧ r.2 = queue) _ _
        ?_ ⟨by simp, rfl, rfl⟩
      rintro ⟨iw, qw, d⟩ ⟨hdle, hiw, hqw⟩
      simp only at hdle
      subst hiw hqw
      simp only [is_printable_loop7_loop0.body]
      split
      · rename_i hdlt
        have hd' : d.val < k.val := hdlt
        have hadjlen : color.val < adj.val.length := by rw [hadj.1]; exact hcolor
        have hvlen : ∀ (v : alloc.vec.Vec Bool), v = adj.val[color.val] → v.val.length = k.val := by
          intro v hv
          rw [hv, ← show adj.val[color.val]! = adj.val[color.val] from by simp [hadjlen]]
          exact (hadj.2 color.val hcolor).1
        have hvfalse : ∀ (v : alloc.vec.Vec Bool), v = adj.val[color.val] → v.val[d.val]! = false := by
          intro v hv
          rw [hv, ← show adj.val[color.val]! = adj.val[color.val] from by simp [hadjlen]]
          exact (hadj.2 color.val hcolor).2 d.val hd'
        step
        have hvl := hvlen v v_post
        have hvf := hvfalse v v_post
        have hdlen : d.val < v.val.length := by rw [hvl]; exact hd'
        step
        have hb : b = false := by
          rw [b_post, ← show v.val[d.val]! = v.val[d.val] from by simp [hdlen]]
          exact hvf
        rw [if_neg (by rw [hb]; simp)]
        simp only [bind_ok]
        step as ⟨d1, hd1⟩
        exact ⟨by omega, by omega⟩
      · simp [WP.spec_ok]
    simp only [is_printable_loop7]
    refine Aeneas.Std.loop.spec_decr_nat
      (fun s : alloc.vec.Vec Std.I64 × alloc.vec.Vec Std.Usize × Std.Usize × Std.I64 =>
        queue.val.length - s.2.2.1.val)
      (fun s => s.2.2.1.val ≤ queue.val.length ∧ s.1 = indeg ∧ s.2.1 = queue ∧
        s.2.2.2.val = (s.2.2.1.val : ℤ))
      (fun r : Std.I64 => r.val = 1)
      (fun s => is_printable_loop7.body k adj s.1 s.2.1 s.2.2.1 s.2.2.2)
      (indeg, queue, 0#usize, 0#i64) ?_ ?_
    · rintro ⟨iw, qw, qi, pr⟩ ⟨hle, hiw, hqw, hpr⟩
      dsimp only at *
      have hiw' : indeg = iw := hiw.symm
      have hqw' : queue = qw := hqw.symm
      subst hiw'
      subst hqw'
      simp only [is_printable_loop7.body]
      by_cases hqi : qi < alloc.vec.Vec.len queue
      · rw [if_pos hqi]
        have hqilen : (alloc.vec.Vec.len queue).val = queue.val.length :=
          Aeneas.Std.alloc.vec.Vec.len_val queue
        have hqib : qi.val < queue.val.length := by rw [← hqilen]; exact hqi
        step as ⟨color, hcolor⟩
        step as ⟨qidx1, hqidx1⟩
        step as ⟨processed1, hproc1⟩
        have hcolork : color.val < k.val := by
          have h0 : qi.val = 0 := by omega
          have e1 : (queue.val)[qi.val]'hqib = (queue.val)[qi.val]! := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hqib]
            exact Option.getD_some.symm
          have hcq : color.val = (queue.val[0]!).val := by
            rw [hcolor, e1, h0]
          rw [hcq]; exact hq0
        refine WP.spec_bind (k := fun p : alloc.vec.Vec Std.I64 × alloc.vec.Vec Std.Usize =>
          Std.Result.ok (Std.ControlFlow.cont (p.1, p.2, qidx1, processed1)))
          (inner color hcolork) ?_
        rintro ⟨indeg1, queue1⟩ ⟨h1, h2⟩
        dsimp only at h1 h2
        simp only [WP.spec_ok]
        refine ⟨?_, h1, h2, ?_, ?_⟩
        · rw [hqidx1]; omega
        · rw [hproc1, hpr, hqidx1]; push_cast; ring
        · rw [hqidx1]; omega
      · rw [if_neg hqi]
        simp only [WP.spec_ok]
        have hqilen : (alloc.vec.Vec.len queue).val = queue.val.length :=
          Aeneas.Std.alloc.vec.Vec.len_val queue
        have hqi' : ¬ (qi.val < queue.val.length) := by
          intro h
          apply hqi
          show qi.val < (alloc.vec.Vec.len queue).val
          rw [hqilen]
          exact h
        have hqk : qi.val = queue.val.length := by omega
        rw [hqk, hq] at hpr
        exact hpr
    · exact ⟨by simp, rfl, rfl, by simp⟩

  /-! ## Elementary list lemmas used by the main proof -/

  lemma getElem!_eq_getElem_of_lt {α : Type} [Inhabited α] (l : List α) (i : ℕ)
      (h : i < l.length) : l[i]! = l[i]'h := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact Option.getD_some

  lemma getElem_eq_of_lt {α : Type} [Inhabited α] (l : List α) (i : ℕ)
      (h1 h2 : i < l.length) : l[i]'h1 = l[i]'h2 :=
    (getElem!_eq_getElem_of_lt l i h1).symm.trans (getElem!_eq_getElem_of_lt l i h2)

  lemma mem_getElem!_of_lt {α : Type} [Inhabited α] (l : List α) (i : ℕ)
      (h : i < l.length) : l[i]! ∈ l := by
    rw [getElem!_eq_getElem_of_lt l i h]
    exact List.getElem_mem h

  lemma cellVal_eq_getElem (g : Grid) (i j : ℕ) (hi : i < g.val.length)
      (hj : j < (g.val[i]!).val.length) :
      cellVal g i j = ((g.val[i]!).val[j]!).val := by
    have h1 : g.val[i]? = some (g.val[i]!) := by
      rw [getElem!_eq_getElem_of_lt g.val i hi, List.getElem?_eq_getElem hi]
    have h3 : ((g.val[i]!).val)[j]? = some ((g.val[i]!).val[j]!) := by
      rw [getElem!_eq_getElem_of_lt (g.val[i]!).val j hj, List.getElem?_eq_getElem hj]
    simp only [AegisSpec.IsPrintable.cellVal, AegisSpec.IsPrintable.rowVals, h1, h3,
      Option.map_some, Option.getD_some, List.getElem?_map]

  lemma eq_replicate_set {α : Type} [Inhabited α] (l : List α) (k cc : ℕ) (x d : α)
      (hlen : l.length = k) (hcc : cc < k) (hx : l[cc]! = x)
      (hf : ∀ j, j < k → j ≠ cc → l[j]! = d) :
      l = (List.replicate k d).set cc x := by
    have hrep : (List.replicate k d).length = k := List.length_replicate
    refine List.ext_getElem! ?_ ?_
    · simp [hlen, hrep]
    · intro i
      by_cases hi : i = cc
      · rw [hi, hx]
        exact (List.set_getElem!_eq (List.replicate k d) cc cc x ⟨by omega, rfl⟩).symm
      · rw [List.set_getElem!_ne (List.replicate k d) cc i x (by omega)]
        by_cases hik : i < k
        · rw [hf i hik hi, List.getElem!_replicate d hik]
        · have h1 : l[i]! = default := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
          have h2 : (List.replicate k d)[i]! = default :=
            List.getElem!_replicate_eq_default d (by omega)
          rw [h1, h2]

  lemma lt_Usize_max {n : ℕ} (h : n ≤ 61) : n < Std.Usize.max := by
    rcases Std.Usize.bounds_eq with h' | h' <;>
      rw [h'] <;>
      simp [Std.U64.max, Std.U32.max, Std.U64.numBits, Std.U32.numBits] <;>
      omega

  lemma le_Usize_max_int {z : ℤ} (h : z ≤ 61) : z ≤ (Std.Usize.max : ℤ) := by
    have h1 : (61 : ℕ) < Std.Usize.max := lt_Usize_max (by omega)
    omega

  /-! ## Specifications

  In every statement below, the "valid grid" precondition is spelled out as the
  hypotheses `hm` (`1 ≤ m ≤ 60` where `m = len(targetGrid)`), `hn` (`1 ≤ n ≤ 60` where
  `n = len(targetGrid[0]) = numCols targetGrid`), `hrows` (every row has length `n`) and
  `hentries` (`1 ≤ targetGrid[i][j] ≤ 60` for all in-bounds cells). -/

  /-- **spec_S1 (MAIN, functional)**: the call always returns a Boolean `r`, and `r = true`
  exactly when the distinct colors occurring in the grid can be listed as
  `c_1, …, c_k` (each distinct occurring color once) so that every cell in the bounding
  box of `c_p` whose color differs from `c_p` has a color occurring later in the list. -/
  theorem spec_S1 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      ∃ r, is_printable targetGrid = ok r ∧
        (r = true ↔ ∃ cs : List ℤ, IsColorList targetGrid cs ∧ OrderedColorList targetGrid cs) := by
    sorry

  /-- **spec_S2 (no_failure)**: on a valid grid the call returns a Boolean, i.e. it does
  not fail (no panic, overflow or out-of-bounds access). -/
  theorem spec_S2 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      ∃ r : Bool, is_printable targetGrid = ok r := by
    sorry

  /-- **spec_S3 (edge)**: when the grid is a single constant color, the function returns
  `true`. -/
  theorem spec_3 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hconst : ∃ c : ℤ, ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        cellVal targetGrid i j = c) :
      ∃ r, is_printable targetGrid = ok r ∧ r = true := by
    obtain ⟨cv, hcv⟩ := hconst
    have hm1 : 1 ≤ targetGrid.val.length := hm.1
    have hn1 : 1 ≤ numCols targetGrid := hn.1
    have hpos : 0 < targetGrid.val.length := by omega
    have hhead : numCols targetGrid = (targetGrid.val[0]!).val.length := by
      have hh : targetGrid.val[0]! = targetGrid.val[0]'hpos := getElem!_eq_getElem_of_lt _ _ hpos
      simp only [AegisSpec.IsPrintable.numCols, List.head?_eq_getElem?, List.getElem?_eq_getElem hpos,
        Option.map_some, Option.getD_some, hh]
    have hrowsL : ∀ i, i < targetGrid.val.length →
        (targetGrid.val[i]!).val.length = numCols targetGrid := by
      intro i hi
      rw [getElem!_eq_getElem_of_lt _ _ hi]
      exact hrows _ (List.getElem_mem hi)
    have hcv1 : 1 ≤ cv := by
      have h := (hentries 0 0 hpos hn1).1
      rwa [hcv 0 0 hpos hn1] at h
    have hcv60 : cv ≤ 60 := by
      have h := (hentries 0 0 hpos hn1).2
      rwa [hcv 0 0 hpos hn1] at h
    have hg : CstGrid targetGrid cv (numCols targetGrid) := by
      refine ⟨hrowsL, ?_⟩
      intro i j hi hj
      have hj' : j < (targetGrid.val[i]!).val.length := by rw [hrowsL i hi]; exact hj
      rw [← cellVal_eq_getElem targetGrid i j hi hj']
      exact hcv i j hi hj
    set cc : ℕ := cv.toNat with hccdef
    have hcvcc : cv = (cc : ℤ) := by
      rw [hccdef]
      exact (Int.toNat_of_nonneg (by omega)).symm
    have hcc1 : 1 ≤ cc := by omega
    have hcc60 : cc ≤ 60 := by omega
    have key : WP.spec (is_printable targetGrid) (fun (r : Bool) => r = true) := by
      unfold Aegis.IsPrintable.is_printable
      dsimp only
      by_cases hm0 : Slice.len targetGrid = 0#usize
      · rw [if_pos hm0]; simp
      · rw [if_neg hm0]
        step
        by_cases hv0 : v.len = 0#usize
        · rw [if_pos hv0]; simp
        · rw [if_neg hv0]
          have hvlen : v.val.length = (targetGrid.val[0]!).val.length := by
            rw [v_post, getElem!_eq_getElem_of_lt targetGrid.val 0 hpos]
          have hnlen : (v.len).val = numCols targetGrid := by
            simp only [Aeneas.Std.alloc.vec.Vec.len_val, hvlen, hhead]
          refine WP.spec_bind (maxColor_spec targetGrid (Slice.len targetGrid) v.len cv
            (numCols targetGrid) ?_ ?_ hnlen hg hn1 hcv1) ?_
          · exact Slice.len_val _
          · rw [Slice.len_val]; exact hm1
          intro max_color hmax
          step as ⟨i, hi⟩
          refine WP.spec_bind (IScalar.hcast_inBounds_spec UScalarTy.Usize i ?_) ?_
          · refine ⟨by omega, ?_⟩
            simp only [UScalar.max_USize_eq]
            exact le_Usize_max_int (by omega)
          intro k hk
          have hkval : k.val = cc + 1 := by
            have h1 : (k.val : ℤ) = i.val := hk
            have h2 : i.val = max_color.val + 1 := hi
            have h3 : max_color.val = cv := hmax
            omega
          refine WP.spec_bind (initArrays_spec (Slice.len targetGrid) v.len k ?_) ?_
          · exact lt_Usize_max (by omega)
          intro r hr
          obtain ⟨present, minr, minc, maxr, maxc⟩ := r
          obtain ⟨hp, hmr, hmc, hxr, hxc⟩ := hr
          dsimp only at hp hmr hmc hxr hxc
          refine WP.spec_bind (scanGrid_spec targetGrid (Slice.len targetGrid) v.len k cv cc
            (numCols targetGrid) present minr minc maxr maxc ?_ hnlen hg hcvcc ?_ hn1 hkval hcc1 hcc60
            hp hmr hmc hxr hxc) ?_
          · exact Slice.len_val _
          · rw [Slice.len_val]; exact hm1
          intro r hr
          obtain ⟨present1, minr1, minc1, maxr1, maxc1⟩ := r
          obtain ⟨hpl1, hmrl1, hmcl1, hxrl1, hxcl1, hp1, hpf1, hmr1, hmc1, hxr1, hxc1⟩ := hr
          dsimp only at hpl1 hmrl1 hmcl1 hxrl1 hxcl1 hp1 hpf1 hmr1 hmc1 hxr1 hxc1
          refine WP.spec_bind (initAdj_spec k ?_) ?_
          · exact lt_Usize_max (by omega)
          intro r hr
          obtain ⟨adj, indeg⟩ := r
          obtain ⟨hadj, hindeg⟩ := hr
          refine WP.spec_bind (buildAdj_spec targetGrid (Slice.len targetGrid) k cv cc
            (numCols targetGrid) present1 minr1 minc1 maxr1 maxc1 adj indeg ?_ hg hcvcc ?_ hn1 hkval
            hcc1 hcc60 hpl1 hp1 hpf1 hmrl1 hmr1 hmcl1 hmc1 hxrl1 hxr1 hxcl1 hxc1) ?_
          · exact Slice.len_val _
          · rw [Slice.len_val]; exact hm1
          intro r hr
          obtain ⟨adj1, indeg1⟩ := r
          obtain ⟨hadj1, hindeg1⟩ := hr
          dsimp only at hadj1 hindeg1
          have hAF : AllFalseMat adj1 k.val := by rw [hadj1]; exact hadj
          have hIE : indeg1.val = List.replicate k.val 0#i64 := by rw [hindeg1]; exact hindeg
          have hset : present1.val = (List.replicate k.val false).set cc true :=
            eq_replicate_set present1.val k.val cc true false hpl1 (by omega) hp1 hpf1
          refine WP.spec_bind (countPresent_spec k present1 cc hkval hset) ?_
          intro total htotal
          refine WP.spec_bind (buildQueue_spec k present1 indeg1 cc hkval hset hIE) ?_
          intro queue hq
          obtain ⟨hql, hq0⟩ := hq
          have hq0' : (queue.val[0]!).val < k.val := by omega
          refine WP.spec_bind (toposort_spec k adj1 indeg1 queue present1 hAF hql hq0') ?_
          intro processed hproc
          simp only [WP.spec_ok]
          have heq : processed = total := by
            apply IScalar.eq_of_val_eq
            rw [hproc, htotal]
          rw [heq]
          simp
    exact ⟨true, spec_eq_ok key, rfl⟩

  /-- **spec_S5 (witness)**: whenever the function returns `true`, some occurring color has
  a *solid* bounding box: every cell of its bounding box has that color. -/
  theorem spec_S5 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok true →
        ∃ c : ℤ, Occurs targetGrid c ∧
          ∀ i j, InBBox targetGrid c i j → cellVal targetGrid i j = c := by
    sorry

  /-- **spec_S6 (witness)**: whenever the function returns `true`, some occurring color `c`
  has no other color inside its own cells' positions relative to the other color's bounding
  box: no cell of color `c` lies in the bounding box of a different occurring color. -/
  theorem spec_S6 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok true →
        ∃ c : ℤ, Occurs targetGrid c ∧
          ∀ d : ℤ, Occurs targetGrid d → d ≠ c →
            ∀ i j, cellVal targetGrid i j = c → ¬ InBBox targetGrid d i j := by
    sorry

  /-- **spec_S7 (relational)**: two distinct occurring colors whose bounding boxes each
  contain a cell of the other color force the answer `false`. -/
  theorem spec_S7 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (a b : ℤ) (ha : Occurs targetGrid a) (hb : Occurs targetGrid b) (hab : a ≠ b)
      (hbox_ab : BoxHasColor targetGrid a b) (hbox_ba : BoxHasColor targetGrid b a) :
      ∃ r, is_printable targetGrid = ok r ∧ r = false := by
    sorry

  /-- **spec_S8 (witness)**: whenever the function returns `false`, the colors admit a
  directed cycle of length `k ≥ 2` of bounding-box containments. -/
  theorem spec_S8 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok false → HasBoxCycle targetGrid := by
    sorry

  /-- **spec_S9 (invariance)**: the answer is invariant under an injective relabeling of the
  occurring colors by values in `{1, …, 60}`. -/
  theorem spec_S9 (targetGrid targetGrid' : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (f : ℤ → ℤ)
      (hf_range : ∀ c : ℤ, Occurs targetGrid c → 1 ≤ f c ∧ f c ≤ 60)
      (hf_inj : ∀ c d : ℤ, Occurs targetGrid c → Occurs targetGrid d → f c = f d → c = d)
      (hrelabel : Relabel targetGrid targetGrid' f) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable targetGrid' = ok r' → r = r' := by
    sorry

  /-- **spec_S10 (shape)**: the answer is invariant under transposition. -/
  theorem spec_S10 (targetGrid T : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hT : TransposeOf targetGrid T) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable T = ok r' → r = r' := by
    sorry

  /-- **spec_S11 (invariance)**: the answer is invariant under a 180 degree rotation. -/
  theorem spec_S11 (targetGrid R : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hR : Rotate180Of targetGrid R) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable R = ok r' → r = r' := by
    sorry

  /-- **spec_S12 (invariance)**: the answer is invariant under a horizontal mirror. -/
  theorem spec_S12 (targetGrid H : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hH : MirrorOf targetGrid H) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable H = ok r' → r = r' := by
    sorry

  /-- **spec_C1 (functional)**: a directed cycle (`k ≥ 2`) of bounding-box containments is
  an obstruction to printability: the function returns `false`.  This is the converse of
  `spec_S8` and generalizes `spec_S7`. -/
  theorem spec_C1 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hcycle : HasBoxCycle targetGrid) :
      ∃ r, is_printable targetGrid = ok r ∧ r = false := by
    sorry

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry

  end AegisSpec.IsPrintable
