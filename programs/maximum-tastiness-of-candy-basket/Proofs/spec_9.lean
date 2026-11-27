import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_9` (maximum-tastiness-of-candy-basket).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumTastiness (maximum_tastiness)

  namespace AegisSpec.MaximumTastiness

  /-! ## Helper notions

  The specifications talk about the integer contents of the `price` array, about
  subsets of index positions (`S ⊆ {0, …, n-1}` with `|S| = k`), about the
  "tastiness" of such a selection (the minimal pairwise distance of the selected
  prices) and about extrema of the price array.  Those notions are defined here so
  that the theorem statements below can be read literally. -/

  /-- The integer values stored in the price array, in index order. -/
  def vals (price : Slice Std.I64) : List ℤ := price.val.map (fun x => x.val)

  /-- Absolute difference of two integer prices. -/
  def absDiff (a b : ℤ) : ℤ := (a - b).natAbs

  /-- The set of pairwise distances `|l[i] - l[j]|` for pairs `i < j` of indices
  drawn from the selection `S` (intended for `S ⊆ Finset.range l.length`; indices past
  the end of `l` read as the default value `0`). -/
  def pairDistsOn (l : List ℤ) (S : Finset ℕ) : Finset ℤ :=
    ((S.product S).filter (fun p => p.1 < p.2)).image
      (fun p => absDiff (l.getD p.1 0) (l.getD p.2 0))

  /-- The *tastiness* of the index selection `S`: the minimum of the pairwise
  distances `|l[i] - l[j]|` over distinct `i, j ∈ S` (and `0` when `S` contains no
  pair of distinct indices, where the minimum is over the empty set; for the
  specifications `S` always has `k ≥ 2` elements, so the minimum is nonempty). -/
  noncomputable def tastinessOn (l : List ℤ) (S : Finset ℕ) : ℤ :=
    if h : (pairDistsOn l S).Nonempty then (pairDistsOn l S).min' h else 0

  /-- The selections of `k` index positions out of `{0, …, l.length - 1}`. -/
  def kSelections (l : List ℤ) (k : ℕ) : Finset (Finset ℕ) :=
    (Finset.range l.length).powerset.filter (fun S => S.card = k)

  /-- The maximal tastiness over all selections of `k` index positions
  (and `0` when no such selection exists). -/
  noncomputable def maxTastiness (l : List ℤ) (k : ℕ) : ℤ :=
    if h : (kSelections l k).Nonempty then
      ((kSelections l k).image (tastinessOn l)).max' (Finset.Nonempty.image h _)
    else 0

  /-- The gaps `s[j] - s[i]` between *consecutive* (adjacent) indices of the
  selection `S`, i.e. the values `s[i_{t+1}] - s[i_t]` for the increasing
  enumeration `i_1 < … < i_k` of `S`. -/
  def consecutiveGaps (s : List ℤ) (S : Finset ℕ) : Finset ℤ :=
    ((S.product S).filter
        (fun p => p.1 < p.2 ∧ ∀ m ∈ S, ¬ (p.1 < m ∧ m < p.2))).image
      (fun p => s.getD p.2 0 - s.getD p.1 0)

  /-- `min_{t=1}^{k-1} (s[i_{t+1}] - s[i_t])` for the increasing enumeration of `S`
  (`0` when `S` has at most one element). -/
  noncomputable def minConsecutiveGap (s : List ℤ) (S : Finset ℕ) : ℤ :=
    if h : (consecutiveGaps s S).Nonempty then (consecutiveGaps s S).min' h else 0

  /-- The maximum of `min_{t=1}^{k-1} (s[i_{t+1}] - s[i_t])` over all increasing
  index sequences `0 ≤ i_1 < … < i_k < s.length`. -/
  noncomputable def maxMinConsecutiveGap (s : List ℤ) (k : ℕ) : ℤ :=
    if h : (kSelections s k).Nonempty then
      ((kSelections s k).image (minConsecutiveGap s)).max' (Finset.Nonempty.image h _)
    else 0

  /-- The largest price value (and `0` for an empty array). -/
  noncomputable def maxPrice (l : List ℤ) : ℤ :=
    if h : l.toFinset.Nonempty then l.toFinset.max' h else 0

  /-- The smallest price value (and `0` for an empty array). -/
  noncomputable def minPrice (l : List ℤ) : ℤ :=
    if h : l.toFinset.Nonempty then l.toFinset.min' h else 0

  /-! ## Auxiliary lemmas used by the proofs below -/

  /-- A total-correctness specification yields the value that is actually returned. -/
  theorem spec_ok_exists {α : Type _} {m : Result α} {p : Aeneas.Std.WP.Post α}
      (h : Aeneas.Std.WP.spec m p) : ∃ v, m = ok v ∧ p v := by
    induction m using Result.cases with
    | ret r => exact ⟨r, rfl, by simpa using h⟩
    | vis i k => simp [Aeneas.Std.WP.spec_vis] at h
    | div => simp [Aeneas.Std.WP.spec_div] at h

  /-! ## Specifications -/

  /-! ### Auxiliary lemmas about sorted lists -/

  theorem sorted_getElem_le {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) {i j : ℕ}
      (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) : l[i] ≤ l[j] := by
    have h := hs.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)
    simpa using h

  theorem getLast_eq_getElem {l : List ℤ} (h : l ≠ []) (hi : l.length - 1 < l.length) :
      l.getLast h = l[l.length - 1] :=
    _root_.List.getLast_eq_getElem h

  /-- In a sorted nonempty list the last element dominates every element. -/
  theorem sorted_getElem_le_getLast {l : List ℤ} (h : l ≠ [])
      (hs : l.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < l.length) : l[i] ≤ l.getLast h := by
    have hlen : l.length - 1 < l.length := by
      have := List.length_pos_iff.mpr h
      omega
    rw [getLast_eq_getElem h hlen]
    exact sorted_getElem_le hs hi hlen (by omega)

  /-! ## Lemmas about `maxPrice` and `minPrice` -/

  theorem toFinset_nonempty_of_ne_nil {l : List ℤ} (h : l ≠ []) : l.toFinset.Nonempty := by
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil h
    exact ⟨a, by simp⟩

  theorem maxPrice_of_nonempty {l : List ℤ} (h : l.toFinset.Nonempty) :
      maxPrice l = l.toFinset.max' h := by
    rw [maxPrice, dif_pos h]

  theorem minPrice_of_nonempty {l : List ℤ} (h : l.toFinset.Nonempty) :
      minPrice l = l.toFinset.min' h := by
    rw [minPrice, dif_pos h]

  theorem le_maxPrice {l : List ℤ} {x : ℤ} (hx : x ∈ l) : x ≤ maxPrice l := by
    have h : l.toFinset.Nonempty := ⟨x, by simpa using hx⟩
    rw [maxPrice_of_nonempty h]
    exact Finset.le_max' l.toFinset x (by simpa using hx)

  theorem maxPrice_le {l : List ℤ} (h : l ≠ []) {x : ℤ} (hx : ∀ y ∈ l, y ≤ x) :
      maxPrice l ≤ x := by
    rw [maxPrice_of_nonempty (toFinset_nonempty_of_ne_nil h)]
    exact Finset.max'_le l.toFinset _ x (fun y hy => hx y (by simpa using hy))

  theorem maxPrice_mem {l : List ℤ} (h : l ≠ []) : maxPrice l ∈ l := by
    have hne : l.toFinset.Nonempty := toFinset_nonempty_of_ne_nil h
    rw [maxPrice_of_nonempty hne]
    exact by simpa using Finset.max'_mem l.toFinset hne

  theorem minPrice_le {l : List ℤ} {x : ℤ} (hx : x ∈ l) : minPrice l ≤ x := by
    have h : l.toFinset.Nonempty := ⟨x, by simpa using hx⟩
    rw [minPrice_of_nonempty h]
    exact Finset.min'_le l.toFinset x (by simpa using hx)

  theorem le_minPrice {l : List ℤ} (h : l ≠ []) {x : ℤ} (hx : ∀ y ∈ l, x ≤ y) :
      x ≤ minPrice l := by
    rw [minPrice_of_nonempty (toFinset_nonempty_of_ne_nil h)]
    exact Finset.le_min' l.toFinset _ x (fun y hy => hx y (by simpa using hy))

  theorem minPrice_mem {l : List ℤ} (h : l ≠ []) : minPrice l ∈ l := by
    have hne : l.toFinset.Nonempty := toFinset_nonempty_of_ne_nil h
    rw [minPrice_of_nonempty hne]
    exact by simpa using Finset.min'_mem l.toFinset hne

  theorem maxPrice_congr_toFinset {l m : List ℤ} (h : l.toFinset = m.toFinset) :
      maxPrice l = maxPrice m := by
    by_cases hl : l.toFinset.Nonempty
    · have hm : m.toFinset.Nonempty := h ▸ hl
      rw [maxPrice_of_nonempty hl, maxPrice_of_nonempty hm]
      refine le_antisymm ?_ ?_
      · exact Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ _ (by rw [← h]; exact hy))
      · exact Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ _ (by rw [h]; exact hy))
    · have hm : ¬ m.toFinset.Nonempty := by rw [← h]; exact hl
      rw [maxPrice, maxPrice, dif_neg hl, dif_neg hm]

  theorem minPrice_congr_toFinset {l m : List ℤ} (h : l.toFinset = m.toFinset) :
      minPrice l = minPrice m := by
    by_cases hl : l.toFinset.Nonempty
    · have hm : m.toFinset.Nonempty := h ▸ hl
      rw [minPrice_of_nonempty hl, minPrice_of_nonempty hm]
      refine le_antisymm ?_ ?_
      · exact Finset.le_min' _ _ _ (fun y hy => Finset.min'_le _ _ (by rw [h]; exact hy))
      · exact Finset.le_min' _ _ _ (fun y hy => Finset.min'_le _ _ (by rw [← h]; exact hy))
    · have hm : ¬ m.toFinset.Nonempty := by rw [← h]; exact hl
      rw [minPrice, minPrice, dif_neg hl, dif_neg hm]

  theorem maxPrice_perm {l m : List ℤ} (h : l.Perm m) : maxPrice l = maxPrice m :=
    maxPrice_congr_toFinset (List.toFinset_eq_of_perm l m h)

  theorem minPrice_perm {l m : List ℤ} (h : l.Perm m) : minPrice l = minPrice m :=
    minPrice_congr_toFinset (List.toFinset_eq_of_perm l m h)

  theorem maxPrice_eq_getLast {l : List ℤ} (h : l ≠ []) (hs : l.Pairwise (· ≤ ·)) :
      maxPrice l = l.getLast h := by
    refine le_antisymm ?_ ?_
    · refine maxPrice_le h (fun y hy => ?_)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      exact sorted_getElem_le_getLast h hs hi
    · exact le_maxPrice (List.getLast_mem h)

  theorem minPrice_eq_head {l : List ℤ} (h : l ≠ []) (hs : l.Pairwise (· ≤ ·)) :
      minPrice l = l.head h := by
    have hpos : 0 < l.length := List.length_pos_iff.mpr h
    refine le_antisymm ?_ ?_
    · exact minPrice_le (List.head_mem h)
    · refine le_minPrice h (fun y hy => ?_)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      rw [List.head_eq_getElem_zero h]
      exact sorted_getElem_le hs hpos hi (by omega)

  theorem I64_le_getLast_val {l : List Std.I64} (h : l ≠ [])
      (hs : (l.map (fun x => x.val)).Pairwise (· ≤ ·)) (i : ℕ) (hi : i < l.length) :
      l[i].val ≤ (l.getLast h).val := by
    have hmap : l.map (fun x => x.val) ≠ [] := by simpa using h
    have h := sorted_getElem_le_getLast hmap hs (i := i) (by simpa using hi)
    simpa [List.getElem_map, List.getLast_map] using h

  theorem I64_getLast_val_eq_maxPrice {l : List Std.I64} (h : l ≠ [])
      (hs : (l.map (fun x => x.val)).Pairwise (· ≤ ·)) :
      maxPrice (l.map (fun x => x.val)) = (l.getLast h).val := by
    have hmap : l.map (fun x => x.val) ≠ [] := by simpa using h
    rw [maxPrice_eq_getLast hmap hs]
    exact List.getLast_map hmap

  theorem I64_head_val_eq_minPrice {l : List Std.I64} (h : l ≠ [])
      (hs : (l.map (fun x => x.val)).Pairwise (· ≤ ·)) :
      minPrice (l.map (fun x => x.val)) = (l.head h).val := by
    have hmap : l.map (fun x => x.val) ≠ [] := by simpa using h
    rw [minPrice_eq_head hmap hs]
    exact List.head_map hmap

  /-! ### Sorting helpers -/

  /-- `SortedVals l` means that the `I64` values of `l`, read from left to right,
  form a nondecreasing sequence. -/
  abbrev SortedVals (l : List Std.I64) : Prop := l.Pairwise (fun a b => a.val ≤ b.val)

  /-- Value-sortedness, phrased on the list of underlying integers. -/
  theorem sortedVals_iff (l : List Std.I64) :
      SortedVals l ↔ (l.map (fun x => x.val)).Pairwise (· ≤ ·) :=
    (List.pairwise_map (f := fun x : Std.I64 => x.val) (R := fun a b : ℤ => a ≤ b)).symm

  /-- The Boolean test `compare a b == .gt` is the test `b < a`. -/
  theorem compare_beq_gt (a b : ℤ) :
      ((compare a b == Ordering.gt) = true) ↔ b < a := by
    rw [← Int.compare_eq_gt]; simp

  /-- One unfolding step of the insertion loop (in terms of the integer values). -/
  theorem sortInsert_cons (x y : Std.I64) (ys r : List Std.I64)
      (hr : AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x ys = ok r) :
      AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x (y :: ys)
        = ok (if y.val < x.val then y :: r else x :: y :: ys) := by
    simp only [AegisShim.sortInsert, hr, bind_ok, compare_beq_gt]
    by_cases h : y.val < x.val <;> simp [h]

  /-- Inserting an element into a sorted list returns a sorted permutation of the
  original list with that element added. -/
  theorem sortInsert_spec (x : Std.I64) (l : List Std.I64) (hl : SortedVals l) :
      ∃ r, AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x l = ok r ∧
        r.Perm (x :: l) ∧ SortedVals r := by
    induction l with
    | nil =>
      refine ⟨[x], ?_, List.Perm.refl _, ?_⟩
      · simp [AegisShim.sortInsert]
      · simp [SortedVals]
    | cons y ys ih =>
      obtain ⟨r, hr, hperm, hsorted⟩ := ih (List.pairwise_cons.1 hl).2
      have hl' := List.pairwise_cons.1 hl
      refine ⟨if y.val < x.val then y :: r else x :: y :: ys, sortInsert_cons x y ys r hr, ?_, ?_⟩
      · by_cases h : y.val < x.val
        · rw [if_pos h]
          exact (List.Perm.cons y hperm).trans (List.Perm.swap y x ys).symm
        · rw [if_neg h]
      · by_cases h : y.val < x.val
        · rw [if_pos h]
          refine List.Pairwise.cons ?_ hsorted
          intro a ha
          rcases List.mem_cons.1 (hperm.subset ha) with rfl | hys
          · exact Int.le_of_lt h
          · exact hl'.1 a hys
        · rw [if_neg h]
          refine List.Pairwise.cons ?_ hl
          intro a ha
          rcases List.mem_cons.1 ha with rfl | hys
          · exact Int.not_lt.1 h
          · exact Int.le_trans (Int.not_lt.1 h) (hl'.1 a hys)

  /-- Insertion sort computes a sorted permutation of its input. -/
  theorem sortList_spec_exists (l : List Std.I64) :
      ∃ r, AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp l = ok r ∧
        r.Perm l ∧ SortedVals r := by
    induction l with
    | nil => exact ⟨[], by simp [AegisShim.sortList], List.Perm.refl _, by simp [SortedVals]⟩
    | cons x xs ih =>
      obtain ⟨r, hr, hperm, hsorted⟩ := ih
      obtain ⟨r', hr', hperm', hsorted'⟩ := sortInsert_spec x r hsorted
      refine ⟨r', ?_, ?_, hsorted'⟩
      · simp only [AegisShim.sortList, hr, bind_ok, hr']
      · exact hperm'.trans (List.Perm.cons x hperm)

  theorem sortList_spec (l : List Std.I64) :
      AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp l ⦃ l' =>
        l'.Perm l ∧ (l'.map (fun x => x.val)).Pairwise (· ≤ ·) ⦄ := by
    obtain ⟨r, hr, hperm, hsorted⟩ := sortList_spec_exists l
    rw [hr]
    simp only [Aeneas.Std.WP.spec_ok]
    exact ⟨hperm, (sortedVals_iff r).1 hsorted⟩

  @[step]
  theorem slice_sort_spec (s : Slice Std.I64) :
      alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s ⦃ s' =>
        s'.val.Perm s.val ∧ (s'.val.map (fun x => x.val)).Pairwise (· ≤ ·) ⦄ := by
    obtain ⟨r, hr, hperm, hsorted⟩ := sortList_spec_exists s.val
    have hlen : r.length ≤ Usize.max := by
      rw [List.Perm.length_eq hperm]; exact s.property
    have hunfold : alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s
        = ok (Slice.from r hlen) := by
      simp only [alloc.slice.Slice.sort, hr, bind_ok]
      rw [dif_pos hlen]
    rw [hunfold]
    simp only [Aeneas.Std.WP.spec_ok, Slice.from_val]
    exact ⟨hperm, (sortedVals_iff r).1 hsorted⟩

  /-! ### Copy loop of `maximum_tastiness` -/

  /-! ### Termination of `can_make` (used for arbitrary `k`) -/

  @[step]
  theorem can_make_loop_term (sorted : Slice Std.I64) (k d : Std.I64) (n : Usize)
      (hn : n.val = sorted.val.length) (count : Std.I64) (last : Std.I64) (i : Usize)
      (h1 : i.val ≤ n.val) (h2 : 1 ≤ count.val) (h3 : count.val ≤ 100000)
      (h4 : 1 ≤ last.val) (h5 : last.val ≤ 1000000000)
      (hk : k.val ≤ 100000)
      (hb : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i ⦃ _ => True ⦄ := by
    unfold Aegis.MaximumTastiness.can_make_loop
    refine Aeneas.Std.loop.spec_decr_nat
      (measure := fun (s : Std.I64 × Std.I64 × Usize) => n.val - s.2.2.val)
      (inv := fun s => s.2.2.val ≤ n.val ∧ 1 ≤ s.1.val ∧ s.1.val ≤ 100000 ∧
        1 ≤ s.2.1.val ∧ s.2.1.val ≤ 1000000000)
      (post := fun (_ : Bool) => True) _ (count, last, i) ?_ ⟨h1, h2, h3, h4, h5⟩
    rintro ⟨c, l, ii⟩ hinv
    simp only [Prod.fst, Prod.snd] at hinv
    obtain ⟨ha, hb1, hc, hd, he⟩ := hinv
    unfold Aegis.MaximumTastiness.can_make_loop.body
    step*
    · have hi1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hb _ (List.getElem_mem (by scalar_tac))
      scalar_tac
    · have hi1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hb _ (List.getElem_mem (by scalar_tac))
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, hi1.1, hi1.2, by scalar_tac⟩

  theorem can_make_term (sorted : Slice Std.I64) (k d : Std.I64)
      (hk : k.val ≤ 100000) (hne : 1 ≤ sorted.val.length)
      (hb : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make sorted k d ⦃ _ => True ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    step*
    · rw [last_post]
      exact (hb _ (List.getElem_mem (by scalar_tac))).1
    · rw [last_post]
      exact (hb _ (List.getElem_mem (by scalar_tac))).2

  /-! ### Functional specification of `can_make` for `k = 2` -/

  theorem getD_mem {l : List Std.I64} {j : ℕ} (h : j < l.length) :
      l.getD j 0#i64 ∈ l := by
    rw [List.getD_eq_getElem l 0#i64 h]
    exact List.getElem_mem h

  theorem getD_val_le_of_le {l : List Std.I64} (hs : SortedVals l) {i j : ℕ}
      (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
      (l.getD i 0#i64).val ≤ (l.getD j 0#i64).val := by
    rw [List.getD_eq_getElem l 0#i64 hi, List.getD_eq_getElem l 0#i64 hj]
    exact hs.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)

  theorem can_make_loop_spec_k2 (sorted : Slice Std.I64) (k d : Std.I64) (n : Usize)
      (hn : n.val = sorted.val.length) (hk : k.val = 2) (hn2 : 2 ≤ sorted.val.length)
      (hs : SortedVals sorted.val)
      (hb : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (count : Std.I64) (last : Std.I64) (i : Usize)
      (hi : i.val ≤ n.val) (hc : count.val = 1)
      (hl : last.val = (sorted.val.getD 0 0#i64).val)
      (hinv : ∀ j, 1 ≤ j → j < i.val →
        (sorted.val.getD j 0#i64).val - (sorted.val.getD 0 0#i64).val < d.val) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i ⦃ b =>
        (b = true ↔ d.val ≤
          (sorted.val.getD (sorted.val.length - 1) 0#i64).val -
            (sorted.val.getD 0 0#i64).val) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make_loop
    refine Aeneas.Std.loop.spec_decr_nat
      (measure := fun (s : Std.I64 × Std.I64 × Usize) => n.val - s.2.2.val)
      (inv := fun s => s.2.2.val ≤ n.val ∧ s.1.val = 1 ∧
        s.2.1.val = (sorted.val.getD 0 0#i64).val ∧
        (∀ j, 1 ≤ j → j < s.2.2.val →
          (sorted.val.getD j 0#i64).val - (sorted.val.getD 0 0#i64).val < d.val))
      (post := fun b => (b = true ↔ d.val ≤
        (sorted.val.getD (sorted.val.length - 1) 0#i64).val -
          (sorted.val.getD 0 0#i64).val))
      _ (count, last, i) ?_ ⟨hi, hc, hl, hinv⟩
    rintro ⟨c, l, ii⟩ hinv0
    simp only [Prod.fst, Prod.snd] at hinv0
    obtain ⟨h1, h2, h3, h4⟩ := hinv0
    unfold Aegis.MaximumTastiness.can_make_loop.body
    step*
    · have hii : ii.val < sorted.val.length := by rw [← hn]; exact ‹ii < n›
      have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hb _ (List.getElem_mem hii)
      have hlb : 1 ≤ l.val ∧ l.val ≤ 1000000000 := by
        rw [h3]
        exact hb _ (getD_mem (by omega))
      scalar_tac
    · have hii : ii.val < sorted.val.length := by rw [← hn]; exact ‹ii < n›
      have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hb _ (List.getElem_mem hii)
      have hlb : 1 ≤ l.val ∧ l.val ≤ 1000000000 := by
        rw [h3]
        exact hb _ (getD_mem (by omega))
      scalar_tac
    · refine ⟨fun _ => ?_, fun _ => trivial⟩
      have hii : ii.val < sorted.val.length := by rw [← hn]; exact ‹ii < n›
      have hlen1 : sorted.val.length - 1 < sorted.val.length := by omega
      have hgd : (sorted.val.getD ii.val 0#i64).val = i1.val := by
        rw [List.getD_eq_getElem _ 0#i64 hii, i1_post]
      have hmono : i1.val ≤ (sorted.val.getD (sorted.val.length - 1) 0#i64).val := by
        rw [← hgd]
        exact getD_val_le_of_le hs hii hlen1 (by omega)
      have hd2 : d.val ≤ i2.val := ‹i2 ≥ d›
      omega
    · have hii' : ii.val < n.val := ‹ii < n›
      have hi3n : i3.val ≤ n.val := by rw [i3_post]; omega
      have hmeas : n.val - i3.val < n.val - ii.val := by rw [i3_post]; omega
      refine ⟨hi3n, h2, h3, ?_, hmeas⟩
      intro j hj1 hji
      have hji' : j < ii.val + 1 := by rw [← i3_post]; exact hji
      by_cases hje : j = ii.val
      · subst hje
        have hii : ii.val < sorted.val.length := by rw [← hn]; exact ‹ii < n›
        have hgd : (sorted.val.getD ii.val 0#i64).val = i1.val := by
          rw [List.getD_eq_getElem _ 0#i64 hii, i1_post]
        have key : i2.val =
            (sorted.val.getD ii.val 0#i64).val - (sorted.val.getD 0 0#i64).val := by
          rw [hgd, ← h3]
          exact i2_post
        have hd2 : ¬ (d.val ≤ i2.val) := ‹¬ i2 ≥ d›
        rw [← key]
        omega
      · have hlt : j < ii.val := by omega
        exact h4 j hj1 hlt

  theorem can_make_spec_k2 (sorted : Slice Std.I64) (k d : Std.I64)
      (hk : k.val = 2) (hn2 : 2 ≤ sorted.val.length) (hs : SortedVals sorted.val)
      (hb : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make sorted k d ⦃ b =>
        (b = true ↔ d.val ≤ (sorted.val.getD (sorted.val.length - 1) 0#i64).val -
          (sorted.val.getD 0 0#i64).val) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    have hk1 : ¬ (k ≤ 1#i64) := by
      intro h
      have h' : k.val ≤ (1#i64).val := h
      simp at h'
      omega
    rw [if_neg hk1]
    step
    refine can_make_loop_spec_k2 sorted k d (Slice.len sorted) ?_ hk hn2 hs hb
      1#i64 last 1#usize ?_ ?_ ?_ ?_
    · rw [Slice.len_val]
    · rw [Slice.len_val]
      have h1 : (1#usize).val = 1 := rfl
      rw [h1]
      have hn2' : (2:ℕ) ≤ sorted.length := hn2
      omega
    · rfl
    · rw [last_post, List.getD_eq_getElem _ 0#i64 (n := 0) (by omega)]
    · intro j hj1 hji
      have h1 : (1#usize).val = 1 := rfl
      rw [h1] at hji
      omega

  /-- Version of `can_make_spec_k2` phrased for a vector (as used by the binary search). -/
  theorem can_make_spec_k2_vec (v : alloc.vec.Vec Std.I64) (k d : Std.I64)
      (hk : k.val = 2) (hn2 : 2 ≤ v.slice.val.length) (hs : SortedVals v.slice.val)
      (hb : ∀ x ∈ v.slice.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make (alloc.vec.Vec.deref v) k d ⦃ b =>
        (b = true ↔ d.val ≤ (v.slice.val.getD (v.slice.val.length - 1) 0#i64).val -
          (v.slice.val.getD 0 0#i64).val) ⦄ := by
    refine Aeneas.Std.WP.spec_mono (can_make_spec_k2 (alloc.vec.Vec.deref v) k d hk ?_ ?_ ?_) ?_
    · simpa only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val] using hn2
    · simpa only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val] using hs
    · intro x hx
      exact hb x (by simpa only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val] using hx)
    · intro b hb'
      simpa only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val] using hb'

  /-! ### Binary search loop of `maximum_tastiness` -/

  theorem tdiv_two_le {x : ℤ} (h : 0 ≤ x) : x.tdiv 2 ≤ x := Int.tdiv_le_self 2 h

  theorem tdiv_two_nonneg {x : ℤ} (h : 0 ≤ x) : 0 ≤ x.tdiv 2 :=
    Int.tdiv_nonneg h (by norm_num)

  theorem tdiv_two_lt {x : ℤ} (h : 2 ≤ x) : x.tdiv 2 < x := by
    have hkey : 2 * (x.tdiv 2) ≤ x := by
      have h1 := Int.mul_tdiv_add_tmod x 2
      have h2 : 0 ≤ x.tmod 2 := Int.tmod_nonneg 2 (by omega)
      omega
    by_contra hc
    push_neg at hc
    omega

  theorem one_le_tdiv_two {x : ℤ} (h : 2 ≤ x) : 1 ≤ x.tdiv 2 := by
    have h1 := Int.tmod_add_mul_tdiv x 2
    have h2 : x.tmod 2 < 2 := Int.tmod_lt_of_pos x (by norm_num)
    by_contra hc
    push_neg at hc
    omega

  theorem loop1_spec (k : Std.I64) (sorted : alloc.vec.Vec Std.I64) (lo hi : Std.I64) (M : ℤ)
      (hne : 1 ≤ sorted.val.length)
      (hb : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hcan : ∀ d : Std.I64,
        Aegis.MaximumTastiness.can_make (alloc.vec.Vec.deref sorted) k d ⦃ b =>
          (k.val = 2 → (b = true ↔ d.val ≤ M)) ⦄)
      (hk : k.val ≤ 100000)
      (hlo : 0 ≤ lo.val) (hlohi : lo.val < hi.val) (hhi : hi.val ≤ 1000000002)
      (hloM : k.val = 2 → lo.val ≤ M) (hMhi : k.val = 2 → M < hi.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi ⦃ r =>
        k.val = 2 → (r : Std.I64).val = M ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
    refine Aeneas.Std.loop.spec_decr_nat
      (measure := fun (s : Std.I64 × Std.I64) => (s.2.val - s.1.val).toNat)
      (inv := fun s => 0 ≤ s.1.val ∧ s.1.val < s.2.val ∧ s.2.val ≤ 1000000002 ∧
        (k.val = 2 → (s.1.val ≤ M ∧ M < s.2.val)))
      (post := fun (r : Std.I64) => k.val = 2 → r.val = M) _ (lo, hi) ?_
      ⟨hlo, hlohi, hhi, fun hk2 => ⟨hloM hk2, hMhi hk2⟩⟩
    rintro ⟨lo1, hi1⟩ hinv
    simp only [Prod.fst, Prod.snd] at hinv
    obtain ⟨h1, h2, h3, h4⟩ := hinv
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
    step*
    · -- `lo1 + i2` does not overflow
      have hx : (0:ℤ) ≤ i1.val := by rw [i1_post]; omega
      have hle : i2.val ≤ i1.val := by rw [i2_post]; exact tdiv_two_le hx
      have hmax : (1000000002 : ℤ) ≤ I64.max := by scalar_tac
      have e1 : i1.val = hi1.val - lo1.val := i1_post
      omega
    · -- branch `b = true`: new state `(mid, hi1)`
      have hge : lo1.val + 1 < hi1.val := by
        have := i_post
        scalar_tac
      have hmid : mid.val = lo1.val + (hi1.val - lo1.val).tdiv 2 := by
        rw [mid_post, i2_post, i1_post]
      have hpos : (0:ℤ) ≤ hi1.val - lo1.val := by omega
      have hlt : (hi1.val - lo1.val).tdiv 2 < hi1.val - lo1.val := tdiv_two_lt (by omega)
      refine ⟨?_, ?_, h3, ?_, ?_⟩
      · have ht : (0:ℤ) ≤ (hi1.val - lo1.val).tdiv 2 := tdiv_two_nonneg hpos
        omega
      · have ht : (hi1.val - lo1.val).tdiv 2 < hi1.val - lo1.val := hlt
        omega
      · intro hk2
        exact ⟨(b_post hk2).1 ‹b = true›, (h4 hk2).2⟩
      · have hkey : (0:ℤ) < hi1.val - lo1.val := by omega
        have ht1 : (1:ℤ) ≤ (hi1.val - lo1.val).tdiv 2 := one_le_tdiv_two (by omega)
        exact (Int.toNat_lt_toNat hkey).mpr (by omega)
    · -- branch `b = false`: new state `(lo1, mid)`
      have hge : lo1.val + 1 < hi1.val := by
        have := i_post
        scalar_tac
      have hmid : mid.val = lo1.val + (hi1.val - lo1.val).tdiv 2 := by
        rw [mid_post, i2_post, i1_post]
      have hpos : (0:ℤ) ≤ hi1.val - lo1.val := by omega
      have hlt : (hi1.val - lo1.val).tdiv 2 < hi1.val - lo1.val := tdiv_two_lt (by omega)
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · have ht : (1:ℤ) ≤ (hi1.val - lo1.val).tdiv 2 := one_le_tdiv_two (by omega)
        omega
      · have ht : (hi1.val - lo1.val).tdiv 2 < hi1.val - lo1.val := hlt
        omega
      · intro hk2
        refine ⟨(h4 hk2).1, ?_⟩
        by_contra hcon
        have hcm : mid.val ≤ M := by omega
        exact ‹¬b = true› ((b_post hk2).2 hcm)
      · have hkey : (0:ℤ) < hi1.val - lo1.val := by omega
        have ht0 : (0:ℤ) ≤ (hi1.val - lo1.val).tdiv 2 := tdiv_two_nonneg (by omega)
        exact (Int.toNat_lt_toNat hkey).mpr (by omega)

  /-- `maximum_tastiness_loop0` copies the whole slice into a fresh vector. -/
  @[step]
  theorem loop0_spec (price : Slice Std.I64) (n : Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Usize)
      (hn : n.val = price.val.length) (hin : sorted.val = price.val.take i.val)
      (hib : i.val ≤ n.val) (hsz : price.val.length < Usize.max) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n sorted i ⦃ v =>
        (v : alloc.vec.Vec Std.I64).val = price.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
    refine Aeneas.Std.loop.spec_decr_nat
      (measure := fun (s : alloc.vec.Vec Std.I64 × Usize) => n.val - s.2.val)
      (inv := fun s => s.1.val = price.val.take s.2.val ∧ s.2.val ≤ n.val)
      (post := fun (v : alloc.vec.Vec Std.I64) => v.val = price.val) _ (sorted, i) ?_
      ⟨hin, hib⟩
    rintro ⟨xs, ii⟩ hinv
    simp only [Prod.fst, Prod.snd] at hinv
    obtain ⟨hinv, hibv⟩ := hinv
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
    step*
    · have hlen : ii.val < price.val.length := by scalar_tac
      have htake : price.val.take ii.val ++ [price.val[ii.val]] =
          price.val.take (ii.val + 1) :=
        List.take_append_getElem hlen
      have hA : i2.val ≤ n.val := by scalar_tac
      have hB : n.val - i2.val < n.val - ii.val := by scalar_tac
      refine ⟨?_, hA, hB⟩
      rw [sorted1_post, hinv, i2_post, i1_post]
      simp only [htake]
    · rw [hinv]
      exact List.take_of_length_le (by scalar_tac)

  /-- For a sorted permutation `s` of the prices, the spread of `s` (its last value minus
  its first value) is the difference of the maximal and of the minimal price. -/
  theorem spread_of_sorted_perm (price s : Slice Std.I64)
      (hperm : s.val.Perm price.val)
      (hsorted : (s.val.map (fun x => x.val)).Pairwise (· ≤ ·))
      (hne : s.val ≠ []) :
      maxPrice (vals price) - minPrice (vals price) =
        (s.val.getD (s.val.length - 1) 0#i64).val - (s.val.getD 0 0#i64).val := by
    have hlen : 0 < s.val.length := List.length_pos_iff.mpr hne
    have hmax : maxPrice (vals price) = (s.val.getD (s.val.length - 1) 0#i64).val := by
      simp only [vals]
      rw [maxPrice_perm (hperm.symm.map (fun x => x.val)),
        I64_getLast_val_eq_maxPrice hne hsorted, List.getLast_eq_getElem hne,
        List.getD_eq_getElem _ 0#i64 (n := s.val.length - 1) (by omega)]
    have hmin : minPrice (vals price) = (s.val.getD 0 0#i64).val := by
      simp only [vals]
      rw [minPrice_perm (hperm.symm.map (fun x => x.val)),
        I64_head_val_eq_minPrice hne hsorted, List.head_eq_getElem_zero hne,
        List.getD_eq_getElem _ 0#i64 (n := 0) hlen]
    rw [hmax, hmin]

  /-! ### The body of `maximum_tastiness` -/

  theorem maximum_tastiness_main (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.maximum_tastiness price k ⦃ r =>
        k.val = 2 → (r : Std.I64).val = maxPrice (vals price) - minPrice (vals price) ⦄ := by
    have hn2 : 2 ≤ price.val.length := h_n
    have hkhi : k.val ≤ (price.val.length : ℤ) := h_k_hi
    have hlen' : price.val.length ≤ 100000 := h_len
    have hn0 : ¬ (Slice.len price = 0#usize) := by
      intro h
      have hv2 : price.val.length = 0 := by
        simpa [Slice.len_val] using congrArg (fun x : Usize => x.val) h
      omega
    have hsz : price.val.length < Usize.max := by
      have hmax : (100000 : ℕ) < Usize.max := by scalar_tac
      omega
    unfold Aegis.MaximumTastiness.maximum_tastiness
    rw [if_neg hn0]
    apply Aeneas.Std.WP.spec_bind
      (loop0_spec price (Slice.len price) (alloc.vec.Vec.new Std.I64) 0#usize
        (by simp) (by simp) (by simp) hsz)
    intro sorted hsorted
    simp only [Aeneas.Std.lift, bind_ok]
    apply Aeneas.Std.WP.spec_bind (slice_sort_spec sorted.slice)
    intro s1 hs1
    obtain ⟨hs1perm, hs1sorted⟩ := hs1
    have hsorted' : sorted.val = price.val := hsorted
    have hbs : ∀ x ∈ s1.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      refine h_price x ?_
      have h1 : x ∈ sorted.slice.val := hs1perm.mem_iff.mp hx
      rw [← hsorted']
      simpa only [alloc.vec.Vec.val] using h1
    have hvals_bnd : ∀ y ∈ vals price, 1 ≤ y ∧ y ≤ 1000000000 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact h_price x hx
    have hplen : (Slice.len price).val = price.val.length := Slice.len_val price
    have hlen_perm : s1.val.length = price.val.length := by
      have h1 : s1.val.length = sorted.val.length := List.Perm.length_eq hs1perm
      rw [h1, hsorted']
    have hs1len : 2 ≤ s1.val.length := by
      rw [hlen_perm]
      exact hn2
    have hperm' : s1.val.Perm price.val := by
      have h1 : s1.val.Perm sorted.val := hs1perm
      rw [hsorted'] at h1
      exact h1
    have hs : SortedVals s1.val := (sortedVals_iff s1.val).2 hs1sorted
    have hs1ne : s1.val ≠ [] := by
      intro h
      have h0 : s1.val.length = 0 := by simp [h]
      omega
    have hspread : maxPrice (vals price) - minPrice (vals price) =
        (s1.val.getD (s1.val.length - 1) 0#i64).val -
          (s1.val.getD 0 0#i64).val :=
      spread_of_sorted_perm price s1 hperm' hs1sorted hs1ne
    step*
    · have h1 : i.val = price.val.length - 1 := by rw [i_post, hplen]
      have h2 : ({ slice := s1 } : alloc.vec.Vec Std.I64).length = price.val.length := by
        simp only [alloc.vec.Vec.length, alloc.vec.Vec.val]
        exact hlen_perm
      omega
    · have h2 : ({ slice := s1 } : alloc.vec.Vec Std.I64).length = price.val.length := by
        simp only [alloc.vec.Vec.length, alloc.vec.Vec.val]
        exact hlen_perm
      have h1 : (0#usize).val = 0 := rfl
      rw [h1]
      omega
    · have h1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hbs _ (List.getElem_mem (by omega))
      have h2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [i2_post]
        exact hbs _ (List.getElem_mem (by omega))
      scalar_tac
    · have h1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hbs _ (List.getElem_mem (by omega))
      have h2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [i2_post]
        exact hbs _ (List.getElem_mem (by omega))
      scalar_tac
    · have h1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hbs _ (List.getElem_mem (by omega))
      have h2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [i2_post]
        exact hbs _ (List.getElem_mem (by omega))
      have hm : max_diff.val = i1.val - i2.val := max_diff_post
      scalar_tac
    · have h1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [i1_post]
        exact hbs _ (List.getElem_mem (by omega))
      have h2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [i2_post]
        exact hbs _ (List.getElem_mem (by omega))
      have hm : max_diff.val = i1.val - i2.val := max_diff_post
      scalar_tac
    · -- the binary search
      have hii : i.val < s1.val.length := by
        have h3 : i.val = price.val.length - 1 := by rw [i_post, hplen]
        omega
      have hieq : i.val = s1.val.length - 1 := by
        have h3 : i.val = price.val.length - 1 := by rw [i_post, hplen]
        omega
      have hi1eq : i1.val = (s1.val.getD i.val 0#i64).val := by
        rw [i1_post, List.getD_eq_getElem _ 0#i64 hii]
        rfl
      have hi2eq : i2.val = (s1.val.getD 0 0#i64).val := by
        rw [i2_post, List.getD_eq_getElem _ 0#i64 (n := 0) (by omega)]
        rfl
      have hmd : max_diff.val = i1.val - i2.val := max_diff_post
      have hhi' : hi.val = max_diff.val + 1 := hi_post
      have hle0 : (0#i64).val = 0 := rfl
      have hle0i : (s1.val.getD 0 0#i64).val ≤ (s1.val.getD i.val 0#i64).val :=
        getD_val_le_of_le hs (by omega) hii (by omega)
      have hlei : (s1.val.getD i.val 0#i64).val ≤
          (s1.val.getD (s1.val.length - 1) 0#i64).val :=
        getD_val_le_of_le hs hii (by omega) (by omega)
      have hb1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [hi1eq]
        exact hbs _ (getD_mem hii)
      have hb2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [hi2eq]
        exact hbs _ (getD_mem (by omega))
      refine loop1_spec k ({ slice := s1 } : alloc.vec.Vec Std.I64) 0#i64 hi
        (maxPrice (vals price) - minPrice (vals price)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [alloc.vec.Vec.val]
        omega
      · intro x hx
        exact hbs x hx
      · intro d
        by_cases hk2 : k.val = 2
        · have hspec : Aegis.MaximumTastiness.can_make
              (alloc.vec.Vec.deref ({ slice := s1 } : alloc.vec.Vec Std.I64)) k d ⦃ b =>
              (b = true ↔ d.val ≤ (s1.val.getD (s1.val.length - 1) 0#i64).val -
                (s1.val.getD 0 0#i64).val) ⦄ :=
            can_make_spec_k2_vec ({ slice := s1 } : alloc.vec.Vec Std.I64) k d hk2
              hs1len hs hbs
          refine Aeneas.Std.WP.spec_mono hspec ?_
          intro b hb' _
          rw [hspread]
          exact hb'
        · have hspec : Aegis.MaximumTastiness.can_make
              (alloc.vec.Vec.deref ({ slice := s1 } : alloc.vec.Vec Std.I64)) k d ⦃ _ => True ⦄ := by
            refine can_make_term _ k d ?_ ?_ ?_
            · omega
            · simpa only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val] using
                (show 1 ≤ s1.val.length by omega)
            · intro x hx
              exact hbs x (by simpa only [alloc.vec.Vec.deref, Slice.from_val,
                alloc.vec.Vec.val] using hx)
          refine Aeneas.Std.WP.spec_mono hspec ?_
          intro b _ hk2'
          exact absurd hk2' hk2
      · omega
      · rw [hle0]
      · rw [hle0, hhi', hmd, hi1eq, hi2eq]
        omega
      · rw [hhi', hmd]
        omega
      · intro _
        rw [hle0, hspread]
        omega
      · intro _
        have hgi : (s1.val.getD (s1.val.length - 1) 0#i64).val =
            (s1.val.getD i.val 0#i64).val := by
          rw [hieq]
        rw [hspread, hhi', hmd, hi1eq, hi2eq, hgi]
        omega

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry

  /-- **S1 (main, functional).**  Under the stated preconditions the function returns a
  result `r` equal to the largest tastiness of a `k`-element set of positions, where the
  tastiness of a selection is the minimum pairwise distance of its prices. -/
  theorem spec_S1 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxTastiness (vals price) k.val.toNat := by
    sorry

  /-- **S2 (no failure).**  Under the preconditions the function returns a result: it does
  not overflow, index out of bounds or panic. -/
  theorem spec_S2 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r := by
    sorry

  /-- **S3 (bounds).**  The returned result is nonnegative. -/
  theorem spec_S3 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧ 0 ≤ r.val := by
    sorry

  /-- **S4 (bounds).**  The result is at most the spread of the prices. -/
  theorem spec_S4 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    sorry

  /-- **S5 (witness).**  The result is the tastiness of some `k`-element selection of
  positions. -/
  theorem spec_S5 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧
          S.card = k.val.toNat ∧ tastinessOn (vals price) S = r.val := by
    sorry

  /-- **S6 (bounds).**  Every `k`-element selection has tastiness at most the result. -/
  theorem spec_S6 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length → S.card = k.val.toNat →
          tastinessOn (vals price) S ≤ r.val := by
    sorry

  /-- **S7 (relational).**  For every `d ≥ 0`, the result is at least `d` exactly when
  some `k`-element selection has all its pairwise distances at least `d`. -/
  theorem spec_S7 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ d : ℤ, 0 ≤ d → (d ≤ r.val ↔
          ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧ S.card = k.val.toNat ∧
            ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
              d ≤ absDiff ((vals price).getD i 0) ((vals price).getD j 0)) := by
    sorry

  /-- **S8 (witness).**  The result is the distance of an actual pair of positions. -/
  theorem spec_S8 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ i j : ℕ, i < j ∧ j < (vals price).length ∧
          r.val = absDiff ((vals price).getD i 0) ((vals price).getD j 0) := by
    sorry

  /-- **S9 (edge case `k = 2`).**  For `k = 2` the result is the full spread of the
  prices. -/
  theorem spec_9 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = 2 → r.val = maxPrice (vals price) - minPrice (vals price)) := by
    obtain ⟨r, hr, hspec⟩ :=
      spec_ok_exists (maximum_tastiness_main price k h_n h_k_lo h_k_hi h_len h_price)
    exact ⟨r, hr, hspec⟩

  /-- **S10 (edge case `k = len price`).**  For `k` equal to the length of the array the
  result is the minimum distance over all pairs of positions. -/
  theorem spec_S10 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length)) := by
    sorry

  /-- **S11 (edge case).**  The result vanishes exactly when the number of distinct price
  values is smaller than `k`. -/
  theorem spec_S11 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (r.val = 0 ↔ (vals price).dedup.length < k.val.toNat) := by
    sorry

  /-- **S12 (functional, via the sorted rearrangement).**  If `s` is a nondecreasing
  rearrangement of the prices, the result is the maximal, over all increasing index
  sequences `i_1 < … < i_k`, of the minimal consecutive gap `s[i_{t+1}] - s[i_t]`. -/
  theorem spec_S12 (price : Slice Std.I64) (k : Std.I64) (s : List ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_sorted : s.Pairwise (· ≤ ·)) (h_perm : s.Perm (vals price)) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxMinConsecutiveGap s k.val.toNat := by
    sorry

  /-- **S13 (invariance under permutation of the positions).**  Any array `q` obtained by
  permuting the entries of `price` yields the same maximal tastiness. -/
  theorem spec_S13 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, (vals q).Perm (vals price) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    sorry

  /-- **S14 (invariance under a uniform shift).**  Shifting all prices by the same integer
  `c` (staying within `[1, 10^9]`) does not change the maximal tastiness. -/
  theorem spec_S14 (price : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_c : ∀ x ∈ vals price, 1 ≤ x + c ∧ x + c ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, vals q = (vals price).map (fun x => x + c) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    sorry

  /-- **C1 (monotonicity in `k`).**  A larger required number of picks cannot increase the
  maximal tastiness. -/
  theorem spec_C1 (price : Slice Std.I64) (k1 k2 : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k1_lo : 2 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r1 r2, maximum_tastiness price k1 = ok r1 ∧ maximum_tastiness price k2 = ok r2 ∧
        r2.val ≤ r1.val := by
    sorry

  /-- **C2 (bounds).**  For `k` picks in an interval of width `W` the gap is at most
  `W / (k - 1)`. -/
  theorem spec_C2 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val - 1) * r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    sorry

  end AegisSpec.MaximumTastiness
