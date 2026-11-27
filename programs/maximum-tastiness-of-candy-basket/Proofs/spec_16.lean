import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_16` (maximum-tastiness-of-candy-basket).
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

  /-! ## Specifications -/

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
  theorem spec_S9 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = 2 → r.val = maxPrice (vals price) - minPrice (vals price)) := by
    sorry

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

  /-! ## Auxiliary lemmas for `spec_C2` -/

  section C2Aux

  /-- Insertion sort (`AegisShim.sortInsert`) does not fail and preserves the multiset of
  elements, in the form of the two membership inclusions plus the length. -/
  private theorem sortInsert_spec (x : Aeneas.Std.I64) (l : List Aeneas.Std.I64) :
      ∃ r, AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x l = .ok r ∧
        r.length = l.length + 1 ∧ (∀ y ∈ r, y = x ∨ y ∈ l) ∧ (∀ y ∈ l, y ∈ r) ∧ x ∈ r := by
    induction l with
    | nil =>
      refine ⟨[x], by simp [AegisShim.sortInsert], by simp, by simp, by simp, by simp⟩
    | cons hd tl ih =>
      obtain ⟨r, hr, hlen, hmem, hmeml, hmemx⟩ := ih
      by_cases hgt : compare x.val hd.val = .gt
      · refine ⟨hd :: r, by simp [AegisShim.sortInsert, hr, hgt], by simp [hlen], ?_, ?_,
          by simp [hmemx]⟩
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · exact Or.inr (by simp [hy])
          · rcases hmem y hy with h | h
            · exact Or.inl h
            · exact Or.inr (by simp [h])
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · subst hy; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hmeml y hy)
      · refine ⟨x :: hd :: tl, by simp [AegisShim.sortInsert, hgt], by simp, ?_, ?_, by simp⟩
        · intro y hy
          simp only [List.mem_cons] at hy ⊢
          rcases hy with hy | hy | hy
          · exact Or.inl hy
          · exact Or.inr (by simp [hy])
          · exact Or.inr (by simp [hy])
        · intro y hy
          simp only [List.mem_cons] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inr (by simp [hy])
          · exact Or.inr (by simp [hy])

  /-- Insertion sort does not fail and does not change the length or the set of elements. -/
  private theorem sortList_spec (l : List Aeneas.Std.I64) :
      ∃ r, AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp l = .ok r ∧
        r.length = l.length ∧ (∀ y ∈ r, y ∈ l) ∧ (∀ y ∈ l, y ∈ r) := by
    induction l with
    | nil => refine ⟨[], by simp [AegisShim.sortList], by simp, by simp, by simp⟩
    | cons hd tl ih =>
      obtain ⟨r, hr, hlen, h1, h2⟩ := ih
      obtain ⟨r2, hr2, hlen2, hmem, hmeml, hmemx⟩ := sortInsert_spec hd r
      refine ⟨r2, by simp [AegisShim.sortList, hr, hr2], by simp [hlen2, hlen], ?_, ?_⟩
      · intro y hy
        rcases hmem y hy with h | h
        · subst h; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (h1 y h)
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · subst hy; exact hmemx
        · exact hmeml y (h2 y hy)

  /-- `Slice.sort` does not fail, preserves the length and the elements. -/
  private theorem slice_sort_spec (s : Aeneas.Std.Slice Aeneas.Std.I64) :
      ∃ s' : Aeneas.Std.Slice Aeneas.Std.I64,
        alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s = .ok s' ∧
        s'.val.length = s.val.length ∧ (∀ y ∈ s'.val, y ∈ s.val) := by
    unfold alloc.slice.Slice.sort
    obtain ⟨r, hr, hlen, h1, h2⟩ := sortList_spec s.val
    rw [hr]
    simp only [Aeneas.Std.bind_ok]
    have hs : r.length ≤ Aeneas.Std.Usize.max := by
      rw [hlen]; exact Aeneas.Std.Slice.length_ineq s
    rw [dif_pos hs]
    refine ⟨_, rfl, by simpa using hlen, ?_⟩
    intro y hy
    exact h1 y (by simpa using hy)

  /-- Loop invariant of the copying loop `maximum_tastiness_loop0`. -/
  private def loop0_inv (price : Aeneas.Std.Slice Aeneas.Std.I64) (n : Aeneas.Std.Usize)
      (p : alloc.vec.Vec Aeneas.Std.I64 × Aeneas.Std.Usize) : Prop :=
    p.2.val ≤ n.val ∧ p.1.val = price.val.take p.2.val

  /-- One iteration of the copying loop `maximum_tastiness_loop0.body`. -/
  private theorem loop0_body_spec (price : Aeneas.Std.Slice Aeneas.Std.I64) (n : Aeneas.Std.Usize)
      (h_n : n.val = price.val.length) (h_len : n.val ≤ 100000)
      (sorted : alloc.vec.Vec Aeneas.Std.I64) (i : Aeneas.Std.Usize)
      (h_i : loop0_inv price n (sorted, i)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0.body price n sorted i ⦃ r =>
        match r with
        | .done v => v.val = price.val
        | .cont p => loop0_inv price n p ∧ n.val - p.2.val < n.val - i.val ⦄ := by
    obtain ⟨h_i1, h_i2⟩ := h_i
    dsimp only at h_i1 h_i2
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
    split
    · rename_i hlt
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.Slice.index_usize_spec price i (by scalar_tac))
      intro x1 hx1
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.alloc.vec.Vec.push_spec sorted x1 (by
          rw [h_i2]; simp [List.length_take]; scalar_tac))
      intro sorted1 hsorted1
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.Usize.add_spec (x := i) (by scalar_tac))
      intro i2 hi2
      simp only [Aeneas.Std.WP.spec_ok]
      have hi2v : (i2 : Nat) = i.val + 1 := by simpa using hi2
      have hx1v : x1 = price.val[i.val]'(by scalar_tac) := by
        simpa using hx1
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hsorted1, h_i2, hx1v, List.take_append_getElem (by scalar_tac)]
      congr 1
      scalar_tac
    · rename_i hlt
      simp only [Aeneas.Std.WP.spec_ok]
      have hin : i.val = n.val := by scalar_tac
      rw [h_i2, hin, h_n, List.take_of_length_le (by simp)]

  /-- The copying loop of `maximum_tastiness` returns (a vector holding) the whole array. -/
  private theorem maximum_tastiness_loop0_spec (price : Aeneas.Std.Slice Aeneas.Std.I64)
      (n : Aeneas.Std.Usize) (h_n : n.val = price.val.length) (h_len : n.val ≤ 100000)
      (sorted : alloc.vec.Vec Aeneas.Std.I64) (i : Aeneas.Std.Usize)
      (h_i : loop0_inv price n (sorted, i)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n sorted i
        ⦃ (v : alloc.vec.Vec Aeneas.Std.I64) => v.val = price.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
    apply Aeneas.Std.loop.spec_decr_nat (fun p : alloc.vec.Vec Aeneas.Std.I64 × Aeneas.Std.Usize =>
      n.val - p.2.val) (loop0_inv price n)
      (fun v : alloc.vec.Vec Aeneas.Std.I64 => v.val = price.val)
    · rintro ⟨sv, iv⟩ hx
      dsimp only
      refine Aeneas.Std.WP.spec_mono (loop0_body_spec price n h_n h_len sv iv hx) ?_
      intro r hr
      cases r with
      | done v => simpa using hr
      | cont p => simpa using hr
    · exact h_i

  /-- A list of integers whose consecutive entries (in the given order) differ by at least `d`. -/
  private def chainDn (d : ℤ) : List ℤ → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => d ≤ a - b ∧ chainDn d (b :: t)

  private theorem chainDn_cons {d x y : ℤ} {t : List ℤ} (h : chainDn d (y :: t))
      (hxy : d ≤ x - y) : chainDn d (x :: y :: t) := ⟨hxy, h⟩

  private theorem chainDn_telescope {d : ℤ} : ∀ (l : List ℤ), chainDn d l → ∀ (y x : ℤ),
      l.head? = some y → l.getLast? = some x → ((l.length : ℤ) - 1) * d ≤ y - x := by
    intro l
    induction l with
    | nil =>
      intro _ y x h1 _
      simp at h1
    | cons a l ih =>
      intro hc y x h1 h2
      cases l with
      | nil =>
        simp only [List.head?_cons, Option.some.injEq] at h1
        simp only [List.getLast?_singleton, Option.some.injEq] at h2
        subst h1
        subst h2
        simp
      | cons b t =>
        obtain ⟨hab, hc'⟩ := hc
        simp only [List.head?_cons, Option.some.injEq] at h1
        have h2' : (b :: t).getLast? = some x := by
          simpa [List.getLast?_cons_cons] using h2
        have ihb := ih hc' b x (by rfl) h2'
        subst h1
        simp only [List.length_cons] at ihb ⊢
        push_cast at ihb ⊢
        nlinarith

  /-- Invariant of the `can_make` scanning loop.  `acc` is the list of accepted values,
  most recent first; the loop state is `(count, last, i)`. -/
  private def canMakeInv (sorted : Aeneas.Std.Slice Aeneas.Std.I64) (k d : Aeneas.Std.I64)
      (n : Aeneas.Std.Usize) (st : Aeneas.Std.I64 × Aeneas.Std.I64 × Aeneas.Std.Usize) : Prop :=
    ∃ acc : List Aeneas.Std.I64,
      st.1.val = (acc.length : ℤ) ∧
      acc.head? = some st.2.1 ∧
      chainDn d.val (acc.map (fun x => x.val)) ∧
      (∀ x ∈ acc, x ∈ sorted.val) ∧
      1 ≤ st.1.val ∧ st.1.val < k.val ∧
      st.2.2.val ≤ n.val

  /-- One iteration of the scanning loop of `can_make`. -/
  private theorem can_make_loop_body_spec (sorted : Aeneas.Std.Slice Aeneas.Std.I64)
      (k d : Aeneas.Std.I64) (n : Aeneas.Std.Usize) (h_n : n.val = sorted.val.length)
      (h_bounds : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_k : 2 ≤ k.val) (h_kmax : k.val ≤ (sorted.val.length : ℤ)) (h_len : n.val ≤ 100000)
      (count last : Aeneas.Std.I64) (i : Aeneas.Std.Usize)
      (h_inv : canMakeInv sorted k d n (count, last, i)) :
      Aegis.MaximumTastiness.can_make_loop.body sorted k d n count last i ⦃ r =>
        match r with
        | .done b => b = true → ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
            (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn d.val (acc.map (fun x => x.val))
        | .cont st => canMakeInv sorted k d n st ∧ n.val - st.2.2.val < n.val - i.val ⦄ := by
    simp only [canMakeInv] at h_inv
    obtain ⟨acc, hlen, hhead, hchain, hmem, hc1, hck, hin⟩ := h_inv
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 hhead
    have haccmap : acc.map (fun x => x.val) = last.val :: ys.map (fun x => x.val) := by
      rw [hys]; simp
    have hchain2 : chainDn d.val (last.val :: ys.map (fun x => x.val)) := by
      rw [← haccmap]; exact hchain
    have hlastmem : last ∈ acc := by rw [hys]; exact List.mem_cons_self ..
    obtain ⟨hlastlo, hlasthi⟩ := h_bounds last (hmem last hlastmem)
    unfold Aegis.MaximumTastiness.can_make_loop.body
    split
    · rename_i hlt
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.Slice.index_usize_spec sorted i (by scalar_tac))
      intro i1 hi1
      have hi1mem : i1 ∈ sorted.val := by
        rw [hi1]
        exact List.getElem_mem _
      obtain ⟨hi1lo, hi1hi⟩ := h_bounds i1 hi1mem
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.I64.sub_spec (by scalar_tac) (by scalar_tac))
      intro i2 hi2
      split
      · rename_i hge
        have hgap : d.val ≤ i1.val - last.val := by scalar_tac
        apply Aeneas.Std.WP.spec_bind
          (Aeneas.Std.I64.add_spec (by scalar_tac) (by scalar_tac))
        intro count1 hcount1
        have hcount1v : count1.val = count.val + 1 := by simpa using hcount1
        split
        · rename_i hgek
          simp only [Aeneas.Std.WP.spec_ok]
          intro _
          have hc1k : count1.val = k.val := by scalar_tac
          refine ⟨i1 :: acc, ?_, ?_, ?_⟩
          · simp only [List.length_cons]
            scalar_tac
          · intro x hx
            rcases List.mem_cons.1 hx with h | h
            · rw [h]; exact hi1mem
            · exact hmem x h
          · rw [List.map_cons, haccmap]
            exact chainDn_cons hchain2 hgap
        · rename_i hgek
          apply Aeneas.Std.WP.spec_bind
            (Aeneas.Std.Usize.add_spec (x := i) (by scalar_tac))
          intro i3 hi3
          simp only [Aeneas.Std.WP.spec_ok]
          have hi3n : i3.val = i.val + 1 := by simpa using hi3
          refine ⟨?_, by scalar_tac⟩
          refine ⟨i1 :: acc, ?_, by simp, ?_, ?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
          · simp only [List.length_cons]
            scalar_tac
          · rw [List.map_cons, haccmap]
            exact chainDn_cons hchain2 hgap
          · intro x hx
            rcases List.mem_cons.1 hx with h | h
            · rw [h]; exact hi1mem
            · exact hmem x h
      · rename_i hge
        apply Aeneas.Std.WP.spec_bind
          (Aeneas.Std.Usize.add_spec (x := i) (by scalar_tac))
        intro i3 hi3
        simp only [Aeneas.Std.WP.spec_ok]
        have hi3n : i3.val = i.val + 1 := by simpa using hi3
        refine ⟨?_, by scalar_tac⟩
        exact ⟨acc, hlen, hhead, hchain, hmem, hc1, hck, by scalar_tac⟩
    · rename_i hlt
      simp only [Aeneas.Std.WP.spec_ok]
      intro hge
      scalar_tac

  /-- The scanning loop of `can_make` is sound: if it reports success, then there are `k`
  accepted values, pairwise separated by at least `d`, taken from the array. -/
  private theorem can_make_loop_spec (sorted : Aeneas.Std.Slice Aeneas.Std.I64)
      (k d : Aeneas.Std.I64) (n : Aeneas.Std.Usize) (h_n : n.val = sorted.val.length)
      (h_bounds : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_k : 2 ≤ k.val) (h_kmax : k.val ≤ (sorted.val.length : ℤ)) (h_len : n.val ≤ 100000)
      (count last : Aeneas.Std.I64) (i : Aeneas.Std.Usize)
      (h_inv : canMakeInv sorted k d n (count, last, i)) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i ⦃ (b : Bool) =>
        b = true → ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
          (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn d.val (acc.map (fun x => x.val)) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make_loop
    apply Aeneas.Std.loop.spec_decr_nat
      (fun st : Aeneas.Std.I64 × Aeneas.Std.I64 × Aeneas.Std.Usize => n.val - st.2.2.val)
      (canMakeInv sorted k d n)
      (fun b : Bool => b = true → ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
        (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn d.val (acc.map (fun x => x.val)))
    · rintro ⟨count', last', i'⟩ hst
      dsimp only
      refine Aeneas.Std.WP.spec_mono
        (can_make_loop_body_spec sorted k d n h_n h_bounds h_k h_kmax h_len count' last' i'
          hst) ?_
      intro r hr
      cases r with
      | done b => simpa using hr
      | cont st => simpa using hr
    · exact h_inv

  /-- Soundness of `can_make`. -/
  private theorem can_make_spec (sorted : Aeneas.Std.Slice Aeneas.Std.I64) (k d : Aeneas.Std.I64)
      (h_n : 2 ≤ sorted.val.length)
      (h_bounds : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_k : 2 ≤ k.val) (h_kmax : k.val ≤ (sorted.val.length : ℤ))
      (h_len : sorted.val.length ≤ 100000) :
      Aegis.MaximumTastiness.can_make sorted k d ⦃ (b : Bool) =>
        b = true → ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
          (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn d.val (acc.map (fun x => x.val)) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    dsimp only
    split
    · rename_i hk1
      simp only [Aeneas.Std.WP.spec_ok]
      intro _
      exfalso
      scalar_tac
    · rename_i hk1
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.Slice.index_usize_spec sorted 0#usize (by scalar_tac))
      intro last hlast
      have hlastmem : last ∈ sorted.val := by
        rw [hlast]
        exact List.getElem_mem _
      have hinit : canMakeInv sorted k d (Aeneas.Std.Slice.len sorted) (1#i64, last, 1#usize) := by
        dsimp only [canMakeInv]
        refine ⟨[last], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp [chainDn]
        · intro x hx
          rw [List.mem_singleton] at hx
          rw [hx]
          exact hlastmem
        · simp
        · simp
          scalar_tac
        · simp
          scalar_tac
      exact can_make_loop_spec sorted k d (Aeneas.Std.Slice.len sorted) (by simp)
        h_bounds h_k h_kmax (by simpa using h_len) (1#i64) last 1#usize hinit

  /-- `Int` truncating division by two of a number at least two is at least one. -/
  private theorem tdiv_two_ge_one {b : ℤ} (h : 2 ≤ b) : 1 ≤ b.tdiv 2 := by
    have hb : 0 ≤ b := by linarith
    have hn : b = ((b.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hb).symm
    have key : b.tdiv 2 = ((b.toNat / 2 : ℕ) : ℤ) := by
      conv => lhs; rw [hn]
      rw [Int.ofNat_tdiv]
      norm_num
    rw [key]
    have h2 : 1 ≤ b.toNat / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    omega

  /-- `Int` truncating division by two of a number at least two is at most `b - 1`. -/
  private theorem tdiv_two_le_sub_one {b : ℤ} (h : 2 ≤ b) : b.tdiv 2 ≤ b - 1 := by
    have hb : 0 ≤ b := by linarith
    have hn : b = ((b.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hb).symm
    have key : b.tdiv 2 = ((b.toNat / 2 : ℕ) : ℤ) := by
      conv => lhs; rw [hn]
      rw [Int.ofNat_tdiv]
      norm_num
    rw [key]
    have h2 : b.toNat / 2 < b.toNat := by
      apply Nat.div_lt_self
      · omega
      · norm_num
    omega

  /-- `minPrice` is a lower bound for every element. -/
  private theorem minPrice_le_of_mem {l : List ℤ} (_h : l ≠ []) {x : ℤ} (hx : x ∈ l) :
      minPrice l ≤ x := by
    have hne : l.toFinset.Nonempty := ⟨x, by simpa using hx⟩
    unfold minPrice
    rw [dif_pos hne]
    exact Finset.min'_le l.toFinset x (by simpa using hx)

  /-- `maxPrice` is an upper bound for every element. -/
  private theorem le_maxPrice_of_mem {l : List ℤ} (_h : l ≠ []) {x : ℤ} (hx : x ∈ l) :
      x ≤ maxPrice l := by
    have hne : l.toFinset.Nonempty := ⟨x, by simpa using hx⟩
    unfold maxPrice
    rw [dif_pos hne]
    exact Finset.le_max' l.toFinset x (by simpa using hx)

  /-- The minimum of a nonempty list is at most its maximum. -/
  private theorem minPrice_le_maxPrice {l : List ℤ} (h : l ≠ []) : minPrice l ≤ maxPrice l := by
    have hne : l.toFinset.Nonempty := ⟨l.head h, by simp⟩
    have hmem : l.toFinset.min' hne ∈ l := by
      simpa using Finset.min'_mem l.toFinset hne
    have h1 := minPrice_le_of_mem h hmem
    have h2 := le_maxPrice_of_mem h hmem
    linarith

  /-- Main combined bound: an I64 list whose values form a decreasing chain with gaps at least
  `d`, all lying in `[mn, mx]`, satisfies `((length : ℤ) - 1) * d ≤ mx - mn`. -/
  private theorem chain_bound_i64 {d mn mx : ℤ} {l : List Aeneas.Std.I64}
      (hl : chainDn d (l.map (fun x => x.val))) (hne : l ≠ [])
      (hlo : ∀ x ∈ l, mn ≤ x.val) (hhi : ∀ x ∈ l, x.val ≤ mx) :
      ((l.length : ℤ) - 1) * d ≤ mx - mn := by
    have hmap : l.map (fun x => x.val) ≠ [] := by
      intro hh
      exact hne (List.map_eq_nil_iff.mp hh)
    obtain ⟨xh, hxhm, hxhe⟩ := List.mem_map.mp (List.head_mem hmap)
    obtain ⟨xl, hxlm, hxle⟩ := List.mem_map.mp (List.getLast_mem hmap)
    have hhead : (l.map (fun x => x.val)).head? = some xh.val := by
      rw [hxhe]
      exact List.head?_eq_some_iff.mpr ⟨_, (List.cons_head_tail hmap).symm⟩
    have hlast : (l.map (fun x => x.val)).getLast? = some xl.val := by
      rw [hxle]
      exact List.getLast?_eq_getLast_of_ne_nil hmap
    have ht := chainDn_telescope (l.map (fun x => x.val)) hl xh.val xl.val hhead hlast
    rw [List.length_map] at ht
    have h1 : mn ≤ xl.val := hlo xl hxlm
    have h2 : xh.val ≤ mx := hhi xh hxhm
    linarith

  /-- Invariant of the binary-search loop of `maximum_tastiness`. -/
  private def bsInv (sorted : alloc.vec.Vec Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (st : Aeneas.Std.I64 × Aeneas.Std.I64) : Prop :=
    0 ≤ st.1.val ∧ st.1.val ≤ 1000000001 ∧ st.2.val ≤ 1000000001 ∧
      (st.1.val ≤ 0 ∨ ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
        (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn st.1.val (acc.map (fun x => x.val)))

  /-- One iteration of the binary-search loop of `maximum_tastiness`. -/
  private theorem loop1_body_spec (k : Aeneas.Std.I64) (sorted : alloc.vec.Vec Aeneas.Std.I64)
      (h_bounds : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_n : 2 ≤ sorted.val.length) (h_k : 2 ≤ k.val)
      (h_kmax : k.val ≤ (sorted.val.length : ℤ)) (h_len : sorted.val.length ≤ 100000)
      (lo hi : Aeneas.Std.I64) (h_inv : bsInv sorted k (lo, hi)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1.body k sorted lo hi ⦃ r =>
        match r with
        | .done v => v.val ≤ 0 ∨ ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
            (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn v.val (acc.map (fun x => x.val))
        | .cont st => bsInv sorted k st ∧
            (st.2.val - st.1.val).toNat < (hi.val - lo.val).toNat ⦄ := by
    simp only [bsInv] at h_inv
    obtain ⟨hlo0, hlo1, hhi1, hpost⟩ := h_inv
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
    apply Aeneas.Std.WP.spec_bind (Aeneas.Std.I64.add_spec (by scalar_tac) (by scalar_tac))
    intro i hi1
    have hin : i.val = lo.val + 1 := by simpa using hi1
    split
    · rename_i hlt
      have hkey : lo.val + 2 ≤ hi.val := by scalar_tac
      apply Aeneas.Std.WP.spec_bind (Aeneas.Std.I64.sub_spec (by scalar_tac) (by scalar_tac))
      intro i1 hi2
      have hi1v : i1.val = hi.val - lo.val := by simpa using hi2
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.I64.div_spec (x := i1) (y := 2#i64) (by simp) (by simp))
      intro i2 hi3
      have hi2v : i2.val = Int.tdiv i1.val 2 := by simpa using hi3
      have hi2_le : i2.val ≤ i1.val := by
        rw [hi2v]
        exact Int.tdiv_le_self 2 (by linarith)
      apply Aeneas.Std.WP.spec_bind (Aeneas.Std.I64.add_spec (by scalar_tac) (by scalar_tac))
      intro mid hi4
      have hmidv : mid.val = lo.val + i2.val := by simpa using hi4
      have hmid_gt : lo.val < mid.val := by
        have := tdiv_two_ge_one (b := i1.val) (by linarith)
        linarith
      have hmid_lt : mid.val < hi.val := by
        have := tdiv_two_le_sub_one (b := i1.val) (by linarith)
        linarith
      dsimp only
      have hb' : ∀ x ∈ (alloc.vec.Vec.deref sorted).val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
        simpa [alloc.vec.Vec.deref] using h_bounds
      have hn' : 2 ≤ (alloc.vec.Vec.deref sorted).val.length := by
        simpa [alloc.vec.Vec.deref] using h_n
      have hkmax' : k.val ≤ ((alloc.vec.Vec.deref sorted).val.length : ℤ) := by
        simpa [alloc.vec.Vec.deref] using h_kmax
      have hlen' : (alloc.vec.Vec.deref sorted).val.length ≤ 100000 := by
        simpa [alloc.vec.Vec.deref] using h_len
      apply Aeneas.Std.WP.spec_bind
        (can_make_spec (alloc.vec.Vec.deref sorted) k mid hn' hb' h_k hkmax' hlen')
      intro b hb
      split
      · rename_i hbtrue
        simp only [Aeneas.Std.WP.spec_ok]
        obtain ⟨acc, hlen', hmem', hchain'⟩ := hb hbtrue
        have hmem'' : ∀ x ∈ acc, x ∈ sorted.val := by simpa [alloc.vec.Vec.deref] using hmem'
        refine ⟨⟨by linarith, by linarith, by linarith, Or.inr ⟨acc, hlen', hmem'', hchain'⟩⟩, ?_⟩
        rw [Int.toNat_lt_toNat (by linarith)]
        linarith
      · rename_i hbfalse
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨⟨by linarith, by linarith, by linarith, hpost⟩, ?_⟩
        rw [Int.toNat_lt_toNat (by linarith)]
        linarith
    · rename_i hlt
      simp only [Aeneas.Std.WP.spec_ok]
      exact hpost

  /-- The binary-search loop of `maximum_tastiness`: if it stops, its result `r` is either
  nonpositive or it is a feasible gap for `k` picks. -/
  private theorem loop1_spec (k : Aeneas.Std.I64) (sorted : alloc.vec.Vec Aeneas.Std.I64)
      (h_bounds : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_n : 2 ≤ sorted.val.length) (h_k : 2 ≤ k.val)
      (h_kmax : k.val ≤ (sorted.val.length : ℤ)) (h_len : sorted.val.length ≤ 100000)
      (lo hi : Aeneas.Std.I64) (h_inv : bsInv sorted k (lo, hi)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi ⦃ (r : Aeneas.Std.I64) =>
        r.val ≤ 0 ∨ ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
          (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn r.val (acc.map (fun x => x.val)) ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
    apply Aeneas.Std.loop.spec_decr_nat
      (fun st : Aeneas.Std.I64 × Aeneas.Std.I64 => (st.2.val - st.1.val).toNat)
      (bsInv sorted k)
      (fun r : Aeneas.Std.I64 => r.val ≤ 0 ∨ ∃ acc : List Aeneas.Std.I64, (acc.length : ℤ) = k.val ∧
        (∀ x ∈ acc, x ∈ sorted.val) ∧ chainDn r.val (acc.map (fun x => x.val)))
    · rintro ⟨lo', hi'⟩ hst
      dsimp only
      refine Aeneas.Std.WP.spec_mono
        (loop1_body_spec k sorted h_bounds h_n h_k h_kmax h_len lo' hi' hst) ?_
      intro r hr
      cases r with
      | done v => simpa using hr
      | cont st => simpa using hr
    · exact h_inv

  /-- `Slice.sort` in specification (triple) form. -/
  private theorem slice_sort_spec' (s : Aeneas.Std.Slice Aeneas.Std.I64) :
      alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s ⦃ (s' : Aeneas.Std.Slice Aeneas.Std.I64) =>
        s'.val.length = s.val.length ∧ (∀ y ∈ s'.val, y ∈ s.val) ⦄ := by
    obtain ⟨s', hs', h1, h2⟩ := slice_sort_spec s
    rw [hs']
    simp only [Aeneas.Std.WP.spec_ok]
    exact ⟨h1, h2⟩

  /-- Extract a witness and the exact value from a triple. -/
  private theorem exists_ok_of_spec {α : Type} {m : Aeneas.Std.Result α} {p : α → Prop}
      (h : Aeneas.Std.WP.spec m p) : ∃ r, m = .ok r ∧ p r := by
    cases m using Aeneas.Std.Result.cases with
    | ret r => exact ⟨r, rfl, by simpa using h⟩
    | vis i k => exact absurd h (by simp)
    | div => exact absurd h (by simp)

  /-- The main function, in triple form. -/
  private theorem maximum_tastiness_spec (price : Aeneas.Std.Slice Aeneas.Std.I64)
      (k : Aeneas.Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.maximum_tastiness price k ⦃ (r : Aeneas.Std.I64) =>
        (k.val - 1) * r.val ≤ maxPrice (vals price) - minPrice (vals price) ⦄ := by
    have hne : vals price ≠ [] := by
      intro h
      have h2 : 2 ≤ (vals price).length := by simpa [vals] using h_n
      rw [h] at h2
      simp at h2
    have hspread : 0 ≤ maxPrice (vals price) - minPrice (vals price) := by
      have := minPrice_le_maxPrice hne
      linarith
    unfold Aegis.MaximumTastiness.maximum_tastiness
    dsimp only
    split
    · rename_i hn0
      simp only [Aeneas.Std.WP.spec_ok]
      have hz : ((0#i64 : Aeneas.Std.I64)).val = 0 := rfl
      rw [hz]
      have hz2 : (k.val - 1) * 0 = 0 := by ring
      rw [hz2]
      exact hspread
    · rename_i hn0
      have h0inv : loop0_inv price (Aeneas.Std.Slice.len price)
          (alloc.vec.Vec.new Aeneas.Std.I64, 0#usize) := by
        dsimp only [loop0_inv]
        exact ⟨by simp, by simp⟩
      apply Aeneas.Std.WP.spec_bind
        (maximum_tastiness_loop0_spec price (Aeneas.Std.Slice.len price) (by simp)
          (by simpa using h_len) (alloc.vec.Vec.new Aeneas.Std.I64) 0#usize h0inv)
      intro sorted0 hsorted0
      dsimp only [Aeneas.Std.lift]
      simp only [Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair]
      apply Aeneas.Std.WP.spec_bind (slice_sort_spec' sorted0.slice)
      intro s1 hs1
      obtain ⟨hs1len, hs1mem⟩ := hs1
      have hlen1 : s1.val.length = price.val.length := by
        rw [hs1len]
        show (↑sorted0 : List Aeneas.Std.I64).length = (↑price : List Aeneas.Std.I64).length
        exact congrArg List.length hsorted0
      have hmem_price : ∀ x ∈ s1.val, x ∈ price.val := by
        intro x hx
        have h2 : x ∈ sorted0.val := hs1mem x hx
        rw [hsorted0] at h2
        exact h2
      dsimp only
      simp only [Aeneas.Std.alloc.vec.Vec.index_slice_index]
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.Usize.sub_spec (x := Aeneas.Std.Slice.len price) (y := 1#usize)
          (by scalar_tac))
      intro i hi
      have hiv : i.val = price.val.length - 1 := by
        have h1 : i.val = (Aeneas.Std.Slice.len price).val - 1 := by simpa using hi.1
        simpa using h1
      have hi_lt : i.val < (alloc.vec.Vec.mk s1).val.length := by
        have hiv' : (↑i : ℕ) = (↑price : List Aeneas.Std.I64).length - 1 := hiv
        have hlen2 : (↑s1 : List Aeneas.Std.I64).length = (↑price : List Aeneas.Std.I64).length :=
          hlen1
        have hge : 2 ≤ (↑price : List Aeneas.Std.I64).length := h_n
        show (↑i : ℕ) < (↑s1 : List Aeneas.Std.I64).length
        omega
      have h0_lt : (0#usize).val < (alloc.vec.Vec.mk s1).val.length := by
        have hlen2 : (↑s1 : List Aeneas.Std.I64).length = (↑price : List Aeneas.Std.I64).length :=
          hlen1
        have hge : 2 ≤ (↑price : List Aeneas.Std.I64).length := h_n
        have h0v : (0#usize).val = 0 := rfl
        show (↑(0#usize) : ℕ) < (↑s1 : List Aeneas.Std.I64).length
        omega
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.alloc.vec.Vec.index_usize_spec (alloc.vec.Vec.mk s1)
          i hi_lt)
      intro i1 hi1
      have hi1mem : i1 ∈ s1.val := by
        rw [hi1]
        exact List.getElem_mem _
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.alloc.vec.Vec.index_usize_spec (alloc.vec.Vec.mk s1)
          0#usize h0_lt)
      intro i2 hi2
      have hi2mem : i2 ∈ s1.val := by
        rw [hi2]
        exact List.getElem_mem _
      obtain ⟨hi2lo, hi2hi⟩ := h_price i2 (hmem_price i2 hi2mem)
      obtain ⟨hi1lo, hi1hi⟩ := h_price i1 (hmem_price i1 hi1mem)
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.I64.sub_spec (x := i1) (y := i2) (by scalar_tac) (by scalar_tac))
      intro md hmd
      have hmdv : md.val = i1.val - i2.val := hmd
      have hmdhi : md.val ≤ 1000000000 - 1 := by scalar_tac
      apply Aeneas.Std.WP.spec_bind
        (Aeneas.Std.I64.add_spec (x := md) (y := 1#i64) (by scalar_tac) (by scalar_tac))
      intro hi2v hhi
      have hhi2v : hi2v.val = md.val + 1 := hhi
      have hhi2hi : hi2v.val ≤ 1000000001 := by scalar_tac
      refine Aeneas.Std.WP.spec_mono
        (loop1_spec k (alloc.vec.Vec.mk s1) ?_ ?_ h_k_lo ?_ ?_ 0#i64 hi2v ?_) ?_
      · -- value bounds of the sorted array
        intro x hx
        exact h_price x (hmem_price x hx)
      · -- length at least 2
        show 2 ≤ (↑s1 : List Aeneas.Std.I64).length
        have h1 : (↑s1 : List Aeneas.Std.I64).length = (↑price : List Aeneas.Std.I64).length :=
          hlen1
        have h2 : 2 ≤ (↑price : List Aeneas.Std.I64).length := h_n
        omega
      · -- k at most the length
        show k.val ≤ ((↑s1 : List Aeneas.Std.I64).length : ℤ)
        rw [show (↑s1 : List Aeneas.Std.I64).length = price.length from hlen1]
        exact h_k_hi
      · -- length at most 100000
        show (↑s1 : List Aeneas.Std.I64).length ≤ 100000
        rw [show (↑s1 : List Aeneas.Std.I64).length = price.length from hlen1]
        exact h_len
      · -- initial invariant
        dsimp only [bsInv]
        refine ⟨by simp, by simp, ?_, Or.inl (by simp)⟩
        exact hhi2hi
      · intro r hr
        rcases hr with hr0 | ⟨acc, hacc_len, hacc_mem, hacc_chain⟩
        · have h1 : 0 ≤ k.val - 1 := by linarith
          have h2 : (k.val - 1) * r.val ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hr0
          linarith
        · have hacc_ne : acc ≠ [] := by
            intro hnil
            rw [hnil] at hacc_len
            simp at hacc_len
            linarith
          have haccmem : ∀ x ∈ acc, x ∈ price.val := by
            intro x hx
            exact hmem_price x (hacc_mem x hx)
          have hlo : ∀ x ∈ acc, minPrice (vals price) ≤ x.val := by
            intro x hx
            refine minPrice_le_of_mem hne ?_
            simp only [vals, List.mem_map]
            exact ⟨x, haccmem x hx, rfl⟩
          have hhi' : ∀ x ∈ acc, x.val ≤ maxPrice (vals price) := by
            intro x hx
            refine le_maxPrice_of_mem hne ?_
            simp only [vals, List.mem_map]
            exact ⟨x, haccmem x hx, rfl⟩
          have hb1 := chain_bound_i64 hacc_chain hacc_ne hlo hhi'
          have heq : k.val - 1 = ((acc.length : ℤ) - 1) := by rw [hacc_len]
          rw [heq]
          exact hb1

  end C2Aux

  /-- **C2 (bounds).**  For `k` picks in an interval of width `W` the gap is at most
  `W / (k - 1)`. -/
  theorem spec_16 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val - 1) * r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    obtain ⟨r, hr, hpost⟩ :=
      exists_ok_of_spec (maximum_tastiness_spec price k h_n h_k_lo h_k_hi h_len h_price)
    exact ⟨r, hr, hpost⟩

  end AegisSpec.MaximumTastiness
