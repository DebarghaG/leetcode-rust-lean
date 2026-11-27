import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_15` (maximum-tastiness-of-candy-basket).
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

  /-! ## Helpers for `spec_C1` -/

  namespace C1

  /-! ### Specification of the insertion-sort model of `slice::sort` -/

  /-- Unfolding lemma for `AegisShim.sortInsert` on a nonempty list. -/
  private theorem sortInsert_cons (x y : Std.I64) (ys : List Std.I64) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x (y :: ys) =
        (if compare x.val y.val == Ordering.gt then
          Std.bind (AegisShim.sortInsert core.cmp.OrdI64.cmp x ys) (fun r => ok (y :: r))
        else ok (x :: y :: ys)) := by
    simp only [AegisShim.sortInsert, bind_ok]

  /-- `sortInsert` keeps the head when `x` is strictly greater than it. -/
  private theorem sortInsert_cons_gt (x y : Std.I64) (ys : List Std.I64) (h : y.val < x.val) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x (y :: ys) =
        Std.bind (AegisShim.sortInsert core.cmp.OrdI64.cmp x ys) (fun r => ok (y :: r)) := by
    rw [sortInsert_cons]
    simp [compare_gt_iff_gt.mpr h]

  /-- `sortInsert` puts `x` in front when it is not greater than the head. -/
  private theorem sortInsert_cons_le (x y : Std.I64) (ys : List Std.I64) (h : x.val ≤ y.val) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x (y :: ys) = ok (x :: y :: ys) := by
    rw [sortInsert_cons]
    simp [compare_le_iff_le.mpr h]

  /-- Unfolding lemma for `AegisShim.sortList` on a nonempty list. -/
  private theorem sortList_cons (x : Std.I64) (xs : List Std.I64) :
      AegisShim.sortList core.cmp.OrdI64.cmp (x :: xs) =
        Std.bind (AegisShim.sortList core.cmp.OrdI64.cmp xs)
          (fun r => AegisShim.sortInsert core.cmp.OrdI64.cmp x r) := by
    simp only [AegisShim.sortList]

  /-- **Insertion of one element** into a sorted list: the result is sorted, one longer,
  and contains nothing but `x` and the elements of the input. -/
  theorem sortInsert_spec (x : Std.I64) (l : List Std.I64)
      (hs : l.Pairwise (fun a b => a.val ≤ b.val)) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x l ⦃ r =>
        r.length = l.length + 1 ∧ r.Pairwise (fun a b => a.val ≤ b.val) ∧
        (∀ z ∈ r, z = x ∨ z ∈ l) ⦄ := by
    induction l with
    | nil => simp [AegisShim.sortInsert]
    | cons y ys ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      by_cases hlt : y.val < x.val
      · rw [sortInsert_cons_gt x y ys hlt]
        apply WP.spec_bind (m := AegisShim.sortInsert core.cmp.OrdI64.cmp x ys)
          (k := fun r => ok (y :: r))
          (Pₘ := fun r => r.length = ys.length + 1 ∧
            r.Pairwise (fun a b => a.val ≤ b.val) ∧ (∀ z ∈ r, z = x ∨ z ∈ ys))
        · exact ih htail
        · intro r hr
          simp only [WP.spec_ok]
          refine ⟨by simp [hr.1], ?_, ?_⟩
          · rw [List.pairwise_cons]
            refine ⟨fun z hz => ?_, hr.2.1⟩
            rcases hr.2.2 z hz with rfl | hz
            · exact le_of_lt hlt
            · exact hhead z hz
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inr (List.mem_cons_self ..)
            · rcases hr.2.2 z hz with rfl | hz
              · exact Or.inl rfl
              · exact Or.inr (List.mem_cons_of_mem y hz)
      · have hle : x.val ≤ y.val := not_lt.mp hlt
        rw [sortInsert_cons_le x y ys hle]
        simp only [WP.spec_ok]
        refine ⟨by simp, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨fun z hz => ?_, hs⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hle
          · exact le_trans hle (hhead z hz)
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr hz

  /-- **Insertion sort**: the result is a sorted rearrangement (a sublist) of the input. -/
  theorem sortList_spec (l : List Std.I64) :
      AegisShim.sortList core.cmp.OrdI64.cmp l ⦃ r =>
        r.length = l.length ∧ r.Pairwise (fun a b => a.val ≤ b.val) ∧
        (∀ z ∈ r, z ∈ l) ⦄ := by
    induction l with
    | nil => simp [AegisShim.sortList]
    | cons x xs ih =>
      rw [sortList_cons]
      apply WP.spec_bind (m := AegisShim.sortList core.cmp.OrdI64.cmp xs)
        (k := fun r => AegisShim.sortInsert core.cmp.OrdI64.cmp x r)
        (Pₘ := fun r => r.length = xs.length ∧
          r.Pairwise (fun a b => a.val ≤ b.val) ∧ (∀ z ∈ r, z ∈ xs))
      · exact ih
      · intro r hr
        refine WP.spec_mono (sortInsert_spec x r hr.2.1) ?_
        intro r' hr'
        refine ⟨by simp [hr'.1, hr.1], hr'.2.1, ?_⟩
        intro z hz
        rcases hr'.2.2 z hz with rfl | hz
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem x (hr.2.2 z hz)

  /-- Unfolding lemma for the model of `slice::sort`. -/
  private theorem Slice_sort_eq (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s =
        Std.bind (AegisShim.sortList core.cmp.OrdI64.cmp s.val)
          (fun l => if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic) := by
    simp only [alloc.slice.Slice.sort]

  /-- **`slice::sort`**: the resulting slice is a sorted rearrangement of the input. -/
  theorem Slice_sort_spec (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s ⦃ r =>
        r.val.length = s.val.length ∧ r.val.Pairwise (fun a b => a.val ≤ b.val) ∧
        (∀ z ∈ r.val, z ∈ s.val) ⦄ := by
    rw [Slice_sort_eq]
    apply WP.spec_bind (m := AegisShim.sortList core.cmp.OrdI64.cmp s.val)
      (k := fun l => if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic)
      (Pₘ := fun l => l.length = s.val.length ∧
        l.Pairwise (fun a b => a.val ≤ b.val) ∧ (∀ z ∈ l, z ∈ s.val))
    · exact sortList_spec s.val
    · intro l hl
      have hlen : l.length ≤ Usize.max := by rw [hl.1]; exact Slice.property s
      rw [dite_eq_left hlen]
      simp only [WP.spec_ok]
      refine ⟨?_, ?_, ?_⟩
      · rw [Slice.from_val]; exact hl.1
      · rw [Slice.from_val]; exact hl.2.1
      · intro z hz
        rw [Slice.from_val] at hz
        exact hl.2.2 z hz

  /-- Greedy chain: starting from the value `L`, accept `x` when `L + d ≤ x`. -/
  def saux (d L : ℤ) : List ℤ → List ℤ
    | [] => []
    | x :: xs => if L + d ≤ x then x :: saux d x xs else saux d L xs

  /-- `l` is a valid chain starting from `L` with gaps at least `d`. -/
  def ChainOK (d L : ℤ) : List ℤ → Prop
    | [] => True
    | x :: xs => L + d ≤ x ∧ ChainOK d x xs

  /-- `k` elements can be picked from the sorted price list `s` so that consecutive
  picked values are at least `d` apart. -/
  def Feas (s : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    k ≤ 1 + (saux d (s.getD 0 0) (s.drop 1)).length

  /-! ### Auxiliary lemmas for the greedy chain -/

  /-- A chain remains a chain when its start value is decreased. -/
  theorem ChainOK_start_le {d x y : ℤ} (hxy : x ≤ y) :
      ∀ {s : List ℤ}, ChainOK d y s → ChainOK d x s
    | [], _ => True.intro
    | z :: zs, h => by
        simp only [ChainOK] at h ⊢
        exact ⟨by omega, h.2⟩

  /-- A chain remains a chain when the required gap is decreased. -/
  theorem ChainOK_mono_d {d d' L : ℤ} (h : d' ≤ d) :
      ∀ {s : List ℤ}, ChainOK d L s → ChainOK d' L s
    | [], _ => True.intro
    | z :: zs, hc => by
        simp only [ChainOK] at hc ⊢
        exact ⟨by omega, ChainOK_mono_d h hc.2⟩

  /-- A prefix of a chain is a chain. -/
  theorem ChainOK_take {d L : ℤ} :
      ∀ (n : ℕ) {s : List ℤ}, ChainOK d L s → ChainOK d L (s.take n)
    | 0, _, _ => True.intro
    | n + 1, [], _ => True.intro
    | n + 1, z :: zs, hc => by
        rw [List.take_succ_cons]
        simp only [ChainOK] at hc ⊢
        exact ⟨hc.1, ChainOK_take n hc.2⟩

  /-- In a nondecreasing list, every entry after the first one is at least the first one. -/
  theorem getD_zero_le_of_mem_drop (s : List ℤ) (hs : s.Pairwise (· ≤ ·)) (hne : s ≠ [])
      {z : ℤ} (hz : z ∈ s.drop 1) : s.getD 0 0 ≤ z := by
    have hlen : 0 < s.length := List.length_pos_iff.mpr hne
    rw [List.getD_eq_getElem s 0 hlen]
    obtain ⟨j, hj, hzj⟩ := List.mem_iff_getElem.mp hz
    rw [← hzj, List.getElem_drop]
    have hj' : 1 + j < s.length := by
      have h2 : j < (s.drop 1).length := hj
      rw [List.length_drop] at h2
      omega
    exact List.SortedLE.getElem_le_getElem_of_le (List.Pairwise.sortedLE hs)
      (i := 0) (j := 1 + j) (hi := hlen) (hj := hj') (by omega)

  /-- In a nondecreasing list, every entry is at most the last one. -/
  theorem le_getD_last (s : List ℤ) (hs : s.Pairwise (· ≤ ·)) (hne : s ≠ [])
      {z : ℤ} (hz : z ∈ s) : z ≤ s.getD (s.length - 1) 0 := by
    have hlen : 0 < s.length := List.length_pos_iff.mpr hne
    rw [List.getD_eq_getElem s 0 (by omega)]
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
    rw [← hiz]
    exact List.SortedLE.getElem_le_getElem_of_le (List.Pairwise.sortedLE hs)
      (i := i) (j := s.length - 1) (hi := hi) (hj := by omega) (by omega)

  /-- `saux` accepts everything when the current value is a lower bound and the gap is
  nonpositive (generalized version, allowing the start value to vary). -/
  theorem saux_eq_self_aux (d : ℤ) (hd : d ≤ 0) :
      ∀ (l : List ℤ) (L : ℤ), (∀ z ∈ l, L ≤ z) → l.Pairwise (· ≤ ·) → saux d L l = l
    | [], _, _, _ => rfl
    | y :: xs, L, h, hs => by
        rw [List.pairwise_cons] at hs
        obtain ⟨hhead, htail⟩ := hs
        have hL : L + d ≤ y := by have := h y (by simp); omega
        rw [show saux d L (y :: xs) = y :: saux d y xs by simp [saux, hL]]
        rw [saux_eq_self_aux d hd xs y hhead htail]

  /-- Three facts about the greedy chain on a nondecreasing list, proved simultaneously. -/
  theorem saux_optimal_aux : ∀ (l : List ℤ), l.Pairwise (· ≤ ·) →
      (∀ d L, ChainOK d L (saux d L l) ∧ (saux d L l).Sublist l) ∧
      (∀ d L s, s.Sublist l → ChainOK d L s → s.length ≤ (saux d L l).length) ∧
      (∀ d L x, (∀ z ∈ l, x ≤ z) → L + d ≤ x →
        (saux d L l).length ≤ 1 + (saux d x l).length)
    | [], _ => by
        refine ⟨?_, ?_, ?_⟩
        · intro d L
          exact ⟨True.intro, List.nil_sublist []⟩
        · intro d L s hsub _
          have hs' : s = [] := List.sublist_nil.mp hsub
          subst hs'
          simp [saux]
        · intro d L x _ _
          simp [saux]
    | y :: xs, hs => by
        rw [List.pairwise_cons] at hs
        obtain ⟨hhead, htail⟩ := hs
        obtain ⟨ihA, ihB, ihC⟩ := saux_optimal_aux xs htail
        have hpos : ∀ {d L}, L + d ≤ y → saux d L (y :: xs) = y :: saux d y xs :=
          fun {_ _} hL => by simp [saux, hL]
        have hneg : ∀ {d L}, ¬ (L + d ≤ y) → saux d L (y :: xs) = saux d L xs :=
          fun {_ _} hL => by simp [saux, hL]
        have hlen_pos : ∀ {d L}, L + d ≤ y →
            (saux d L (y :: xs)).length = 1 + (saux d y xs).length :=
          fun {_ _} hL => by rw [hpos hL, List.length_cons]; omega
        have hlen_neg : ∀ {d L}, ¬ (L + d ≤ y) →
            (saux d L (y :: xs)).length = (saux d L xs).length :=
          fun {_ _} hL => by rw [hneg hL]
        refine ⟨?_, ?_, ?_⟩
        · intro d L
          by_cases hL : L + d ≤ y
          · rw [hpos hL]
            exact ⟨⟨hL, (ihA d y).1⟩, List.Sublist.cons_cons y (ihA d y).2⟩
          · rw [hneg hL]
            exact ⟨(ihA d L).1, (ihA d L).2.cons y⟩
        · intro d L s hsub hc
          rw [List.sublist_cons_iff] at hsub
          rcases hsub with hsub | ⟨r, rfl, hsubr⟩
          · by_cases hL : L + d ≤ y
            · rw [hlen_pos hL]
              have h1 := ihB d L s hsub hc
              have h2 := ihC d L y hhead hL
              omega
            · rw [hlen_neg hL]
              exact ihB d L s hsub hc
          · by_cases hL : L + d ≤ y
            · rw [hlen_pos hL, List.length_cons]
              have h1 := ihB d y r hsubr hc.2
              omega
            · exact absurd hc.1 hL
        · intro d L x hall hL
          have hxy : x ≤ y := hall y (by simp)
          have hLy : L + d ≤ y := by omega
          by_cases hx : x + d ≤ y
          · rw [hlen_pos hLy, hlen_pos hx]
            omega
          · rw [hlen_pos hLy, hlen_neg hx]
            have h1 : (saux d y xs).length ≤ (saux d x xs).length :=
              ihB d x (saux d y xs) (ihA d y).2 (ChainOK_start_le hxy (ihA d y).1)
            omega

  /-- The greedy chain is a valid chain and a sublist. -/
  theorem saux_chain (d L : ℤ) (l : List ℤ) :
      ChainOK d L (saux d L l) ∧ (saux d L l).Sublist l := by
    induction l generalizing L with
    | nil => exact ⟨trivial, List.nil_sublist []⟩
    | cons y xs ih =>
        by_cases hL : L + d ≤ y
        · rw [show saux d L (y :: xs) = y :: saux d y xs by simp [saux, hL]]
          exact ⟨⟨hL, (ih y).1⟩, List.Sublist.cons_cons y (ih y).2⟩
        · rw [show saux d L (y :: xs) = saux d L xs by simp [saux, hL]]
          exact ⟨(ih L).1, (ih L).2.cons y⟩

  /-- The greedy chain is optimal on a sorted list. -/
  theorem saux_optimal (d L : ℤ) (l : List ℤ) (hs : l.Pairwise (· ≤ ·)) (s : List ℤ)
      (hsub : s.Sublist l) (hc : ChainOK d L s) : s.length ≤ (saux d L l).length := by
    exact (saux_optimal_aux l hs).2.1 d L s hsub hc

  /-- `saux` accepts everything when all elements are at least the current value and the
  gap is nonpositive. -/
  theorem saux_eq_self (d L : ℤ) (l : List ℤ) (hd : d ≤ 0) (h : ∀ z ∈ l, L ≤ z)
      (hs : l.Pairwise (· ≤ ·)) :
      saux d L l = l :=
    saux_eq_self_aux d hd l L h hs

  /-- Feasibility is monotone in the gap. -/
  theorem Feas_mono_d (s : List ℤ) (k : ℕ) {d d' : ℤ} (hs : s.Pairwise (· ≤ ·)) (h : d' ≤ d)
      (hf : Feas s k d) : Feas s k d' := by
    have hsorted : (s.drop 1).Pairwise (· ≤ ·) := List.Pairwise.sublist (List.drop_sublist 1 s) hs
    have hchain := saux_chain d (s.getD 0 0) (s.drop 1)
    have hk : k - 1 ≤ (saux d (s.getD 0 0) (s.drop 1)).length := by
      simp only [Feas] at hf
      omega
    have htake : ((saux d (s.getD 0 0) (s.drop 1)).take (k - 1)).length = k - 1 := by
      rw [List.length_take]
      omega
    have hsub : ((saux d (s.getD 0 0) (s.drop 1)).take (k - 1)).Sublist (s.drop 1) :=
      (List.take_sublist (k - 1) _).trans hchain.2
    have hc : ChainOK d' (s.getD 0 0) ((saux d (s.getD 0 0) (s.drop 1)).take (k - 1)) :=
      ChainOK_mono_d h (ChainOK_take (k - 1) hchain.1)
    have hopt := saux_optimal d' (s.getD 0 0) (s.drop 1) hsorted _ hsub hc
    simp only [Feas]
    omega

  /-- Feasibility is monotone in the number of picks. -/
  theorem Feas_mono_k (s : List ℤ) {k k' : ℕ} {d : ℤ} (h : k' ≤ k) (hf : Feas s k d) :
      Feas s k' d := by
    simp only [Feas] at hf ⊢
    omega

  /-- Any number of picks up to the length is feasible for gap `0`. -/
  theorem Feas_zero (s : List ℤ) (k : ℕ) (hs : s.Pairwise (· ≤ ·)) (hne : s ≠ [])
      (hk : k ≤ s.length) : Feas s k 0 := by
    have hpair : (s.drop 1).Pairwise (· ≤ ·) := List.Pairwise.sublist (List.drop_sublist 1 s) hs
    have hd : ∀ z ∈ s.drop 1, s.getD 0 0 ≤ z := fun z hz =>
      getD_zero_le_of_mem_drop s hs hne hz
    have hself : saux 0 (s.getD 0 0) (s.drop 1) = s.drop 1 :=
      saux_eq_self 0 (s.getD 0 0) (s.drop 1) (by omega) hd hpair
    simp only [Feas]
    rw [hself, List.length_drop]
    omega

  /-- Nothing is feasible above the spread of the values. -/
  theorem not_Feas_of_lt (s : List ℤ) {k : ℕ} (hs : s.Pairwise (· ≤ ·)) (hne : s ≠ [])
      (hk : 2 ≤ k) {d : ℤ} (hd : s.getD 0 0 + d > s.getD (s.length - 1) 0) :
      ¬ Feas s k d := by
    intro hf
    simp only [Feas] at hf
    have hlen : 0 < (saux d (s.getD 0 0) (s.drop 1)).length := by omega
    obtain ⟨z, zs, hz⟩ : ∃ z zs, saux d (s.getD 0 0) (s.drop 1) = z :: zs := by
      match h : saux d (s.getD 0 0) (s.drop 1) with
      | [] => rw [h] at hlen; simp at hlen
      | z :: zs => exact ⟨z, zs, rfl⟩
    have hchain : ChainOK d (s.getD 0 0) (saux d (s.getD 0 0) (s.drop 1)) :=
      (saux_chain d (s.getD 0 0) (s.drop 1)).1
    rw [hz] at hchain
    have h1 : s.getD 0 0 + d ≤ z := hchain.1
    have hzmem : z ∈ s.drop 1 :=
      (saux_chain d (s.getD 0 0) (s.drop 1)).2.subset (by rw [hz]; simp)
    have hup : z ≤ s.getD (s.length - 1) 0 :=
      le_getD_last s hs hne (List.mem_of_mem_drop hzmem)
    omega

  /-- Dropping the value list at `j` (for `j` a valid index) exposes the `j`-th value as head. -/
  theorem vals_drop_eq (s : Slice Std.I64) (j : Nat) (hj : j < s.val.length) :
      (vals s).drop j = (s.val[j]).val :: (vals s).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa [vals] using hj)]
    simp [vals]

  /-- `saux` accepts its head when the gap condition holds. -/
  theorem saux_cons_eq (d L x : ℤ) (xs : List ℤ) (h : L + d ≤ x) :
      saux d L (x :: xs) = x :: saux d x xs := by
    simp [saux, h]

  /-- `saux` drops its head when the gap condition fails. -/
  theorem saux_cons_skip (d L x : ℤ) (xs : List ℤ) (h : ¬ (L + d ≤ x)) :
      saux d L (x :: xs) = saux d L xs := by
    simp [saux, h]

  /-- The loop invariant of `can_make_loop`. -/
  def loopInv (sorted : Slice Std.I64) (k d : Std.I64) (n : Usize)
      (p : Std.I64 × Std.I64 × Usize) : Prop :=
    p.1.val + (saux d.val p.2.1.val ((vals sorted).drop p.2.2.val)).length
        = 1 + (saux d.val ((vals sorted).getD 0 0) ((vals sorted).drop 1)).length ∧
      p.1.val < k.val ∧ p.2.2.val ≤ n.val ∧
      1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000

  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Usize)
      (count last : Std.I64) (i : Usize)
      (hne : sorted.val ≠ []) (hk : 2 ≤ k.val) (hd : 0 ≤ d.val)
      (hn : n.val = sorted.val.length)
      (hlow : ∀ z ∈ sorted.val, 1 ≤ z.val)
      (hhigh : ∀ z ∈ sorted.val, z.val ≤ 1000000000)
      (hi : i.val ≤ n.val)
      (hclt : count.val < k.val)
      (hlast : 1 ≤ last.val) (hlast2 : last.val ≤ 1000000000)
      (hinv : count.val + (saux d.val last.val ((vals sorted).drop i.val)).length
        = 1 + (saux d.val ((vals sorted).getD 0 0) ((vals sorted).drop 1)).length) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i ⦃ b =>
        (b = true ↔ Feas (vals sorted) k.val.toNat d.val) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make_loop
    apply Std.loop.spec_decr_nat
      (fun (p : Std.I64 × Std.I64 × Usize) => n.val - p.2.2.val)
      (loopInv sorted k d n)
      (fun b => b = true ↔ Feas (vals sorted) k.val.toNat d.val)
    · rintro ⟨c, l, ii⟩ ⟨hinv', hclt', hi', hl1', hl2'⟩
      dsimp only at hinv' hclt' hi' hl1' hl2' ⊢
      unfold Aegis.MaximumTastiness.can_make_loop.body
      split
      · rename_i hlt
        have hival : ii.val < n.val := by simpa using hlt
        have hlen : ii.val < sorted.val.length := by rw [← hn]; exact hival
        have hb1 : 1 ≤ (sorted.val[ii.val]).val := hlow _ (List.getElem_mem hlen)
        have hb2 : (sorted.val[ii.val]).val ≤ 1000000000 := hhigh _ (List.getElem_mem hlen)
        step
        subst i1
        step
        split
        · rename_i hge
          have hxs : l.val + d.val ≤ (sorted.val[ii.val]).val := by
            simp only [ge_iff_le, IScalar.le_equiv] at hge
            omega
          have hsplit : (saux d.val l.val ((vals sorted).drop ii.val)).length
              = 1 + (saux d.val (sorted.val[ii.val]).val
                  ((vals sorted).drop (ii.val + 1))).length := by
            rw [vals_drop_eq sorted ii.val hlen, saux_cons_eq _ _ _ _ hxs]
            simp only [List.length_cons]
            omega
          step
          split
          · rename_i hge1
            simp only [WP.spec_ok, Feas, ge_iff_le, IScalar.le_equiv] at hge1 ⊢
            rw [hsplit] at hinv'
            rw [true_iff]
            omega
          · rename_i hge1
            step
            have hclt1 : count1.val < k.val := by
              simp only [ge_iff_le, IScalar.le_equiv] at hge1
              omega
            have hi3n : i3.val ≤ n.val := by omega
            have hinv1 : count1.val + (saux d.val (sorted.val[ii.val]).val
                ((vals sorted).drop i3.val)).length
                = 1 + (saux d.val ((vals sorted).getD 0 0) ((vals sorted).drop 1)).length := by
              rw [hsplit] at hinv'
              rw [i3_post]
              omega
            refine ⟨?_, ?_⟩
            · simp only [loopInv]
              exact ⟨hinv1, hclt1, hi3n, hb1, hb2⟩
            · omega
        · rename_i hge
          have hxs : ¬ (l.val + d.val ≤ (sorted.val[ii.val]).val) := by
            simp only [ge_iff_le, IScalar.le_equiv] at hge
            omega
          have hskip : saux d.val l.val ((vals sorted).drop ii.val)
              = saux d.val l.val ((vals sorted).drop (ii.val + 1)) := by
            rw [vals_drop_eq sorted ii.val hlen]
            exact saux_cons_skip d.val l.val _ _ hxs
          step
          have hi3n : i3.val ≤ n.val := by omega
          have hinv1 : c.val + (saux d.val l.val ((vals sorted).drop i3.val)).length
              = 1 + (saux d.val ((vals sorted).getD 0 0) ((vals sorted).drop 1)).length := by
            rw [i3_post, ← hskip]
            exact hinv'
          refine ⟨?_, ?_⟩
          · simp only [loopInv]
            exact ⟨hinv1, hclt', hi3n, hl1', hl2'⟩
          · omega
      · rename_i hlt
        have hii_lt : ¬ ii.val < n.val := by simpa using hlt
        have hii : ii.val = n.val := by omega
        have hdrop0 : (vals sorted).drop ii.val = [] := by
          have h1 : ii.val = (vals sorted).length := by
            rw [hii, hn]; simp [vals]
          rw [h1]; simp
        have hcz : c.val
            = 1 + (saux d.val ((vals sorted).getD 0 0) ((vals sorted).drop 1)).length := by
          have h := hinv'
          rw [hdrop0] at h
          simpa [saux] using h
        simp only [WP.spec_ok, Feas, decide_eq_true_eq, ge_iff_le, IScalar.le_equiv]
        rw [hcz]
        constructor <;> intro h <;> omega
    · exact ⟨hinv, hclt, hi, hlast, hlast2⟩

  /-- Specification of the greedy counting function behind `can_make`. -/
  theorem can_make_spec (s : Slice Std.I64) (k d : Std.I64)
      (hne : s.val ≠ []) (hk : 2 ≤ k.val) (hd : 0 ≤ d.val)
      (hlow : ∀ z ∈ s.val, 1 ≤ z.val) (hhigh : ∀ z ∈ s.val, z.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make s k d ⦃ b =>
        (b = true ↔ Feas (s.val.map (fun x => x.val)) k.val.toNat d.val) ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    split
    · rename_i h
      exfalso
      simp only [IScalar.le_equiv] at h
      scalar_tac
    · rename_i hk1
      have hpos : 0 < s.val.length := List.length_pos_iff.mpr hne
      step
      subst b_post
      refine can_make_loop_spec s k d (Slice.len s) 1#i64 (s.val[0]) 1#usize
        hne hk hd ?_ hlow hhigh ?_ ?_ ?_ ?_ ?_
      · simp
      · have h1 : (1#usize).val = 1 := by decide
        simp only [h1, Slice.len_val]
        exact Nat.succ_le_of_lt hpos
      · have h1 : (1#i64).val = 1 := by decide
        rw [h1]
        omega
      · exact hlow _ (List.getElem_mem hpos)
      · exact hhigh _ (List.getElem_mem hpos)
      · have hgetD : (vals s).getD 0 0 = (s.val[0]).val := by
          have hvals : vals s = (s.val[0]).val :: (vals s).drop 1 := vals_drop_eq s 0 hpos
          rw [hvals]
          simp
        have h1u : (1#usize).val = 1 := by decide
        have h1i : (1#i64).val = 1 := by decide
        rw [hgetD, h1u, h1i]

  /-- Specification of the filling loop of `maximum_tastiness`. -/
  theorem loop0_spec (price : Slice Std.I64) (n : Usize) (v : alloc.vec.Vec Std.I64) (i : Usize)
      (hn : n.val = price.val.length) (hnm : n.val ≤ 100000)
      (hvi : i.val ≤ n.val) (hvl : v.val = price.val.take i.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n v i ⦃ r =>
        r.val = v.val ++ (price.val.drop i.val).take (n.val - i.val) ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec Std.I64 × Usize => n.val - p.2.val)
      (inv := fun p => p.1.val = v.val ++ (price.val.drop i.val).take (p.2.val - i.val) ∧ i.val ≤ p.2.val ∧ p.2.val ≤ n.val)
      (post := fun (r : alloc.vec.Vec Std.I64) => r.val = v.val ++ (price.val.drop i.val).take (n.val - i.val))
    · rintro ⟨v', i'⟩ ⟨hv', hi'1, hi'2⟩
      dsimp only at hv' hi'1 hi'2
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
      simp only
      split
      · rename_i hlt
        step
        · step
          · have h1 : (List.take (i.val) (price.val)).length ≤ 100000 := by
              have h := List.length_take_le (i.val) (price.val)
              omega
            have h2 : (List.take (i'.val - i.val) (List.drop (i.val) (price.val))).length ≤ 100000 := by
              have h3 := List.length_take_le (i'.val - i.val) (List.drop (i.val) (price.val))
              have h4 : (List.drop (i.val) (price.val)).length = (price.val).length - i.val := List.length_drop
              omega
            rw [hv', hvl, List.length_append]
            scalar_tac
          · step
            refine ⟨?_, ?_, ?_, ?_⟩
            · have e1 : (↑v : List Std.I64) ++ List.take (↑i' - ↑i) (List.drop ↑i ↑price) = List.take ↑i' ↑price := by
                rw [hvl, ← List.take_add (l := (↑price : List Std.I64)) (i := ↑i) (j := ↑i' - ↑i)]
                congr 1
                omega
              have e2 : (↑v : List Std.I64) ++ List.take (↑i' + 1 - ↑i) (List.drop ↑i ↑price)
                  = List.take (↑i' + 1) ↑price := by
                rw [hvl, ← List.take_add (l := (↑price : List Std.I64)) (i := ↑i) (j := ↑i' + 1 - ↑i)]
                congr 1
                omega
              rw [sorted1_post, hv', e1, i1_post, List.take_append_getElem, i2_post, ← e2]
            · have hi : (↑i' : Nat) ≤ ↑i2 := by
                rw [i2_post]
                exact Nat.le_succ _
              exact Nat.le_trans hi'1 hi
            · have h2 : (↑i' : Nat) < ↑n := by simpa using hlt
              rw [i2_post]
              exact Nat.lt_iff_add_one_le.mp h2
            · have h1 : (↑i' : Nat) < ↑n := by simpa using hlt
              have h2 : (↑i' : Nat) < ↑i2 := by
                rw [i2_post]
                exact Nat.lt_succ_self _
              exact Nat.sub_lt_sub_left h1 h2
      · rename_i hnlt
        rw [Aeneas.Std.WP.spec_ok]
        dsimp only
        have hie : (↑i' : Nat) = ↑n :=
          le_antisymm hi'2 (Nat.le_of_not_lt (by simpa using hnlt))
        rw [hv', hie]
    · simp [hvl, hvi]

  /-- Division by two, in `tdiv` form. -/
  theorem div2_spec (x : Std.I64) :
      x / 2#i64 ⦃ z => z.val = x.val.tdiv 2 ⦄ := by
    obtain ⟨z, hz, hzv⟩ := Aeneas.Std.IScalar.div_spec (x := x) (y := 2#i64) (by simp) (by simp)
    rw [hz]
    simpa using hzv

  /-- `spec` for the `Result` monad is the expected `∃ ok` statement. -/
  theorem spec_iff_exists {α : Type} (m : Result α) (p : α → Prop) :
      WP.spec m p ↔ ∃ v, m = ok v ∧ p v := by
    cases m with
    | ret v => simp [WP.spec_ok]
    | vis e k => rw [WP.spec_vis]; simp
    | div => rw [WP.spec_div]; simp

  /-- The model of `slice::sort` applied to a slice whose contents sort to `s`. -/
  theorem sort_slice_eq (s0 : Slice Std.I64) (s : List Std.I64)
      (h : AegisShim.sortList core.cmp.OrdI64.cmp s0.val = ok s)
      (hlen : s.length ≤ Usize.max) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s0 = ok (Slice.from s hlen) := by
    unfold alloc.slice.Slice.sort
    rw [h]
    simp only [bind_ok]
    rw [dite_eq_left hlen]

  /-- `getD` commutes with mapping to the underlying integers. -/
  theorem getD_map_val (l : List Std.I64) (n : ℕ) :
      (l.map (fun x => x.val)).getD n 0 = (l.getD n (0#i64)).val := by
    induction l generalizing n with
    | nil => cases n <;> rfl
    | cons a as' ih =>
      cases n with
      | zero => rfl
      | succ k => simpa using ih k


  /-- Specification of the binary search loop of `maximum_tastiness`. -/
  theorem loop1_spec (k : Std.I64) (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64)
      (hne : v.val.map (fun x => x.val) ≠ [])
      (hord : (v.val.map (fun x => x.val)).Pairwise (· ≤ ·))
      (hk : 2 ≤ k.val)
      (hval : ∀ z ∈ v.val, 1 ≤ z.val ∧ z.val ≤ 1000000000)
      (hlo_f : Feas (v.val.map (fun x => x.val)) k.val.toNat lo.val)
      (hhi_f : ∀ d : ℤ, hi.val ≤ d → ¬ Feas (v.val.map (fun x => x.val)) k.val.toNat d)
      (hlo0 : 0 ≤ lo.val) (hlt : lo.val < hi.val) (hhi_le : hi.val ≤ 1000000001) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k v lo hi ⦃ r =>
        Feas (v.val.map (fun x => x.val)) k.val.toNat r.val ∧
        ∀ d : ℤ, r.val < d → ¬ Feas (v.val.map (fun x => x.val)) k.val.toNat d ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun (p : Std.I64 × Std.I64) => (p.2.val - p.1.val).toNat)
      (inv := fun p => Feas (v.val.map (fun x => x.val)) k.val.toNat p.1.val ∧
        (∀ d : ℤ, p.2.val ≤ d → ¬ Feas (v.val.map (fun x => x.val)) k.val.toNat d) ∧
        0 ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ 1000000001)
    · intro p hp
      obtain ⟨hf, hh, h0, hlt', hle⟩ := hp
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
      step
      by_cases hcond : r < p.2
      · rw [if_pos hcond]
        step
        have hrv : r.val = p.1.val + 1 := r_post
        have hi1v : i1.val = p.2.val - p.1.val := i1_post
        have hrc : r.val < p.2.val := hcond
        have hi10 : 0 ≤ i1.val := by rw [hi1v]; omega
        have hgap2 : 2 ≤ i1.val := by rw [hi1v]; omega
        step with div2_spec
        have hi2v : i2.val = i1.val.tdiv 2 := i2_post
        have hi2pos : 0 ≤ i2.val := by
          rw [hi2v]; exact Int.tdiv_nonneg hi10 (by norm_num)
        have hi2lt : i2.val < i1.val := by
          rw [hi2v]
          have h1 := Int.tdiv_le_of_le_mul (a := i1.val) (b := i1.val - 1) (c := 2)
            (by norm_num) (by omega)
          rw [if_pos hi10] at h1
          omega
        have hi2ge : 1 ≤ i2.val := by
          rw [hi2v]
          exact Int.le_tdiv_of_mul_le (by norm_num) (by omega)
        step
        have hmidv : mid.val = p.1.val + i2.val := mid_post
        have hlo_mid : p.1.val < mid.val := by omega
        have hmid_hi : mid.val < p.2.val := by omega
        have hmid0 : 0 ≤ mid.val := by omega
        have hdv : v.deref.val = v.val := by
          unfold alloc.vec.Vec.deref
          exact Aeneas.Std.Slice.from_val v.val _
        have hv1 : ∀ z ∈ v.deref.val, 1 ≤ z.val := by
          intro z hz; rw [hdv] at hz; exact (hval z hz).1
        have hv2 : ∀ z ∈ v.deref.val, z.val ≤ 1000000000 := by
          intro z hz; rw [hdv] at hz; exact (hval z hz).2
        have hnev : v.deref.val ≠ [] := by
          rw [hdv]; intro h; exact hne (by rw [h]; rfl)
        step with can_make_spec
        rw [hdv] at b_post
        by_cases hb : b = true
        · rw [if_pos hb]
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨b_post.mp hb, fun d hd => hh d hd, hmid0, hmid_hi, by omega, ?_⟩
          rw [Int.toNat_lt_toNat (by omega)]
          omega
        · rw [if_neg hb]
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨hf, ?_, h0, hlo_mid, by omega, ?_⟩
          · intro d hd
            by_cases hdp : p.2.val ≤ d
            · exact hh d hdp
            · intro hfeas
              exact hb (b_post.mpr (Feas_mono_d _ _ hord (by omega) hfeas))
          · rw [Int.toNat_lt_toNat (by omega)]
            omega
      · rw [if_neg hcond]
        simp only [Aeneas.Std.WP.spec_ok]
        refine ⟨hf, ?_⟩
        intro d hd
        have hp2r : p.2.val ≤ r.val := by simpa using hcond
        exact hh d (by omega)
    · exact ⟨hlo_f, hhi_f, hlo0, hlt, hhi_le⟩

  theorem maximum_tastiness_spec (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (s : List Std.I64) (hsort : AegisShim.sortList core.cmp.OrdI64.cmp price.val = ok s)
      (hs_sorted : s.Pairwise (fun a b => a.val ≤ b.val))
      (hs_len : s.length = price.val.length)
      (hs_sub : ∀ z ∈ s, z ∈ price.val) :
      ∃ r, maximum_tastiness price k = ok r ∧
        Feas (s.map (fun x => x.val)) k.val.toNat r.val ∧
        ∀ d : ℤ, r.val < d → ¬ Feas (s.map (fun x => x.val)) k.val.toNat d := by
    rw [← spec_iff_exists]
    unfold maximum_tastiness
    have hnval : (Slice.len price).val = price.val.length := Slice.len_val price
    have hn2 : 2 ≤ price.val.length := h_n
    have hne0 : Slice.len price ≠ 0#usize := by
      intro h
      have h2 := congrArg (fun x : Usize => x.val) h
      rw [hnval] at h2
      have h4 : price.val.length = 0 := by simpa using h2
      rw [h4] at hn2
      exact absurd hn2 (by omega)
    rw [if_neg hne0]
    have hloop0 : WP.spec (Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price)
        (alloc.vec.Vec.new Std.I64) 0#usize) (fun v => v.val = price.val) := by
      have h := loop0_spec price (Slice.len price) (alloc.vec.Vec.new Std.I64) 0#usize
        hnval (by rw [hnval]; exact h_len) (by simp) (by simp)
      refine WP.spec_mono h ?_
      intro r hr
      rw [hr]
      simp [hnval]
    apply WP.spec_bind hloop0
    intro v hv
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_ok, Aeneas.Std.alloc.vec.Vec.deref_mut]
    have hsortv : AegisShim.sortList core.cmp.OrdI64.cmp v.slice.val = ok s := by
      have hvv : v.slice.val = price.val := hv
      rw [hvv]; exact hsort
    have hlenmax : s.length ≤ Usize.max := by rw [hs_len]; exact Slice.property price
    change WP.spec (do
        let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 v.slice
        let sorted1 : alloc.vec.Vec Std.I64 := { slice := s1 }
        let i ← price.len - 1#usize
        let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) sorted1 i
        let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) sorted1 0#usize
        let max_diff ← i1 - i2
        let hi ← max_diff + 1#i64
        Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted1 0#i64 hi) _
    rw [sort_slice_eq v.slice s hsortv hlenmax]
    simp only [Aeneas.Std.bind_ok]
    have hVval : ({ slice := Slice.from s hlenmax } : alloc.vec.Vec Std.I64).val = s := by
      simp [alloc.vec.Vec.val, Slice.from_val]
    have hVlen : ({ slice := Slice.from s hlenmax } : alloc.vec.Vec Std.I64).length = s.length := by
      simpa using congrArg List.length hVval
    have hslen2 : 2 ≤ s.length := by rw [hs_len]; exact hn2
    step
    have hi_lt : i.val < ({ slice := Slice.from s hlenmax } : alloc.vec.Vec Std.I64).length := by
      rw [hVlen]
      have h1 : i.val = (Slice.len price).val - 1 := i_post
      rw [hnval] at h1
      omega
    have h0_lt : (0#usize).val < ({ slice := Slice.from s hlenmax } : alloc.vec.Vec Std.I64).length := by
      rw [hVlen]
      have h1 : (0#usize).val = 0 := rfl
      omega
    step
    step
    -- identifications of the two indexed values with `getD` of the mapped list
    have hSlen : (s.map (fun x => x.val)).length = s.length := List.length_map ..
    have hleni : i.val < s.length := by
      have h := hi_lt
      rwa [hVlen] at h
    have hlen0 : (0#usize).val < s.length := by
      have h := h0_lt
      rwa [hVlen] at h
    have hlt : i.val = s.length - 1 := by
      have h2 : i.val = (Slice.len price).val - 1 := i_post
      rw [hnval] at h2
      omega
    have hi1v : i1.val = (s.map (fun x => x.val)).getD ((s.map (fun x => x.val)).length - 1) 0 := by
      have h1 : i1 = s[i.val]'hleni := by rw [i1_post]; simp only [hVval]
      rw [getD_map_val, hSlen, h1]
      have h2 : (s[i.val]'hleni).val = (s.getD i.val 0#i64).val := by
        rw [List.getD_eq_getElem s (0#i64) hleni]
      rw [h2, hlt]
    have hi2v : i2.val = (s.map (fun x => x.val)).getD 0 0 := by
      have hlen0' : 0 < s.length := by omega
      have h1 : i2 = s[0]'hlen0' := by rw [i2_post]; simp only [hVval]
      rw [getD_map_val, h1]
      have h2 : (s[0]'hlen0').val = (s.getD 0 0#i64).val := by
        rw [List.getD_eq_getElem s (0#i64) hlen0']
      rw [h2]
    have hsS : List.Pairwise (fun a b : ℤ => a ≤ b) (s.map (fun x : Std.I64 => x.val)) :=
      List.Pairwise.map (fun x : Std.I64 => x.val) (fun a b h => h) hs_sorted
    have hneS : (s.map (fun x => x.val)) ≠ [] := by
      intro h
      have h1 : (s.map (fun x => x.val)).length = 0 := by rw [h]; rfl
      rw [hSlen] at h1
      omega
    have hmemL : (s.map (fun x => x.val)).getD ((s.map (fun x => x.val)).length - 1) 0
        ∈ (s.map (fun x => x.val)) := by
      rw [List.getD_eq_getElem _ _ (by rw [hSlen]; omega)]
      exact List.getElem_mem ..
    have hmem0 : (s.map (fun x => x.val)).getD 0 0 ∈ (s.map (fun x => x.val)) := by
      rw [List.getD_eq_getElem _ _ (by rw [hSlen]; omega)]
      exact List.getElem_mem ..
    have hboundS : ∀ z ∈ (s.map (fun x => x.val)), 1 ≤ z ∧ z ≤ 1000000000 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact h_price x (hs_sub x hx)
    have hle : i2.val ≤ i1.val := by
      rw [hi1v, hi2v]
      exact le_getD_last _ hsS hneS hmem0
    have hi1b : i1.val ≤ 1000000000 := by
      have := hboundS _ hmemL
      rw [hi1v]; exact this.2
    have hi2b : 1 ≤ i2.val := by
      have := hboundS _ hmem0
      rw [hi2v]; exact this.1
    step
    have hmd : max_diff.val ≤ 1000000000 := by rw [max_diff_post]; omega
    step
    -- hi = i1 - i2 + 1
    have hzero : (0#i64).val = 0 := rfl
    have hk2 : 2 ≤ k.val.toNat := by
      have h3 : (k.val.toNat : ℤ) = k.val := Int.toNat_of_nonneg (by omega)
      omega
    have hhiv : hi.val = i1.val - i2.val + 1 := by
      rw [hi_post, max_diff_post]
    have hhi_lt : 0 < hi.val := by rw [hhiv]; omega
    have hhi_le : hi.val ≤ 1000000001 := by rw [hhiv]; omega
    have hhi_f : ∀ d : ℤ, hi.val ≤ d →
        ¬ Feas (s.map (fun x => x.val)) k.val.toNat d := by
      intro d hd
      refine not_Feas_of_lt _ hsS hneS hk2 ?_
      rw [← hi2v, ← hi1v]
      omega
    have hlo_f : Feas (s.map (fun x => x.val)) k.val.toNat (0#i64).val := by
      rw [hzero]
      refine Feas_zero _ _ hsS hneS ?_
      rw [hSlen]
      have h2 : k.val ≤ (price.length : ℤ) := h_k_hi
      have h3 : (price.val.length : ℤ) = (price.length : ℤ) := rfl
      omega
    have hloop1 := loop1_spec k { slice := Slice.from s hlenmax } 0#i64 hi
      (by rw [hVval]; exact hneS) (by rw [hVval]; exact hsS) h_k_lo
      (by intro z hz; rw [hVval] at hz; exact hboundS z.val (List.mem_map_of_mem hz))
      (by rw [hVval]; exact hlo_f) (by rw [hVval]; exact hhi_f)
      (by rw [hzero]) hhi_lt hhi_le
    rw [hVval] at hloop1
    exact hloop1

  end C1

  /-- **C1 (monotonicity in `k`).**  A larger required number of picks cannot increase the
  maximal tastiness. -/
  theorem spec_15 (price : Slice Std.I64) (k1 k2 : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k1_lo : 2 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r1 r2, maximum_tastiness price k1 = ok r1 ∧ maximum_tastiness price k2 = ok r2 ∧
        r2.val ≤ r1.val := by
    obtain ⟨s, hsort, hs_len, hs_sorted, hs_sub⟩ :=
      (C1.spec_iff_exists _ _).mp (C1.sortList_spec price.val)
    obtain ⟨r1, hr1, hf1, hu1⟩ :=
      C1.maximum_tastiness_spec price k1 h_n h_k1_lo (le_trans h_k12 h_k2_hi) h_len h_price
        s hsort hs_sorted hs_len hs_sub
    obtain ⟨r2, hr2, hf2, hu2⟩ :=
      C1.maximum_tastiness_spec price k2 h_n (le_trans h_k1_lo h_k12) h_k2_hi h_len h_price
        s hsort hs_sorted hs_len hs_sub
    refine ⟨r1, r2, hr1, hr2, ?_⟩
    by_contra hc
    have hc' : r1.val < r2.val := by omega
    have hk12' : k1.val.toNat ≤ k2.val.toNat := by
      have h := h_k12
      omega
    exact hu1 r2.val hc' (C1.Feas_mono_k _ hk12' hf2)

  end AegisSpec.MaximumTastiness
