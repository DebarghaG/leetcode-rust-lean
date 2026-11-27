import Aegis.MaximumTastiness.Code.Funs
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card

/-
Proof of `AegisSpec.MaximumTastiness.spec_5` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary development for `spec_S5` -/

  open Aegis.MaximumTastiness

  local notation "cmpI" => Aeneas.Std.liftFun2 Aeneas.Std.core.cmp.impls.OrdI64.cmp

  /-- `l` is nondecreasing w.r.t. the integer values of its elements. -/
  def SortedV (l : List Std.I64) : Prop := l.Pairwise (fun a b => a.val ≤ b.val)

  theorem cmpI_eq : (Aeneas.Std.core.cmp.OrdI64.cmp : Std.I64 → Std.I64 → Result Ordering) = cmpI := rfl

  theorem cmpI_spec (x y : Std.I64) : cmpI x y = ok (compare x.val y.val) := rfl

  theorem cmp_eq_gt_iff {x y : Std.I64} : cmpI x y = ok Ordering.gt ↔ y.val < x.val := by
    rw [cmpI_spec, Result.ok.injEq]
    exact compare_gt_iff_gt

  theorem sortInsert_gt (x y : Std.I64) (ys : List Std.I64) (h : y.val < x.val) :
      AegisShim.sortInsert cmpI x (y :: ys)
        = (do let r ← AegisShim.sortInsert cmpI x ys; ok (y :: r)) := by
    have hc : compare x.val y.val = Ordering.gt := compare_gt_iff_gt.mpr h
    simp only [AegisShim.sortInsert]
    simp only [cmpI_spec, hc, bind_ok]
    simp

  theorem sortInsert_not_gt (x y : Std.I64) (ys : List Std.I64) (h : x.val ≤ y.val) :
      AegisShim.sortInsert cmpI x (y :: ys) = ok (x :: y :: ys) := by
    have hc : compare x.val y.val ≠ Ordering.gt := compare_le_iff_le.mpr h
    have hb : (compare x.val y.val == Ordering.gt) = false := by
      simp [hc]
    simp only [AegisShim.sortInsert]
    simp only [cmpI_spec, hb, bind_ok, Bool.false_eq_true, if_false]

  theorem sortInsert_spec (x : Std.I64) :
      ∀ l : List Std.I64, SortedV l →
        ∃ r, AegisShim.sortInsert cmpI x l = ok r ∧ r.Perm (x :: l) ∧ SortedV r
    | [], _ => by
      refine ⟨[x], ?_, ?_, ?_⟩
      · simp [AegisShim.sortInsert]
      · simp
      · simp [SortedV]
    | y :: ys, h => by
      obtain ⟨hyle, hys⟩ := List.pairwise_cons.mp h
      obtain ⟨r, hr, hperm, hsorted⟩ := sortInsert_spec x ys hys
      rcases lt_or_ge y.val x.val with hlt | hge
      · rw [sortInsert_gt x y ys hlt, hr]
        refine ⟨y :: r, ?_, (List.Perm.cons y hperm).trans (List.Perm.swap x y ys),
          List.pairwise_cons.mpr ⟨fun z hz => by
            rcases List.mem_cons.mp ((hperm.mem_iff).mp hz) with hzx | hzy
            · rw [hzx]; omega
            · exact hyle z hzy, hsorted⟩⟩
        simp only [bind_ok]
      · rw [sortInsert_not_gt x y ys hge]
        exact ⟨x :: y :: ys, rfl, List.Perm.refl _,
          List.pairwise_cons.mpr ⟨fun z hz => by
            rcases List.mem_cons.mp hz with hzy | hzys
            · rw [hzy]; omega
            · exact le_trans hge (hyle z hzys),
          List.pairwise_cons.mpr ⟨hyle, hys⟩⟩⟩

  theorem sortList_spec :
      ∀ l : List Std.I64, ∃ r, AegisShim.sortList cmpI l = ok r ∧
        r.Perm l ∧ SortedV r ∧ r.length = l.length
    | [] => ⟨[], by simp [AegisShim.sortList], by simp, by simp [SortedV], rfl⟩
    | x :: xs => by
      obtain ⟨r, hr, hperm, hsorted, hlen⟩ := sortList_spec xs
      obtain ⟨r', hr', hperm', hsorted'⟩ := sortInsert_spec x r hsorted
      refine ⟨r', ?_, ?_, hsorted', ?_⟩
      · simp only [AegisShim.sortList, hr, bind_ok]
        exact hr'
      · exact hperm'.trans (List.Perm.cons x hperm)
      · rw [hperm'.length_eq]
        simp [hlen]

  theorem sort_spec (s : Slice Std.I64) :
      ∃ t : Slice Std.I64, alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s = ok t ∧
        t.val.Perm s.val ∧ SortedV t.val ∧ t.length = s.length := by
    obtain ⟨r, hr, hperm, hsorted, hlen⟩ := sortList_spec s.val
    have hb : r.length ≤ Usize.max := by rw [hlen]; exact s.property
    have hstep : alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s
        = (do let l ← AegisShim.sortList cmpI s.val
              if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic) := rfl
    refine ⟨Slice.from r hb, ?_, ?_, ?_, ?_⟩
    · rw [hstep, hr]
      simp only [bind_ok]
      rw [dif_pos hb]
    · rw [Slice.from_val]; exact hperm
    · rw [Slice.from_val]; exact hsorted
    · show (Slice.from r hb).val.length = s.val.length
      rw [Slice.from_val, hlen]

  /-! ### Monotonicity of a sorted list, read through `getD` -/

  theorem pairwise_getD_le {l : List ℤ} (h : l.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < l.length) :
      ∀ {j : ℕ}, i ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0 := by
    intro j hij hj
    revert hj
    refine Nat.le_induction (motive := fun n _ => n < l.length → l.getD i 0 ≤ l.getD n 0)
      (by intro _; exact le_refl _) ?_ j hij
    intro n _ ih hn1
    have hn : n < l.length := by omega
    have hstep : l.getD n 0 ≤ l.getD (n + 1) 0 := by
      rw [List.getD_eq_getElem l 0 hn, List.getD_eq_getElem l 0 hn1]
      exact List.pairwise_iff_get.mp h ⟨n, hn⟩ ⟨n + 1, hn1⟩ (by simp)
    exact le_trans (ih hn) hstep

  theorem getD_mono {l : List ℤ} (h : l.Pairwise (· ≤ ·)) {i j : ℕ}
      (hij : i ≤ j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 :=
    pairwise_getD_le h (lt_of_le_of_lt hij hj) hij hj

  /-! ### The greedy selection -/

  /-- Greedy scan of `l` with `n` steps left, starting at index `start` with last picked value `L`:
  pick `start` whenever `l[start] - L ≥ d`, then move on. -/
  def gpicksF (l : List ℤ) (d : ℤ) : ℕ → ℕ → ℤ → List ℕ
    | 0, _, _ => []
    | n + 1, start, L =>
        if start < l.length then
          (if d ≤ l.getD start 0 - L then
            start :: gpicksF l d n (start + 1) (l.getD start 0)
           else gpicksF l d n (start + 1) L)
        else []

  /-- The indices picked by the greedy scan of `l` from index `start` with last picked value `L`. -/
  def gpicks (l : List ℤ) (d : ℤ) (start : ℕ) (L : ℤ) : List ℕ :=
    gpicksF l d (l.length - start) start L

  theorem gpicksF_pick {l : List ℤ} {d : ℤ} {n start : ℕ} {L : ℤ}
      (h : start < l.length) (hd : d ≤ l.getD start 0 - L) :
      gpicksF l d (n + 1) start L = start :: gpicksF l d n (start + 1) (l.getD start 0) := by
    simp only [gpicksF, if_pos h, if_pos hd]

  theorem gpicksF_skip {l : List ℤ} {d : ℤ} {n start : ℕ} {L : ℤ}
      (h : start < l.length) (hd : ¬ d ≤ l.getD start 0 - L) :
      gpicksF l d (n + 1) start L = gpicksF l d n (start + 1) L := by
    simp only [gpicksF, if_pos h, if_neg hd]

  theorem gpicksF_stop {l : List ℤ} {d : ℤ} {n start : ℕ} {L : ℤ}
      (h : ¬ start < l.length) : gpicksF l d (n + 1) start L = [] := by
    simp only [gpicksF, if_neg h]

  theorem gpicks_pick {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ}
      (h : start < l.length) (hd : d ≤ l.getD start 0 - L) :
      gpicks l d start L = start :: gpicks l d (start + 1) (l.getD start 0) := by
    have h1 : l.length - start = (l.length - start - 1) + 1 := by omega
    have h2 : l.length - (start + 1) = l.length - start - 1 := by omega
    simp only [gpicks]
    rw [h1, gpicksF_pick h hd, h2]

  theorem gpicks_skip {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ}
      (h : start < l.length) (hd : ¬ d ≤ l.getD start 0 - L) :
      gpicks l d start L = gpicks l d (start + 1) L := by
    have h1 : l.length - start = (l.length - start - 1) + 1 := by omega
    have h2 : l.length - (start + 1) = l.length - start - 1 := by omega
    simp only [gpicks]
    rw [h1, gpicksF_skip h hd, h2]

  theorem gpicksF_bounds {l : List ℤ} {d : ℤ} :
      ∀ (n start : ℕ) (L : ℤ), l.length - start ≤ n →
        ∀ x ∈ gpicksF l d n start L, start ≤ x ∧ x < l.length
    | 0, start, L, h, x, hx => by simp [gpicksF] at hx
    | n + 1, start, L, h, x, hx => by
      by_cases hs : start < l.length
      · by_cases hd : d ≤ l.getD start 0 - L
        · rw [gpicksF_pick hs hd] at hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨le_refl _, hs⟩
          · have := gpicksF_bounds n (start + 1) (l.getD start 0) (by omega) x hx'
            omega
        · rw [gpicksF_skip hs hd] at hx
          have := gpicksF_bounds n (start + 1) L (by omega) x hx
          omega
      · rw [gpicksF_stop hs] at hx
        simp at hx

  theorem gpicks_bounds {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ} :
      ∀ x ∈ gpicks l d start L, start ≤ x ∧ x < l.length :=
    gpicksF_bounds (l.length - start) start L (le_refl _)

  theorem gpicksF_head {l : List ℤ} {d : ℤ} :
      ∀ (n start : ℕ) (L : ℤ), ∀ z ∈ (gpicksF l d n start L).head?, d ≤ l.getD z 0 - L
    | 0, start, L, z, hz => by simp [gpicksF] at hz
    | n + 1, start, L, z, hz => by
      by_cases hs : start < l.length
      · by_cases hd : d ≤ l.getD start 0 - L
        · rw [gpicksF_pick hs hd] at hz
          simp only [List.head?_cons, Option.mem_some_iff] at hz
          rw [← hz]; exact hd
        · rw [gpicksF_skip hs hd] at hz
          exact gpicksF_head n (start + 1) L z hz
      · rw [gpicksF_stop hs] at hz
        simp at hz

  theorem gpicksF_chain {l : List ℤ} {d : ℤ} (hS : l.Pairwise (· ≤ ·)) :
      ∀ (n start : ℕ) (L : ℤ), l.length - start ≤ n →
        (∀ x ∈ gpicksF l d n start L, start ≤ x ∧ x < l.length) ∧
        (∀ t, t + 1 < (gpicksF l d n start L).length →
          d ≤ l.getD ((gpicksF l d n start L).getD (t + 1) 0) 0 -
              l.getD ((gpicksF l d n start L).getD t 0) 0)
    | 0, start, L, _ => by simp [gpicksF]
    | n + 1, start, L, hf => by
      by_cases hs : start < l.length
      · by_cases hd : d ≤ l.getD start 0 - L
        · obtain ⟨b1, b2⟩ := gpicksF_chain hS n (start + 1) (l.getD start 0) (by omega)
          have hres : gpicksF l d (n + 1) start L
              = start :: gpicksF l d n (start + 1) (l.getD start 0) := gpicksF_pick hs hd
          have hhead : ∀ z ∈ (gpicksF l d n (start + 1) (l.getD start 0)).head?,
              d ≤ l.getD z 0 - l.getD start 0 :=
            gpicksF_head n (start + 1) (l.getD start 0)
          rw [hres]
          refine ⟨?_, ?_⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact ⟨le_refl _, hs⟩
            · have := b1 y hy'; omega
          · rcases rest : gpicksF l d n (start + 1) (l.getD start 0) with _ | ⟨z, zs⟩
            · intro t ht
              simp at ht
            · intro t ht
              rw [rest] at b2
              rcases t with _ | t'
              · have hz := hhead z (by rw [rest]; simp)
                simpa using hz
              · have h2 := b2 t' (by simpa using ht)
                simpa using h2
        · rw [gpicksF_skip hs hd]
          obtain ⟨c1, c2⟩ := gpicksF_chain hS n (start + 1) L (by omega)
          exact ⟨fun x hx => by have := c1 x hx; omega, c2⟩
      · rw [gpicksF_stop hs]
        simp

  theorem gpicks_head {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ} :
      ∀ z ∈ (gpicks l d start L).head?, d ≤ l.getD z 0 - L :=
    gpicksF_head (l.length - start) start L

  theorem gpicks_chain {l : List ℤ} {d : ℤ} (hS : l.Pairwise (· ≤ ·)) {start : ℕ} {L : ℤ} :
      (∀ x ∈ gpicks l d start L, start ≤ x ∧ x < l.length) ∧
      (∀ t, t + 1 < (gpicks l d start L).length →
        d ≤ l.getD ((gpicks l d start L).getD (t + 1) 0) 0 -
            l.getD ((gpicks l d start L).getD t 0) 0) :=
    gpicksF_chain hS (l.length - start) start L (le_refl _)

  theorem gpicksF_dom {l : List ℤ} {d : ℤ} (hS : l.Pairwise (· ≤ ·)) :
      ∀ (n start : ℕ) (L : ℤ), l.length - start ≤ n →
      ∀ (m : ℕ) (x : ℕ → ℕ),
        (∀ t < m, start ≤ x t ∧ x t < l.length) →
        (∀ t, t + 1 < m → x t < x (t + 1)) →
        (∀ t, t + 1 < m → d ≤ l.getD (x (t + 1)) 0 - l.getD (x t) 0) →
        (0 < m → d ≤ l.getD (x 0) 0 - L) →
        (m ≤ (gpicksF l d n start L).length ∧
          ∀ t < m, (gpicksF l d n start L).getD t 0 ≤ x t)
    | 0, start, L, hf, m, x, hin, hinc, hgap, hfirst => by
      have hm0 : m = 0 := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exact h
        · exfalso
          have h1 := (hin 0 h).1
          have h2 := (hin 0 h).2
          omega
      subst hm0
      simp [gpicksF]
    | n + 1, start, L, hf, m, x, hin, hinc, hgap, hfirst => by
      by_cases hs : start < l.length
      · by_cases hd : d ≤ l.getD start 0 - L
        · rcases Nat.eq_zero_or_pos m with hm0 | hm
          · subst hm0
            rw [gpicksF_pick hs hd]
            simp
          · have hfirst' : 0 < m - 1 → d ≤ l.getD (x (0 + 1)) 0 - l.getD start 0 := by
              intro hmm
              have hm2 : 1 < m := by omega
              by_cases h0 : x 0 = start
              · have hh := hgap 0 (by omega)
                rw [h0] at hh
                exact hh
              · have h0' : start < x 0 := by have := (hin 0 hm).1; omega
                have hm1 := getD_mono hS (le_of_lt h0') (hin 0 hm).2
                have := hgap 0 (by omega)
                omega
            obtain ⟨ih1, ih2⟩ := gpicksF_dom hS n (start + 1) (l.getD start 0) (by omega)
              (m - 1) (fun t => x (t + 1))
              (fun t ht => by
                have h1 := (hin (t + 1) (by omega)).2
                have h2 := hinc t (by omega)
                have h3 := (hin t (by omega)).1
                omega)
              (fun t ht => hinc (t + 1) (by omega))
              (fun t ht => hgap (t + 1) (by omega))
              hfirst'
            rw [gpicksF_pick hs hd]
            refine ⟨by simp only [List.length_cons]; omega, ?_⟩
            intro t ht
            rcases t with _ | t'
            · simpa using (hin 0 hm).1
            · simpa using ih2 t' (by omega)
        · rcases Nat.eq_zero_or_pos m with hm0 | hm
          · subst hm0
            rw [gpicksF_skip hs hd]
            simp
          · have hx0 : start < x 0 := by
              by_contra hcon
              have h1 := (hin 0 hm).1
              have h2 : x 0 = start := by omega
              rw [h2] at hfirst
              exact hd (hfirst hm)
            have hmono : ∀ t, t < m → x 0 ≤ x t := by
              intro t
              induction t with
              | zero => intro _; exact le_refl _
              | succ k ih =>
                intro hk
                have h1 := hinc k (by omega)
                have h2 := ih (by omega)
                omega
            obtain ⟨ih1, ih2⟩ := gpicksF_dom hS n (start + 1) L (by omega) m x
              (fun t ht => by
                have h1 := (hin t ht).2
                have h2 := hmono t ht
                omega)
              hinc hgap hfirst
            rw [gpicksF_skip hs hd]
            exact ⟨ih1, ih2⟩
      · have hm0 : m = 0 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exact h
          · exfalso
            have h1 := (hin 0 h).1
            have h2 := (hin 0 h).2
            omega
        subst hm0
        rw [gpicksF_stop hs]
        simp

  theorem gpicks_dom {l : List ℤ} {d : ℤ} (hS : l.Pairwise (· ≤ ·)) {start : ℕ} {L : ℤ}
      {m : ℕ} {x : ℕ → ℕ}
      (hin : ∀ t < m, start ≤ x t ∧ x t < l.length)
      (hinc : ∀ t, t + 1 < m → x t < x (t + 1))
      (hgap : ∀ t, t + 1 < m → d ≤ l.getD (x (t + 1)) 0 - l.getD (x t) 0)
      (hfirst : 0 < m → d ≤ l.getD (x 0) 0 - L) :
      m ≤ (gpicks l d start L).length ∧ ∀ t < m, (gpicks l d start L).getD t 0 ≤ x t :=
    gpicksF_dom hS (l.length - start) start L (le_refl _) m x hin hinc hgap hfirst

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    have h : (a - b).natAbs = (b - a).natAbs := by
      rw [show b - a = -(a - b) by omega, Int.natAbs_neg]
    simp only [absDiff, h]

  theorem absDiff_nonneg (a b : ℤ) : 0 ≤ absDiff a b := by
    exact Int.natCast_nonneg _

  theorem absDiff_of_le {a b : ℤ} (h : a ≤ b) : absDiff a b = b - a := by
    have h3 : (0 : ℤ) ≤ -(a - b) := by omega
    have key : ((a - b).natAbs : ℤ) = -(a - b) := by
      rw [← Int.natAbs_neg (a - b), Int.natAbs_of_nonneg h3]
    simp only [absDiff]
    rw [key]
    omega

  /-- A selection of positions all of whose pairwise distances are at least `d`. -/
  def goodSel (l : List ℤ) (d : ℤ) (S : Finset ℕ) : Prop :=
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d ≤ absDiff (l.getD i 0) (l.getD j 0)

  /-! ### Basic facts about `vals` and the slices -/

  theorem vals_length (s : Slice Std.I64) : (vals s).length = s.length := by
    simp [vals]

  theorem vals_getD_eq {s : Slice Std.I64} {i : ℕ} (h : i < s.length) :
      (vals s).getD i 0 = (s.val[i]).val := by
    have h' : i < (vals s).length := by simpa [vals] using h
    rw [List.getD_eq_getElem (vals s) 0 h']
    simp [vals]

  theorem vals_pairwise {s : Slice Std.I64} (h : SortedV s.val) :
      (vals s).Pairwise (· ≤ ·) := by
    have h1 : (s.val.map (fun x : Std.I64 => x.val)).Pairwise (· ≤ ·) :=
      List.Pairwise.map (f := fun x : Std.I64 => x.val)
        (S := fun a b => a ≤ b) (fun a b hab => hab) h
    simpa [vals] using h1

  theorem vals_bounds {s : Slice Std.I64} (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      {i : ℕ} (h : i < s.length) :
      1 ≤ (vals s).getD i 0 ∧ (vals s).getD i 0 ≤ 1000000000 := by
    rw [vals_getD_eq h]
    exact hv _ (List.getElem_mem h)

  theorem gpicks_stop {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ} (h : ¬ start < l.length) :
      gpicks l d start L = [] := by
    have h0 : l.length - start = 0 := by omega
    simp only [gpicks, h0]
    rfl

  /-! ### From WP specifications to equations -/

  theorem spec_eq_ok {β : Type} {x : Result β} {v : β}
      (h : Aeneas.Std.WP.spec x (fun r => r = v)) : x = ok v := by
    cases hx : x.match with
    | ok a =>
      rw [Result.match.isOk] at hx
      subst hx
      simp only [WP.spec_ok] at h
      rw [h]
    | div =>
      rw [Result.match.isDiv] at hx
      subst hx
      simp at h
    | vis e k =>
      rw [Result.match.isVis] at hx
      subst hx
      simp at h

  /-! ### The greedy loop of `can_make` -/

  theorem gpicks_pick_len {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ}
      (h : start < l.length) (hd : d ≤ l.getD start 0 - L) :
      ((gpicks l d start L).length : ℤ)
        = 1 + ((gpicks l d (start + 1) (l.getD start 0)).length : ℤ) := by
    rw [gpicks_pick h hd]
    simp [List.length_cons]
    omega

  theorem can_make_loop_body_spec (s : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (hn : n.val = s.length)
      (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : 0 ≤ d.val) (hlen : s.length ≤ 100000)
      (c L : Std.I64) (i : Std.Usize)
      (hi : i.val ≤ s.length) (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ i.val + 1)
      (hL0 : 0 ≤ L.val) (hL1 : L.val ≤ 1000000000) :
      can_make_loop.body s k d n c L i ⦃ r =>
        (match r with
         | ControlFlow.done b =>
           b = decide (c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ) ≥ k.val)
         | ControlFlow.cont p =>
           p.2.2.val ≤ s.length ∧ p.2.2.val = i.val + 1 ∧
           0 ≤ p.1.val ∧ p.1.val ≤ p.2.2.val + 1 ∧
           0 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000 ∧
           p.1.val + ((gpicks (vals s) d.val p.2.2.val p.2.1.val).length : ℤ)
             = c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ)) ⦄ := by
    unfold can_make_loop.body
    split
    · rename_i hlt
      have hilen : i.val < s.length := by
        have h2 := hlt; rw [UScalar.lt_equiv] at h2; omega
      have hilen' : i.val < (vals s).length := by rw [vals_length]; exact hilen
      apply WP.spec_bind (Slice.index_usize_spec s i hilen)
      intro i1 hi1
      have hi1v : i1.val = (vals s).getD i.val 0 := by
        rw [hi1, vals_getD_eq hilen]
      have hb1 : 1 ≤ i1.val := by rw [hi1v]; exact (vals_bounds hv hilen).1
      have hb2 : i1.val ≤ 1000000000 := by rw [hi1v]; exact (vals_bounds hv hilen).2
      apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := i1) (y := L)
        (by scalar_tac) (by scalar_tac))
      intro i2 hi2
      have hi2v : i2.val = i1.val - L.val := by simpa using hi2
      split
      · rename_i hgele
        have hdge : d.val ≤ (vals s).getD i.val 0 - L.val := by
          have h1 : d.val ≤ i2.val := by simpa using hgele
          rw [hi2v, hi1v] at h1; exact h1
        apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := c) (y := 1#i64)
          (by scalar_tac) (by scalar_tac))
        intro count1 hcount1
        have hcount1v : count1.val = c.val + 1 := by simpa using hcount1
        split
        · rename_i hcke
          simp only [WP.spec_ok]
          have hgk : c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ) ≥ k.val := by
            have h1 : k.val ≤ count1.val := by simpa using hcke
            rw [gpicks_pick_len hilen' hdge]
            omega
          have hz : decide (c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ) ≥ k.val)
              = true := by
            rw [decide_eq_true_iff]
            exact hgk
          rw [hz]
        · rename_i hncke
          apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := i) (y := 1#usize)
            (by scalar_tac))
          intro i3 hi3
          have hi3v : i3.val = i.val + 1 := by simpa using hi3
          simp only [WP.spec_ok]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hi3v]; omega
          · rw [hi3v]
          · rw [hcount1v]; omega
          · rw [hi3v, hcount1v]; omega
          · omega
          · omega
          · rw [hi3v, hcount1v, gpicks_pick_len hilen' hdge, hi1v]
            ring
      · rename_i hgele
        have hdlt : ¬ d.val ≤ (vals s).getD i.val 0 - L.val := by
          intro hh
          apply hgele
          show d.val ≤ i2.val
          rw [hi2v, hi1v]
          exact hh
        apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := i) (y := 1#usize)
          (by scalar_tac))
        intro i3 hi3
        have hi3v : i3.val = i.val + 1 := by simpa using hi3
        simp only [WP.spec_ok]
        refine ⟨?_, ?_, hc0, ?_, hL0, hL1, ?_⟩
        · rw [hi3v]; omega
        · rw [hi3v]
        · rw [hi3v]; omega
        · rw [hi3v, gpicks_skip hilen' hdlt]
    · rename_i hge
      simp only [WP.spec_ok]
      have hilen : s.length ≤ i.val := by
        have h2 := hge; rw [UScalar.lt_equiv] at h2; omega
      have hstop : gpicks (vals s) d.val i.val L.val = [] := by
        apply gpicks_stop
        rw [vals_length]; omega
      simp [hstop]

  theorem can_make_loop_spec (s : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (hn : n.val = s.length)
      (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : 0 ≤ d.val) (hlen : s.length ≤ 100000)
      (c L : Std.I64) (i : Std.Usize)
      (hi : i.val ≤ s.length) (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ i.val + 1)
      (hL0 : 0 ≤ L.val) (hL1 : L.val ≤ 1000000000) :
      can_make_loop s k d n c L i
        = ok (decide (c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ) ≥ k.val)) := by
    let total : ℤ := c.val + ((gpicks (vals s) d.val i.val L.val).length : ℤ)
    have hspec : can_make_loop s k d n c L i ⦃ r => r = decide (total ≥ k.val) ⦄ := by
      unfold can_make_loop
      apply loop.spec_decr_nat
        (fun p : Std.I64 × Std.I64 × Std.Usize => s.length - p.2.2.val)
        (fun p => p.2.2.val ≤ s.length ∧ 0 ≤ p.1.val ∧ p.1.val ≤ p.2.2.val + 1 ∧
          0 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000 ∧
          p.1.val + ((gpicks (vals s) d.val p.2.2.val p.2.1.val).length : ℤ) = total)
        (fun b => b = decide (total ≥ k.val))
        (fun p => can_make_loop.body s k d n p.1 p.2.1 p.2.2) (c, L, i)
        ?_ ⟨hi, hc0, hc1, hL0, hL1, rfl⟩
      rintro ⟨c', L', i'⟩ ⟨hi', hc0', hc1', hL0', hL1', htot⟩
      apply WP.spec_mono
        (can_make_loop_body_spec s k d n hn hv hd hlen c' L' i' hi' hc0' hc1' hL0' hL1')
      intro r hr
      cases r with
      | done b =>
        show b = decide (total ≥ k.val)
        rw [hr, htot]
      | cont p =>
        obtain ⟨pc, pL, pi⟩ := p
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        refine ⟨⟨h1, h3, h4, h5, h6, ?_⟩, ?_⟩
        · rw [h7, htot]
        · have hk : i'.val < s.length := by omega
          show s.length - pi.val < s.length - i'.val
          rw [h2]
          exact Nat.sub_lt_sub_left hk (Nat.lt_succ_self _)
    exact spec_eq_ok hspec

  theorem i64_one_val : ((1#i64 : Std.I64).val : ℤ) = 1 := rfl

  theorem usize_one_val : ((1#usize : Std.Usize).val : ℕ) = 1 := rfl

  theorem can_make_spec (s : Slice Std.I64) (k d : Std.I64)
      (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : 0 ≤ d.val) (hk : 2 ≤ k.val) (hlen : s.length ≤ 100000)
      (h1 : 1 ≤ s.length) :
      can_make s k d
        = ok (decide (1 + ((gpicks (vals s) d.val 1 ((vals s).getD 0 0)).length : ℤ) ≥ k.val)) := by
    have hk1 : ¬ (k ≤ 1#i64) := by
      intro h
      have h' : k.val ≤ (1#i64).val := by simpa using h
      rw [i64_one_val] at h'
      omega
    have hidx : Slice.index_usize s 0#usize = ok (s.val[0]) := by
      apply spec_eq_ok
      have h2 : ((0#usize : Std.Usize).val : ℕ) = 0 := rfl
      simpa [h2] using Slice.index_usize_spec s 0#usize (by omega : (0#usize).val < s.length)
    have hstep : can_make s k d
        = (do let n := Slice.len s
              if k ≤ 1#i64 then ok true
              else (do let last ← Slice.index_usize s 0#usize
                       can_make_loop s k d n 1#i64 last 1#usize)) := rfl
    rw [hstep]
    simp only [hk1, if_false, hidx, bind_ok]
    have h0 : 1 ≤ (vals s).getD 0 0 ∧ (vals s).getD 0 0 ≤ 1000000000 := vals_bounds hv h1
    rw [can_make_loop_spec s k d (Slice.len s) (Slice.len_val s) hv hd hlen
      (1#i64) (s.val[0]) (1#usize) (by rw [usize_one_val]; omega)
      (by rw [i64_one_val]; omega) (by rw [i64_one_val, usize_one_val]; omega)
      (by rw [← vals_getD_eq h1]; omega)
      (by rw [← vals_getD_eq h1]; omega)]
    rw [i64_one_val, usize_one_val, vals_getD_eq h1]

  /-! ### Index maps induced by a list permutation -/

  /-- Index map for a `cons` step: `0 ↦ 0` and `k+1 ↦ σ k + 1`. -/
  private def shiftIdx (σ : ℕ → ℕ) : ℕ → ℕ :=
    fun i => match i with | 0 => 0 | (k + 1) => σ k + 1

  /-- Index map for a `swap` step: exchanges `0` and `1`. -/
  private def swapIdx : ℕ → ℕ :=
    fun i => if i = 0 then 1 else if i = 1 then 0 else i

  private theorem shiftIdx_injective {σ : ℕ → ℕ} (h : Function.Injective σ) :
      Function.Injective (shiftIdx σ) := by
    intro a b hab
    rcases a with _ | k
    · rcases b with _ | m
      · rfl
      · exact absurd (show σ m + 1 = 0 from hab.symm) (Nat.succ_ne_zero (σ m))
    · rcases b with _ | m
      · exact absurd (show σ k + 1 = 0 from hab) (Nat.succ_ne_zero (σ k))
      · exact congrArg Nat.succ (h (Nat.succ.inj (show σ k + 1 = σ m + 1 from hab)))

  private theorem swapIdx_invol (i : ℕ) : swapIdx (swapIdx i) = i := by
    rcases i with _ | _ | k <;> simp [swapIdx]

  private theorem swapIdx_injective : Function.Injective swapIdx := by
    intro a b hab
    have h1 : swapIdx (swapIdx a) = swapIdx (swapIdx b) := by rw [hab]
    rwa [swapIdx_invol, swapIdx_invol] at h1

  /-- A strong form of `perm_exists_map`: the index map is globally injective. -/
  private theorem perm_exists_map_aux {l₁ l₂ : List ℤ} (h : l₁.Perm l₂) :
      ∃ σ : ℕ → ℕ, Function.Injective σ ∧
        (∀ i, i < l₁.length → σ i < l₂.length ∧ l₂.getD (σ i) 0 = l₁.getD i 0) :=
    List.Perm.rec
      (motive := fun a b _ => ∃ σ : ℕ → ℕ, Function.Injective σ ∧
        (∀ i, i < a.length → σ i < b.length ∧ b.getD (σ i) 0 = a.getD i 0))
      (by exact ⟨id, fun _ _ hh => hh, fun i hi => by simp at hi⟩)
      (fun x {l₁ l₂} _ ih => by
        obtain ⟨σ, hinj, hσ⟩ := ih
        refine ⟨shiftIdx σ, shiftIdx_injective hinj, ?_⟩
        intro i hi
        rcases i with _ | k
        · refine ⟨?_, ?_⟩
          · show shiftIdx σ 0 < (x :: l₂).length
            simp [shiftIdx]
          · show (x :: l₂).getD (shiftIdx σ 0) 0 = (x :: l₁).getD 0 0
            simp [shiftIdx]
        · have hk : k < l₁.length := by
            simp only [List.length_cons] at hi
            omega
          obtain ⟨hlt, heq⟩ := hσ k hk
          refine ⟨?_, ?_⟩
          · show shiftIdx σ (k + 1) < (x :: l₂).length
            rw [show shiftIdx σ (k + 1) = σ k + 1 by simp [shiftIdx]]
            simp only [List.length_cons]
            omega
          · show (x :: l₂).getD (shiftIdx σ (k + 1)) 0 = (x :: l₁).getD (k + 1) 0
            rw [show shiftIdx σ (k + 1) = σ k + 1 by simp [shiftIdx]]
            rw [List.getD_cons_succ, List.getD_cons_succ]
            exact heq)
      (fun x y l => by
        refine ⟨swapIdx, swapIdx_injective, ?_⟩
        intro i hi
        rcases i with _ | _ | k
        · refine ⟨?_, ?_⟩
          · show swapIdx 0 < (x :: y :: l).length
            simp [swapIdx]
          · show (x :: y :: l).getD (swapIdx 0) 0 = (y :: x :: l).getD 0 0
            simp [swapIdx]
        · refine ⟨?_, ?_⟩
          · show swapIdx 1 < (x :: y :: l).length
            simp [swapIdx]
          · show (x :: y :: l).getD (swapIdx 1) 0 = (y :: x :: l).getD 1 0
            simp [swapIdx]
        · have hk : k + 2 < (y :: x :: l).length := hi
          have hval : swapIdx (k + 2) = k + 2 := by simp [swapIdx]
          refine ⟨?_, ?_⟩
          · show swapIdx (k + 2) < (x :: y :: l).length
            rw [hval]
            simp only [List.length_cons] at hk ⊢
            omega
          · show (x :: y :: l).getD (swapIdx (k + 2)) 0 = (y :: x :: l).getD (k + 2) 0
            rw [hval]
            simp only [List.getD_cons_succ])
      (fun {l₁ l₂ l₃} _ _ ih1 ih2 => by
        obtain ⟨σ1, hinj1, hσ1⟩ := ih1
        obtain ⟨σ2, hinj2, hσ2⟩ := ih2
        refine ⟨fun i => σ2 (σ1 i), fun a b hab => hinj1 (hinj2 hab), ?_⟩
        intro i hi
        obtain ⟨hlt, heq⟩ := hσ1 i hi
        obtain ⟨hlt2, heq2⟩ := hσ2 (σ1 i) hlt
        exact ⟨hlt2, by rw [heq2, heq]⟩)
      h

  theorem perm_exists_map {l₁ l₂ : List ℤ} (h : l₁.Perm l₂) :
      ∃ σ : ℕ → ℕ,
        (∀ i, i < l₁.length → σ i < l₂.length ∧ l₂.getD (σ i) 0 = l₁.getD i 0) ∧
        (∀ i j, i < l₁.length → j < l₁.length → i ≠ j → σ i ≠ σ j) := by
    obtain ⟨σ, hinj, hσ⟩ := perm_exists_map_aux h
    exact ⟨σ, hσ, fun i j _ _ hij hcon => hij (hinj hcon)⟩

  theorem perm_good_sel {l₁ l₂ : List ℤ} (h : l₁.Perm l₂) (d : ℤ) (S₁ : Finset ℕ)
      (hS₁ : S₁ ⊆ Finset.range l₁.length) :
      ∃ S₂, S₂ ⊆ Finset.range l₂.length ∧ S₂.card = S₁.card ∧
        (goodSel l₂ d S₂ ↔ goodSel l₁ d S₁) := by
    obtain ⟨σ, hσ, hinj⟩ := perm_exists_map h
    have hlt : ∀ i ∈ S₁, i < l₁.length := fun i hi => Finset.mem_range.mp (hS₁ hi)
    refine ⟨S₁.image σ, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hσ i (hlt i hi)).1
    · refine Finset.card_image_of_injOn ?_
      intro a ha b hb hab
      by_contra hne
      exact hinj a b (hlt a ha) (hlt b hb) hne hab
    · constructor
      · intro h₂ i hi j hj hij
        have hi' : σ i ∈ S₁.image σ := Finset.mem_image.mpr ⟨i, hi, rfl⟩
        have hj' : σ j ∈ S₁.image σ := Finset.mem_image.mpr ⟨j, hj, rfl⟩
        have hne : σ i ≠ σ j := hinj i j (hlt i hi) (hlt j hj) hij
        have hh := h₂ (σ i) hi' (σ j) hj' hne
        simpa only [(hσ i (hlt i hi)).2, (hσ j (hlt j hj)).2] using hh
      · intro h₁ i hi j hj hij
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
        have hne : a ≠ b := by
          rintro rfl
          exact hij rfl
        have hh := h₁ a ha b hb hne
        simpa only [(hσ a (hlt a ha)).2, (hσ b (hlt b hb)).2] using hh

  /-! ### Chains and selections -/

  theorem gpicksF_incr {l : List ℤ} {d : ℤ} :
      ∀ (n start : ℕ) (L : ℤ), l.length - start ≤ n →
      ∀ t, t + 1 < (gpicksF l d n start L).length →
        (gpicksF l d n start L).getD t 0 < (gpicksF l d n start L).getD (t + 1) 0
    | 0, start, L, h, t, ht => by simp [gpicksF] at ht
    | n + 1, start, L, h, t, ht => by
      by_cases hs : start < l.length
      · by_cases hd : d ≤ l.getD start 0 - L
        · have hb := gpicksF_bounds (l := l) (d := d) n (start + 1) (l.getD start 0) (by omega)
          rw [gpicksF_pick hs hd] at ht ⊢
          cases t with
          | zero =>
            have h1 : 0 < (gpicksF l d n (start + 1) (l.getD start 0)).length := by
              simpa using ht
            have hmem : (gpicksF l d n (start + 1) (l.getD start 0)).getD 0 0
                ∈ gpicksF l d n (start + 1) (l.getD start 0) := by
              rw [List.getD_eq_getElem _ _ h1]
              exact List.getElem_mem h1
            have h2 := hb _ hmem
            simpa using h2.1
          | succ t' =>
            exact gpicksF_incr (l := l) (d := d) n (start + 1) (l.getD start 0) (by omega) t'
              (by simpa using ht)
        · rw [gpicksF_skip hs hd] at ht ⊢
          exact gpicksF_incr (l := l) (d := d) n (start + 1) L (by omega) t ht
      · rw [gpicksF_stop hs] at ht
        simp at ht

  theorem gpicks_incr {l : List ℤ} {d : ℤ} {start : ℕ} {L : ℤ} :
      ∀ t, t + 1 < (gpicks l d start L).length →
        (gpicks l d start L).getD t 0 < (gpicks l d start L).getD (t + 1) 0 :=
    gpicksF_incr (l.length - start) start L (le_refl _)

  /-- A strictly increasing-by-one list of indices is strictly increasing. -/
  theorem getD_lt_of_lt {W : List ℕ}
      (hinc : ∀ t, t + 1 < W.length → W.getD t 0 < W.getD (t + 1) 0) :
      ∀ a b, b < W.length → a < b → W.getD a 0 < W.getD b 0 := by
    intro a b hb hab
    have hmono : ∀ n, a + 1 ≤ n → n < W.length → W.getD (a + 1) 0 ≤ W.getD n 0 := by
      intro n han
      refine Nat.le_induction
        (motive := fun n _ => n < W.length → W.getD (a + 1) 0 ≤ W.getD n 0)
        (fun _ => le_refl _) ?_ n han
      intro m _ ih hm1
      exact le_trans (ih (by omega)) (le_of_lt (hinc m hm1))
    have h1 : W.getD a 0 < W.getD (a + 1) 0 := hinc a (by omega)
    exact lt_of_lt_of_le h1 (hmono b (by omega) hb)

  /-- Telescoping of consecutive gaps. -/
  theorem telescoping {l : List ℤ} {d : ℤ} {W : List ℕ}
      (hgap : ∀ t, t + 1 < W.length → d ≤ l.getD (W.getD (t + 1) 0) 0 - l.getD (W.getD t 0) 0) :
      ∀ a b, b < W.length → a ≤ b →
        ((b - a : ℕ) : ℤ) * d ≤ l.getD (W.getD b 0) 0 - l.getD (W.getD a 0) 0 := by
    intro a b hb hab
    revert hb
    refine Nat.le_induction (motive := fun n _ => n < W.length →
      ((n - a : ℕ) : ℤ) * d ≤ l.getD (W.getD n 0) 0 - l.getD (W.getD a 0) 0)
      ?_ ?_ b hab
    · intro _
      simp
    · intro n _ ih hn1
      have h1 : ((n + 1 - a : ℕ) : ℤ) = ((n - a : ℕ) : ℤ) + 1 := by
        have h : n + 1 - a = (n - a) + 1 := by omega
        rw [h, Nat.cast_add, Nat.cast_one]
      rw [h1, add_mul, one_mul]
      have h2 := ih (by omega)
      have h3 := hgap n hn1
      omega

  /-- A list-chain of indices (whose consecutive values are at distance `≥ d` under `l`)
  yields a `goodSel` Finset witness of any size up to its length. -/
  theorem chain_list_to_goodSel {l : List ℤ} {d : ℤ} (hl : l.Pairwise (· ≤ ·)) (hd : 0 ≤ d)
      {W : List ℕ} (hinc : ∀ t, t + 1 < W.length → W.getD t 0 < W.getD (t + 1) 0)
      (hbound : ∀ x ∈ W, x < l.length)
      (hgap : ∀ t, t + 1 < W.length → d ≤ l.getD (W.getD (t + 1) 0) 0 - l.getD (W.getD t 0) 0)
      {c : ℕ} (hc : c ≤ W.length) :
      ∃ S : Finset ℕ, S ⊆ Finset.range l.length ∧ S.card = c ∧ goodSel l d S := by
    have hWpair : W.Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have h := getD_lt_of_lt hinc i j hj hij
      rwa [List.getD_eq_getElem W 0 hi, List.getD_eq_getElem W 0 hj] at h
    have htnodup : (W.take c).Nodup :=
      (hWpair.take (i := c)).imp (fun {a b} h => ne_of_lt h)
    have key : ∀ k m : ℕ, k < m → m < W.length →
        d ≤ absDiff (l.getD (W.getD k 0) 0) (l.getD (W.getD m 0) 0) := by
      intro k m hkm hm
      have hklt : W.getD k 0 < W.getD m 0 := getD_lt_of_lt hinc k m hm hkm
      have hml : W.getD m 0 < l.length := by
        rw [List.getD_eq_getElem W 0 hm]
        exact hbound _ (List.getElem_mem hm)
      have hle : l.getD (W.getD k 0) 0 ≤ l.getD (W.getD m 0) 0 :=
        getD_mono hl (le_of_lt hklt) hml
      have htel := telescoping hgap k m hm (le_of_lt hkm)
      have hge1 : d ≤ ((m - k : ℕ) : ℤ) * d := by
        have h1 : (1 : ℤ) ≤ ((m - k : ℕ) : ℤ) := by
          have h2 : 1 ≤ m - k := Nat.one_le_iff_ne_zero.mpr (by omega)
          exact_mod_cast h2
        calc d = 1 * d := (one_mul d).symm
          _ ≤ ((m - k : ℕ) : ℤ) * d := mul_le_mul_of_nonneg_right h1 hd
      rw [absDiff_of_le hle]
      exact le_trans hge1 htel
    refine ⟨(W.take c).toFinset, ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_range]
      exact hbound x (List.mem_of_mem_take hx)
    · rw [List.toFinset_card_of_nodup htnodup, List.length_take, Nat.min_eq_left hc]
    · intro i hi j hj hij
      rw [List.mem_toFinset] at hi hj
      obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hi)
      obtain ⟨m, hm, hmx⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hj)
      have hkm : k ≠ m := by
        intro h
        subst h
        exact hij (by rw [← hkx, ← hmx])
      rw [← hkx, ← hmx, ← List.getD_eq_getElem W 0 hk, ← List.getD_eq_getElem W 0 hm]
      rcases lt_or_gt_of_ne hkm with h | h
      · exact key k m h hm
      · rw [absDiff_comm]
        exact key m k h hk

  /-- A `goodSel` Finset with indices in range yields a strictly increasing index function
  whose consecutive gaps are at least `d`. -/
  theorem goodSel_to_chain {l : List ℤ} (hl : l.Pairwise (· ≤ ·)) {d : ℤ} {S : Finset ℕ}
      (hsub : S ⊆ Finset.range l.length) (hsel : goodSel l d S) :
      ∃ x : ℕ → ℕ, (∀ t < S.card, x t ∈ S) ∧ (∀ t < S.card, x t < l.length) ∧
        (∀ t, t + 1 < S.card → x t < x (t + 1)) ∧
        (∀ t, t + 1 < S.card → d ≤ l.getD (x (t + 1)) 0 - l.getD (x t) 0) := by
    classical
    let x : ℕ → ℕ := fun t =>
      if h : t < S.card then (((Finset.orderIsoOfFin S rfl) ⟨t, h⟩ : S) : ℕ) else 0
    have hxval : ∀ t (h : t < S.card),
        x t = (((Finset.orderIsoOfFin S rfl) ⟨t, h⟩ : S) : ℕ) := by
      intro t h
      simp only [x, dite_eq_left h]
    have hxmem : ∀ t (h : t < S.card), x t ∈ S := by
      intro t h
      rw [hxval t h]
      exact (Finset.orderIsoOfFin S rfl ⟨t, h⟩).2
    have hxlt : ∀ t (h : t < S.card), x t < l.length := by
      intro t h
      have h1 : x t ∈ Finset.range l.length := hsub (hxmem t h)
      rwa [Finset.mem_range] at h1
    have hxmono : ∀ t, t + 1 < S.card → x t < x (t + 1) := by
      intro t ht
      have h1 : t < S.card := by omega
      rw [hxval t h1, hxval (t + 1) ht]
      exact (Finset.orderIsoOfFin S rfl).strictMono
        (show (⟨t, h1⟩ : Fin S.card) < ⟨t + 1, ht⟩ by simp)
    refine ⟨x, hxmem, hxlt, hxmono, ?_⟩
    intro t ht
    have h1 : t < S.card := by omega
    have hne : x t ≠ x (t + 1) := ne_of_lt (hxmono t ht)
    have hle : l.getD (x t) 0 ≤ l.getD (x (t + 1)) 0 :=
      getD_mono hl (le_of_lt (hxmono t ht)) (hxlt (t + 1) ht)
    have hsd := hsel (x t) (hxmem t h1) (x (t + 1)) (hxmem (t + 1) ht) hne
    rwa [absDiff_of_le hle] at hsd

  /-- If all pairwise distances on `S` are at least `d` and one pair attains `d`, then the
  tastiness of `S` is exactly `d`. -/
  theorem tastinessOn_eq {l : List ℤ} {S : Finset ℕ} {d : ℤ} (hne : 2 ≤ S.card)
      (hge : ∀ i ∈ S, ∀ j ∈ S, i < j → d ≤ absDiff (l.getD i 0) (l.getD j 0))
      (hex : ∃ i ∈ S, ∃ j ∈ S, i < j ∧ absDiff (l.getD i 0) (l.getD j 0) ≤ d) :
      tastinessOn l S = d := by
    classical
    have hmem : ∀ i j : ℕ, i ∈ S → j ∈ S → i < j →
        absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := by
      intro i j hi hj hij
      rw [pairDistsOn, Finset.mem_image]
      exact ⟨(i, j), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hij⟩, rfl⟩
    have hne' : (pairDistsOn l S).Nonempty := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨_, hmem a b ha hb h⟩
      · exact ⟨_, hmem b a hb ha h⟩
    rw [tastinessOn, dite_eq_left hne']
    refine le_antisymm ?_ ?_
    · obtain ⟨i, hi, j, hj, hij, hex'⟩ := hex
      exact le_trans (Finset.min'_le _ _ (hmem i j hi hj hij)) hex'
    · rw [Finset.le_min'_iff]
      intro y hy
      rw [pairDistsOn, Finset.mem_image] at hy
      obtain ⟨⟨i, j⟩, hp, rfl⟩ := hy
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hp1a, hp1b⟩ := Finset.mem_product.mp hp1
      exact hge i hp1a j hp1b hp2

  /-- The greedy count reaches `k` only if there is a `k`-element selection with all
  pairwise distances at least `d`. -/
  theorem gtastiness_sound {l : List ℤ} {d : ℤ} {k : ℕ}
      (hl : l.Pairwise (· ≤ ·)) (hd : 0 ≤ d) (hpos : 0 < l.length)
      (h : 1 + ((gpicks l d 1 (l.getD 0 0)).length : ℤ) ≥ (k : ℤ)) :
      ∃ S : Finset ℕ, S ⊆ Finset.range l.length ∧ S.card = k ∧ goodSel l d S := by
    have hd0 : d ≤ l.getD 0 0 - (l.getD 0 0 - d - 1) := by omega
    have hW : ((gpicks l d 0 (l.getD 0 0 - d - 1)).length : ℤ)
        = 1 + ((gpicks l d 1 (l.getD 0 0)).length : ℤ) :=
      gpicks_pick_len hpos hd0
    have hc : k ≤ (gpicks l d 0 (l.getD 0 0 - d - 1)).length := by
      have h1 : (k : ℤ) ≤ ((gpicks l d 0 (l.getD 0 0 - d - 1)).length : ℤ) := by
        rw [hW]; omega
      omega
    refine chain_list_to_goodSel (W := gpicks l d 0 (l.getD 0 0 - d - 1)) hl hd
      (gpicks_incr (start := 0)) (fun x hx => (gpicks_bounds (start := 0) x hx).2) ?_ hc
    exact (gpicks_chain hl (start := 0) (L := l.getD 0 0 - d - 1)).2

  /-- Any `k`-element selection with all pairwise distances at least `d` forces the greedy
  count to reach `k`. -/
  theorem gtastiness_complete {l : List ℤ} {d : ℤ} {k : ℕ}
      (hl : l.Pairwise (· ≤ ·)) (hd : 0 ≤ d) (hpos : 0 < l.length)
      {S : Finset ℕ} (hsub : S ⊆ Finset.range l.length) (hcard : S.card = k)
      (hsel : goodSel l d S) :
      1 + ((gpicks l d 1 (l.getD 0 0)).length : ℤ) ≥ (k : ℤ) := by
    have hL : d ≤ l.getD 0 0 - (l.getD 0 0 - d - 1) := by omega
    have hW : ((gpicks l d 0 (l.getD 0 0 - d - 1)).length : ℤ)
        = 1 + ((gpicks l d 1 (l.getD 0 0)).length : ℤ) :=
      gpicks_pick_len hpos hL
    obtain ⟨x, hxmem, hxlt, hxinc, hxgap⟩ := goodSel_to_chain hl hsub hsel
    have hdom := gpicks_dom hl (start := 0) (L := l.getD 0 0 - d - 1) (m := k) (x := x)
      (fun t ht => ⟨Nat.zero_le _, hxlt t (by omega)⟩)
      (fun t ht => hxinc t (by omega))
      (fun t ht => hxgap t (by omega))
      (fun hm => by
        have h1 : l.getD 0 0 ≤ l.getD (x 0) 0 :=
          getD_mono hl (Nat.zero_le _) (hxlt 0 (by omega))
        omega)
    have h1 : (k : ℤ) ≤ ((gpicks l d 0 (l.getD 0 0 - d - 1)).length : ℤ) := by
      have := hdom.1
      omega
    rw [hW] at h1
    exact h1

  /-- Pairwise distances in a sorted list are bounded by the spread of the list. -/
  theorem absDiff_le_spread {l : List ℤ} (hl : l.Pairwise (· ≤ ·)) (hpos : 0 < l.length)
      {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
      absDiff (l.getD i 0) (l.getD j 0) ≤ l.getD (l.length - 1) 0 - l.getD 0 0 := by
    have hlast : l.length - 1 < l.length := by omega
    have h0i : l.getD 0 0 ≤ l.getD i 0 := getD_mono hl (Nat.zero_le _) hi
    have h0j : l.getD 0 0 ≤ l.getD j 0 := getD_mono hl (Nat.zero_le _) hj
    have hil : l.getD i 0 ≤ l.getD (l.length - 1) 0 := getD_mono hl (by omega) hlast
    have hjl : l.getD j 0 ≤ l.getD (l.length - 1) 0 := getD_mono hl (by omega) hlast
    rcases le_total i j with h | h
    · rw [absDiff_of_le (getD_mono hl h hj)]
      omega
    · rw [absDiff_comm, absDiff_of_le (getD_mono hl h hi)]
      omega

  theorem can_make_true_goodSel (s : Slice Std.I64) (k d : Std.I64)
      (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hSv : SortedV s.val)
      (hd : 0 ≤ d.val) (hk : 2 ≤ k.val) (hlen : s.length ≤ 100000)
      (h1 : 1 ≤ s.length) (hb : can_make s k d = ok true) :
      ∃ S : Finset ℕ, S ⊆ Finset.range s.length ∧ S.card = k.val.toNat ∧ goodSel (vals s) d.val S := by
    have hspec := can_make_spec s k d hv hd hk hlen h1
    rw [hb] at hspec
    have h3 : decide (1 + ((gpicks (vals s) d.val 1 ((vals s).getD 0 0)).length : ℤ) ≥ k.val)
        = true := by
      rw [Result.ok.injEq] at hspec
      exact hspec.symm
    have hP : 1 + ((gpicks (vals s) d.val 1 ((vals s).getD 0 0)).length : ℤ) ≥ k.val :=
      of_decide_eq_true h3
    have hknn : ((k.val.toNat : ℤ)) = k.val := Int.toNat_of_nonneg (by omega)
    obtain ⟨S, hsub, hcard, hsel⟩ :=
      gtastiness_sound (l := vals s) (d := d.val) (k := k.val.toNat)
        (vals_pairwise hSv) hd (by rw [vals_length]; omega)
        (by rw [hknn]; exact hP)
    refine ⟨S, ?_, hcard, hsel⟩
    rwa [vals_length] at hsub

  theorem can_make_false_no_goodSel (s : Slice Std.I64) (k d : Std.I64)
      (hv : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hSv : SortedV s.val)
      (hd : 0 ≤ d.val) (hk : 2 ≤ k.val) (hlen : s.length ≤ 100000)
      (h1 : 1 ≤ s.length) (hb : can_make s k d = ok false) :
      ¬ ∃ S : Finset ℕ, S ⊆ Finset.range s.length ∧ S.card = k.val.toNat ∧
          goodSel (vals s) d.val S := by
    rintro ⟨S, hsub, hcard, hsel⟩
    have hspec := can_make_spec s k d hv hd hk hlen h1
    have hknn : ((k.val.toNat : ℤ)) = k.val := Int.toNat_of_nonneg (by omega)
    have hge := gtastiness_complete (l := vals s) (d := d.val) (k := k.val.toNat)
      (vals_pairwise hSv) hd (by rw [vals_length]; omega) (by rwa [vals_length]) hcard hsel
    rw [hknn] at hge
    have hP : decide (1 + ((gpicks (vals s) d.val 1 ((vals s).getD 0 0)).length : ℤ) ≥ k.val)
        = true := by
      rw [decide_eq_true_iff]
      exact hge
    rw [hP] at hspec
    rw [hb] at hspec
    simp at hspec

  /-! ### The binary search loop -/

  theorem loop1_init_yes (sv : Slice Std.I64) (k : Std.I64)
      (hk0 : 0 ≤ k.val) (hklen : k.val ≤ (sv.length : ℤ)) :
      ∃ S : Finset ℕ, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
        goodSel (vals sv) 0 S := by
    have hkn : k.val.toNat ≤ sv.length := by
      have h1 : ((k.val.toNat : ℕ) : ℤ) = k.val := Int.toNat_of_nonneg hk0
      omega
    refine ⟨Finset.range k.val.toNat, ?_, Finset.card_range _, ?_⟩
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro i hi j hj hij
      exact absDiff_nonneg _ _

  theorem loop1_init_no (sv : Slice Std.I64) (k : Std.I64) (hS : SortedV sv.val)
      (hpos : 0 < sv.length) (hk2 : 2 ≤ k.val)
      (hi : Std.I64)
      (hhi : hi.val = (vals sv).getD (sv.length - 1) 0 - (vals sv).getD 0 0 + 1) :
      ¬ ∃ S : Finset ℕ, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
          goodSel (vals sv) hi.val S := by
    rintro ⟨S, hsub, hcard, hsel⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have halt : a < sv.length := Finset.mem_range.mp (hsub ha)
    have hblt : b < sv.length := Finset.mem_range.mp (hsub hb)
    have hspread := absDiff_le_spread (vals_pairwise hS) (by rw [vals_length]; exact hpos)
      (i := a) (j := b) (by rw [vals_length]; exact halt) (by rw [vals_length]; exact hblt)
    rw [vals_length] at hspread
    rcases lt_or_gt_of_ne hab with h | h
    · have := hsel a ha b hb hab
      omega
    · have := hsel b hb a ha (ne_of_lt h)
      rw [absDiff_comm] at this
      omega

  theorem loop1_body_spec (sv : Slice Std.I64) (sorted : alloc.vec.Vec Std.I64) (k : Std.I64)
      (hsv : alloc.vec.Vec.deref sorted = sv)
      (hv : ∀ x ∈ sv.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hS : SortedV sv.val) (hpos : 0 < sv.length) (hlen : sv.length ≤ 100000)
      (hk : 2 ≤ k.val)
      (lo hi : Std.I64) (hlo0 : 0 ≤ lo.val) (hlohi : lo.val < hi.val)
      (hhib : hi.val ≤ 1000000001)
      (hyes : ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
        goodSel (vals sv) lo.val S)
      (hno : ¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
        goodSel (vals sv) hi.val S) :
      maximum_tastiness_loop1.body k sorted lo hi ⦃ r =>
        (match r with
         | ControlFlow.done x =>
           0 ≤ x.val ∧ (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
             goodSel (vals sv) x.val S) ∧
           (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
             goodSel (vals sv) (x.val + 1) S)
         | ControlFlow.cont p =>
           0 ≤ p.1.val ∧ lo.val ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ hi.val ∧
           (lo.val < p.1.val ∨ p.2.val < hi.val) ∧
           (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
             goodSel (vals sv) p.1.val S) ∧
           (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
             goodSel (vals sv) p.2.val S)) ⦄ := by
    unfold maximum_tastiness_loop1.body
    apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := lo) (y := 1#i64)
      (by scalar_tac) (by scalar_tac))
    intro i hi1
    have hi1v : i.val = lo.val + 1 := by
      have h := hi1; rw [i64_one_val] at h; simpa using h
    split
    · rename_i hlt
      have hilthi : i.val < hi.val := by simpa using hlt
      apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := hi) (y := lo)
        (by scalar_tac) (by scalar_tac))
      intro i1' hi2
      have hi2v : i1'.val = hi.val - lo.val := by simpa using hi2
      have hge2 : 2 ≤ i1'.val := by rw [hi2v]; omega
      apply WP.spec_bind (I64.div_spec (x := i1') (y := 2#i64) (by decide) (by
        intro hcon
        have h2 : (2#i64).val = 2 := rfl
        have := hcon.2
        rw [h2] at this
        omega))
      intro i2 hi3
      have hi3v : i2.val = Int.tdiv i1'.val 2 := by simpa using hi3
      have hdiv1 : 1 ≤ i2.val := by
        rw [hi3v, Int.tdiv_eq_ediv_of_nonneg (by omega)]
        rw [Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ) < 2)]
        omega
      have hdiv2 : i2.val < hi.val - lo.val := by
        rw [hi3v, Int.tdiv_eq_ediv_of_nonneg (by omega), hi2v]
        rw [Int.ediv_lt_iff_lt_mul (by norm_num : (0:ℤ) < 2)]
        omega
      apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := lo) (y := i2)
        (by scalar_tac) (by scalar_tac))
      intro mid hi4
      have hi4v : mid.val = lo.val + i2.val := by simpa using hi4
      have hmid0 : 0 ≤ mid.val := by rw [hi4v]; omega
      have hmid1 : lo.val < mid.val := by rw [hi4v]; omega
      have hmid2 : mid.val < hi.val := by rw [hi4v]; omega
      have hmid3 : mid.val ≤ 1000000001 := by omega
      rw [hsv]
      dsimp only
      rw [can_make_spec sv k mid hv hmid0 hk hlen (by omega)]
      simp only [bind_ok]
      split
      · rename_i hbtr
        simp only [WP.spec_ok]
        have hcan : can_make sv k mid = ok true := by
          rw [can_make_spec sv k mid hv hmid0 hk hlen (by omega), hbtr]
        obtain ⟨S, hsub, hcard, hsel⟩ :=
          can_make_true_goodSel sv k mid hv hS hmid0 hk hlen (by omega) hcan
        exact ⟨hmid0, le_of_lt hmid1, hmid2, le_refl _, Or.inl hmid1,
          ⟨S, hsub, hcard, hsel⟩, hno⟩
      · rename_i hbtr
        simp only [WP.spec_ok]
        have hdf : decide (1 + ((gpicks (vals sv) mid.val 1 ((vals sv).getD 0 0)).length : ℤ)
            ≥ k.val) = false := by
          cases h : decide (1 + ((gpicks (vals sv) mid.val 1 ((vals sv).getD 0 0)).length : ℤ)
            ≥ k.val) with
          | false => rfl
          | true => exact absurd h hbtr
        have hcan : can_make sv k mid = ok false := by
          rw [can_make_spec sv k mid hv hmid0 hk hlen (by omega), hdf]
        have hno' := can_make_false_no_goodSel sv k mid hv hS hmid0 hk hlen (by omega) hcan
        exact ⟨hlo0, le_refl _, hmid1, le_of_lt hmid2, Or.inr hmid2, hyes, hno'⟩
    · rename_i hge
      simp only [WP.spec_ok]
      have hle : hi.val ≤ lo.val + 1 := by
        have h := hge
        rw [IScalar.lt_equiv] at h
        omega
      refine ⟨hlo0, hyes, ?_⟩
      rintro ⟨S, hsub, hcard, hsel⟩
      exact hno ⟨S, hsub, hcard, fun a ha b hb hne => by
        have h1 := hsel a ha b hb hne
        omega⟩

  theorem spec_exists_ok {β : Type} {x : Result β} {P : β → Prop}
      (h : Aeneas.Std.WP.spec x P) : ∃ v, x = ok v ∧ P v := by
    cases hx : x.match with
    | ok a =>
      rw [Result.match.isOk] at hx
      subst hx
      exact ⟨a, rfl, by simpa using h⟩
    | div =>
      rw [Result.match.isDiv] at hx
      subst hx
      simp at h
    | vis e k =>
      rw [Result.match.isVis] at hx
      subst hx
      simp at h

  theorem loop1_spec (sv : Slice Std.I64) (sorted : alloc.vec.Vec Std.I64) (k : Std.I64)
      (hsv : alloc.vec.Vec.deref sorted = sv)
      (hv : ∀ x ∈ sv.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hS : SortedV sv.val) (hpos : 0 < sv.length) (hlen : sv.length ≤ 100000)
      (hk : 2 ≤ k.val) (hklen : k.val ≤ (sv.length : ℤ))
      (hi : Std.I64)
      (hhib : hi.val = (vals sv).getD (sv.length - 1) 0 - (vals sv).getD 0 0 + 1) :
      ∃ lo, maximum_tastiness_loop1 k sorted 0#i64 hi = ok lo ∧ 0 ≤ lo.val ∧
        (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧ goodSel (vals sv) lo.val S) ∧
        (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
          goodSel (vals sv) (lo.val + 1) S) := by
    have hhile : hi.val ≤ 1000000001 := by
      have h1 := (vals_bounds hv (i := sv.length - 1) (by omega)).2
      have h2 := (vals_bounds hv (i := 0) (by omega)).1
      omega
    have hspec : maximum_tastiness_loop1 k sorted 0#i64 hi ⦃ lo =>
        0 ≤ lo.val ∧
        (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧ goodSel (vals sv) lo.val S) ∧
        (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
          goodSel (vals sv) (lo.val + 1) S) ⦄ := by
      unfold maximum_tastiness_loop1
      apply loop.spec_decr_nat (fun p : Std.I64 × Std.I64 => (p.2.val - p.1.val).toNat)
        (fun p => 0 ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ hi.val ∧
          (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
            goodSel (vals sv) p.1.val S) ∧
          (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
            goodSel (vals sv) p.2.val S))
        _ (fun p => maximum_tastiness_loop1.body k sorted p.1 p.2) (0#i64, hi) ?_ ?_
      · rintro ⟨lo', hi'⟩ ⟨h0, h1, h2, h3, h4⟩
        dsimp only at h0 h1 h2 h3 h4 ⊢
        apply WP.spec_mono
          (loop1_body_spec sv sorted k hsv hv hS hpos hlen hk lo' hi' h0 h1 (by omega) h3 h4)
        intro r hr
        cases r with
        | done x =>
          obtain ⟨b1, b2, b3⟩ := hr
          exact ⟨b1, b2, b3⟩
        | cont p =>
          obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hr
          refine ⟨⟨b1, b3, le_trans b4 h2, b6, b7⟩, ?_⟩
          have hmeas : (p.2.val - p.1.val).toNat < (hi'.val - lo'.val).toNat := by
            rcases b5 with h5 | h5
            · have h6 : p.2.val - p.1.val < hi'.val - lo'.val := by omega
              omega
            · have h6 : p.2.val - p.1.val < hi'.val - lo'.val := by omega
              omega
          simpa using hmeas
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show (0 : ℤ) ≤ (0#i64).val
          rw [show (0#i64 : Std.I64).val = 0 from rfl]
        · show (0#i64).val < hi.val
          rw [show (0#i64 : Std.I64).val = 0 from rfl]
          have hmono : (vals sv).getD 0 0 ≤ (vals sv).getD (sv.length - 1) 0 :=
            getD_mono (vals_pairwise hS) (by omega) (by rw [vals_length]; omega)
          omega
        · exact le_refl _
        · exact loop1_init_yes sv k (by omega) hklen
        · exact loop1_init_no sv k hS hpos hk hi hhib
    obtain ⟨lo, heq, h0, h1, h2⟩ := spec_exists_ok hspec
    exact ⟨lo, heq, h0, h1, h2⟩

  /-! ### Building the copy of the array which gets sorted -/

  theorem loop0_body_spec (price : Slice Std.I64) (n : Std.Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hn : n.val = price.length) (hi : i.val ≤ n.val)
      (hinv : sorted.val = price.val.take i.val) :
      maximum_tastiness_loop0.body price n sorted i ⦃ r =>
        (match r with
         | ControlFlow.done v => v.val = price.val
         | ControlFlow.cont p => p.1.val = price.val.take p.2.val ∧ p.2.val ≤ n.val ∧
             n.val - p.2.val < n.val - i.val) ⦄ := by
    unfold maximum_tastiness_loop0.body
    split
    · rename_i hlt
      have hilt : i.val < price.length := by
        have h := hlt; rw [UScalar.lt_equiv] at h; omega
      apply WP.spec_bind (Slice.index_usize_spec price i hilt)
      intro i1 hi1
      have hpl : sorted.val.length < Usize.max := by
        rw [hinv, List.length_take]
        have h1 : i.val ≤ price.val.length := by simpa using hilt.le
        rw [Nat.min_eq_left h1]
        exact lt_of_lt_of_le hilt (by simpa using price.property)
      apply WP.spec_bind (alloc.vec.Vec.push_spec sorted i1 hpl)
      intro sorted1 hs1
      apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := i) (y := 1#usize)
        (by scalar_tac))
      intro i2 hi2
      have hi2v : i2.val = i.val + 1 := by simpa using hi2
      simp only [WP.spec_ok]
      refine ⟨?_, ?_, ?_⟩
      · rw [hs1, hinv, hi2v, List.take_succ_eq_append_getElem hilt, hi1]
      · rw [hi2v]; omega
      · rw [hi2v]; omega
    · rename_i hge
      have hile : n.val ≤ i.val := by
        have h := hge; rw [UScalar.lt_equiv] at h; omega
      have hieq : i.val = n.val := le_antisymm hi hile
      simp only [WP.spec_ok]
      rw [hinv, hieq, hn, List.take_length]

  theorem loop0_spec (price : Slice Std.I64) (n : Std.Usize) (hn : n.val = price.length) :
      maximum_tastiness_loop0 price n (alloc.vec.Vec.new Std.I64) 0#usize
        ⦃ v => v.val = price.val ⦄ := by
    unfold maximum_tastiness_loop0
    apply loop.spec_decr_nat (fun p : alloc.vec.Vec Std.I64 × Std.Usize => n.val - p.2.val)
      (fun p => p.2.val ≤ n.val ∧ p.1.val = price.val.take p.2.val)
      (fun v => v.val = price.val)
      (fun p => maximum_tastiness_loop0.body price n p.1 p.2)
      (alloc.vec.Vec.new Std.I64, 0#usize)
    · rintro ⟨v, i⟩ ⟨hi, hinv⟩
      apply WP.spec_mono (loop0_body_spec price n v i hn hi hinv)
      intro r hr
      cases r with
      | done x => simpa using hr
      | cont p => exact ⟨⟨hr.2.1, hr.1⟩, hr.2.2⟩
    · refine ⟨by simp, by simp⟩

  /-! ### Stepping lemmas for the main function -/

  theorem sort_spec_wp (s : Slice Std.I64) :
      WP.spec (alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s)
        (fun t => t.val.Perm s.val ∧ SortedV t.val ∧ t.length = s.length) := by
    obtain ⟨t, ht, h1, h2, h3⟩ := sort_spec s
    rw [ht]
    simp only [WP.spec_ok]
    exact ⟨h1, h2, h3⟩

  theorem deref_mut_spec (v : alloc.vec.Vec Std.I64) :
      WP.spec (lift (alloc.vec.Vec.deref_mut v))
        (fun p : Slice Std.I64 × (Slice Std.I64 → alloc.vec.Vec Std.I64) =>
          p.1.val = v.val ∧ ∀ s', (p.2 s').val = s'.val) := by
    rw [show lift (alloc.vec.Vec.deref_mut v) = ok (alloc.vec.Vec.deref_mut v) from rfl]
    rw [show alloc.vec.Vec.deref_mut v = (v.slice, fun s => { slice := s })
      from rfl]
    simp only [WP.spec_ok]
    exact ⟨rfl, fun s' => rfl⟩

  theorem vec_index_spec (v : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (h : i.val < v.val.length) :
      WP.spec (alloc.vec.Vec.index (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice Std.I64) v i)
        (fun x => x = v.val.getD i.val 0#i64) := by
    rw [alloc.vec.Vec.index_slice_index]
    apply WP.spec_mono (alloc.vec.Vec.index_usize_spec (v := v) (i := i) h)
    intro x hx
    rw [hx]
    exact (List.getD_eq_getElem v.val 0#i64 h).symm

  theorem vals_getD_val {s : Slice Std.I64} {i : ℕ} (h : i < s.length) :
      (vals s).getD i 0 = (s.val.getD i 0#i64).val := by
    rw [vals_getD_eq h, List.getD_eq_getElem s.val 0#i64 h]

  theorem usize_zero_val : ((0#usize : Std.Usize).val : ℕ) = 0 := rfl

  theorem mem_kSelections {l : List ℤ} {k : ℕ} {S : Finset ℕ} :
      S ∈ kSelections l k ↔ S ⊆ Finset.range l.length ∧ S.card = k := by
    simp [kSelections]

  theorem selOK_perm_iff {l₁ l₂ : List ℤ} (h : l₁.Perm l₂) (k : ℕ) (d : ℤ) :
      (∃ S ∈ kSelections l₁ k, goodSel l₁ d S) ↔
        (∃ S ∈ kSelections l₂ k, goodSel l₂ d S) := by
    constructor
    · rintro ⟨S₁, hS₁, hg⟩
      obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS₁
      obtain ⟨S₂, hsub₂, hcard₂, hiff⟩ := perm_good_sel h d S₁ hsub
      exact ⟨S₂, mem_kSelections.mpr ⟨hsub₂, by rw [hcard₂, hcard]⟩, hiff.mpr hg⟩
    · rintro ⟨S₂, hS₂, hg⟩
      obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS₂
      obtain ⟨S₁, hsub₁, hcard₁, hiff⟩ := perm_good_sel h.symm d S₂ hsub
      exact ⟨S₁, mem_kSelections.mpr ⟨hsub₁, by rw [hcard₁, hcard]⟩, hiff.mpr hg⟩

  theorem loop1_spec_wp (sv : Slice Std.I64) (sorted : alloc.vec.Vec Std.I64) (k : Std.I64)
      (hsv : alloc.vec.Vec.deref sorted = sv)
      (hv : ∀ x ∈ sv.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hS : SortedV sv.val) (hpos : 0 < sv.length) (hlen : sv.length ≤ 100000)
      (hk : 2 ≤ k.val) (hklen : k.val ≤ (sv.length : ℤ))
      (hi : Std.I64)
      (hhib : hi.val = (vals sv).getD (sv.length - 1) 0 - (vals sv).getD 0 0 + 1) :
      WP.spec (maximum_tastiness_loop1 k sorted 0#i64 hi) (fun lo => 0 ≤ lo.val ∧
        (∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧ goodSel (vals sv) lo.val S) ∧
        (¬ ∃ S, S ⊆ Finset.range sv.length ∧ S.card = k.val.toNat ∧
          goodSel (vals sv) (lo.val + 1) S)) := by
    obtain ⟨lo, heq, h1, h2, h3⟩ := loop1_spec sv sorted k hsv hv hS hpos hlen hk hklen hi hhib
    rw [heq]
    simp only [WP.spec_ok]
    exact ⟨h1, h2, h3⟩

  /-! ### The main function, from the loop result to the specification -/

  theorem maximum_tastiness_core (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_len : price.length ≤ 100000)
      (hv : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk : 2 ≤ k.val) (hklen : k.val ≤ (price.length : ℤ)) :
      ∃ r, maximum_tastiness price k = ok r ∧ 0 ≤ r.val ∧
        (∃ S ∈ kSelections (vals price) k.val.toNat, goodSel (vals price) r.val S) ∧
        ¬ (∃ S ∈ kSelections (vals price) k.val.toNat, goodSel (vals price) (r.val + 1) S) := by
    classical
    have hpvlen : price.length = price.val.length := rfl
    have hpl : 1 ≤ price.val.length := by rw [← hpvlen]; omega
    have hne : ¬ (Slice.len price = 0#usize) := by
      intro h
      have h1 : (Slice.len price).val = (0#usize).val := congrArg _ h
      rw [Slice.len_val] at h1
      rw [usize_zero_val] at h1
      omega
    have hspec : maximum_tastiness price k ⦃ r => 0 ≤ r.val ∧
        (∃ S ∈ kSelections (vals price) k.val.toNat, goodSel (vals price) r.val S) ∧
        ¬ (∃ S ∈ kSelections (vals price) k.val.toNat, goodSel (vals price) (r.val + 1) S) ⦄ := by
      unfold maximum_tastiness
      dsimp only
      rw [if_neg hne]
      apply WP.spec_bind (loop0_spec price (Slice.len price) rfl)
      intro sorted hsorted
      apply WP.spec_bind (deref_mut_spec sorted)
      rintro ⟨s, back⟩ ⟨hs, hback⟩
      apply WP.spec_bind (sort_spec_wp s)
      intro t ht
      obtain ⟨hperm, htsorted, htlen⟩ := ht
      have hsval : s.val = price.val := hs.trans hsorted
      have htv : ∀ x ∈ t.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
        intro x hx
        exact hv x (by rw [← hsval]; exact hperm.subset hx)
      have htlen' : t.val.length = price.val.length := by rw [hperm.length_eq, hsval]
      have hsub1 : (1#usize).val ≤ (Slice.len price).val := by
        rw [Slice.len_val, usize_one_val]
        omega
      apply WP.spec_bind (UScalar.sub_spec (ty := .Usize) (x := Slice.len price) (y := 1#usize)
        hsub1)
      intro i hi
      have hiv : i.val = price.length - 1 := by
        have h := hi.1
        rw [Slice.len_val, usize_one_val] at h
        exact h
      have hidx1 : i.val < ((back t).val).length := by
        rw [hback t, htlen']
        omega
      apply WP.spec_bind (vec_index_spec (back t) i hidx1)
      intro i1 hi1
      have hidx1t : i.val < t.val.length := by rwa [hback t] at hidx1
      have hi1v : i1 = t.val.getD i.val 0#i64 := by rw [hi1, hback t]
      have hb1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        have hmem : i1 ∈ t.val := by
          rw [hi1v, List.getD_eq_getElem t.val 0#i64 hidx1t]
          exact List.getElem_mem hidx1t
        exact htv i1 hmem
      have hidx2 : (0#usize).val < ((back t).val).length := by
        rw [hback t, htlen', usize_zero_val]
        omega
      apply WP.spec_bind (vec_index_spec (back t) 0#usize hidx2)
      intro i2 hi2
      have hidx2t : (0#usize).val < t.val.length := by rwa [hback t] at hidx2
      have hi2v : i2 = t.val.getD (0#usize).val 0#i64 := by rw [hi2, hback t]
      have hi2v' : i2.val = (t.val.getD 0 0#i64).val := by
        rw [hi2v, usize_zero_val]
      have hb2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        have hmem : i2 ∈ t.val := by
          rw [hi2v, List.getD_eq_getElem t.val 0#i64 hidx2t]
          exact List.getElem_mem hidx2t
        exact htv i2 hmem
      apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := i1) (y := i2)
        (by scalar_tac) (by scalar_tac))
      intro md hmd
      have hmdv : md.val = i1.val - i2.val := hmd
      apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := md) (y := 1#i64)
        (by scalar_tac) (by scalar_tac))
      intro hi' hhi'
      have hhi'v : hi'.val = md.val + 1 := by
        rw [hhi', i64_one_val]
      let sv : Slice Std.I64 := alloc.vec.Vec.deref (back t)
      have hsvval : sv.val = t.val := by
        show (Slice.from (back t).val (back t).property).val = t.val
        rw [Slice.from_val, hback t]
      have hsvlen : sv.val.length = price.val.length := by rw [hsvval, htlen']
      have hsvlen2 : sv.length = price.length := by
        show sv.val.length = price.val.length
        exact hsvlen
      have hv' : ∀ x ∈ sv.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
        rw [hsvval]; exact htv
      have hS' : SortedV sv.val := by
        rw [hsvval]; exact htsorted
      have hpos' : 0 < sv.length := by
        show 0 < sv.val.length
        rw [hsvlen]; omega
      have hlen' : sv.length ≤ 100000 := by
        show sv.val.length ≤ 100000
        rw [hsvlen]; omega
      have hklen' : k.val ≤ (sv.length : ℤ) := by
        rw [hsvlen2]; exact hklen
      have hsub1' : sv.length - 1 = i.val := by
        show sv.val.length - 1 = i.val
        rw [hsvlen, hiv]
      have hlast : (vals sv).getD (sv.length - 1) 0 = i1.val := by
        have hpos1 : sv.length - 1 < sv.length := by
          show sv.val.length - 1 < sv.val.length
          rw [hsvlen]; omega
        rw [vals_getD_val hpos1, hsub1', hsvval, ← hi1v]
      have hfirst : (vals sv).getD 0 0 = i2.val := by
        rw [vals_getD_val hpos', hsvval]
        exact hi2v'.symm
      have hhib : hi'.val = (vals sv).getD (sv.length - 1) 0 - (vals sv).getD 0 0 + 1 := by
        rw [hlast, hfirst, hhi'v, hmdv]
      apply WP.spec_mono (loop1_spec_wp sv (back t) k rfl hv' hS' hpos' hlen' hk hklen' hi' hhib)
      intro lo hlo
      obtain ⟨hlo0, hyes, hno⟩ := hlo
      have hno' : ¬ (∃ S ∈ kSelections (vals sv) k.val.toNat, goodSel (vals sv) (lo.val + 1) S) := by
        rintro ⟨S, hS, hg⟩
        obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS
        exact hno ⟨S, by rwa [vals_length] at hsub, hcard, hg⟩
      have hyes' : ∃ S ∈ kSelections (vals sv) k.val.toNat, goodSel (vals sv) lo.val S := by
        obtain ⟨S, hsub, hcard, hg⟩ := hyes
        exact ⟨S, mem_kSelections.mpr ⟨by rwa [vals_length], hcard⟩, hg⟩
      have hpermv : (vals sv).Perm (vals price) := by
        have h1 : t.val.Perm price.val := hsval ▸ hperm
        have h2 := h1.map (fun x : Std.I64 => x.val)
        simpa [vals, hsvval] using h2
      refine ⟨hlo0, ?_, ?_⟩
      · exact (selOK_perm_iff hpermv k.val.toNat lo.val).mp hyes'
      · intro hc
        exact hno' ((selOK_perm_iff hpermv k.val.toNat (lo.val + 1)).mpr hc)
    exact spec_exists_ok hspec

  /-! ### Relating the maximal gap to `maxTastiness` -/

  theorem pairDistsOn_nonempty {l : List ℤ} {S : Finset ℕ} (h : 2 ≤ S.card) :
      (pairDistsOn l S).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have key : ∀ i j, i ∈ S → j ∈ S → i < j →
        absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := by
      intro i j hi hj hij
      rw [pairDistsOn, Finset.mem_image]
      exact ⟨(i, j), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hij⟩, rfl⟩
    rcases lt_or_gt_of_ne hab with h' | h'
    · exact ⟨_, key a b ha hb h'⟩
    · exact ⟨_, key b a hb ha h'⟩

  theorem goodSel_iff_le_tastinessOn {l : List ℤ} {S : Finset ℕ} (hne : 2 ≤ S.card) (d : ℤ) :
      goodSel l d S ↔ d ≤ tastinessOn l S := by
    have hne' := pairDistsOn_nonempty (l := l) hne
    have hmem : ∀ i j : ℕ, i ∈ S → j ∈ S → i < j →
        absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := by
      intro i j hi hj hij
      rw [pairDistsOn, Finset.mem_image]
      exact ⟨(i, j), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hij⟩, rfl⟩
    constructor
    · intro hg
      rw [tastinessOn, dite_eq_left hne', Finset.le_min'_iff]
      intro y hy
      rw [pairDistsOn, Finset.mem_image] at hy
      obtain ⟨⟨i, j⟩, hp, rfl⟩ := hy
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hij⟩ := hp
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp1
      exact hg i hi j hj (ne_of_lt hij)
    · intro hd i hi j hj hij
      rw [tastinessOn, dite_eq_left hne'] at hd
      rcases lt_or_gt_of_ne hij with h' | h'
      · exact le_trans hd (Finset.min'_le _ _ (hmem i j hi hj h'))
      · rw [absDiff_comm]
        exact le_trans hd (Finset.min'_le _ _ (hmem j i hj hi h'))

  theorem le_maxTastiness {l : List ℤ} {k : ℕ} {d : ℤ} (hk : 2 ≤ k)
      (h : ∃ S ∈ kSelections l k, goodSel l d S) : d ≤ maxTastiness l k := by
    obtain ⟨S, hS, hg⟩ := h
    obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS
    have hne : (kSelections l k).Nonempty := ⟨S, hS⟩
    rw [maxTastiness, dite_eq_left hne]
    have himg : tastinessOn l S ∈ (kSelections l k).image (tastinessOn l) :=
      Finset.mem_image.mpr ⟨S, hS, rfl⟩
    refine le_trans ?_ (Finset.le_max' _ _ himg)
    rw [← goodSel_iff_le_tastinessOn (l := l) (S := S) (by rw [hcard]; exact hk)]
    exact hg

  theorem maxTastiness_le {l : List ℤ} {k : ℕ} {lo : ℤ} (hk : 2 ≤ k)
      (hne : (kSelections l k).Nonempty)
      (h : ¬ ∃ S ∈ kSelections l k, goodSel l (lo + 1) S) : maxTastiness l k ≤ lo := by
    rw [maxTastiness, dite_eq_left hne]
    apply Finset.max'_le
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS
    by_contra hcon
    exact h ⟨S, hS, by
      rw [goodSel_iff_le_tastinessOn (l := l) (S := S) (by rw [hcard]; exact hk)]
      omega⟩

  /-- **S5 (witness).**  The result is the tastiness of some `k`-element selection of
  positions. -/
  theorem spec_5 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧
          S.card = k.val.toNat ∧ tastinessOn (vals price) S = r.val := by
    obtain ⟨r, heq, hr0, hyes, hno⟩ :=
      maximum_tastiness_core price k h_n h_len h_price h_k_lo h_k_hi
    have hk2 : 2 ≤ k.val.toNat := by
      have h1 : ((k.val.toNat : ℕ) : ℤ) = k.val := Int.toNat_of_nonneg (by omega)
      omega
    have hne : (kSelections (vals price) k.val.toNat).Nonempty := by
      obtain ⟨S, hS, -⟩ := hyes
      exact ⟨S, hS⟩
    have h1 : r.val ≤ maxTastiness (vals price) k.val.toNat := le_maxTastiness hk2 hyes
    have h2 : maxTastiness (vals price) k.val.toNat ≤ r.val := maxTastiness_le hk2 hne hno
    have hat : ∃ S ∈ kSelections (vals price) k.val.toNat,
        tastinessOn (vals price) S = maxTastiness (vals price) k.val.toNat := by
      have himg : maxTastiness (vals price) k.val.toNat ∈
          ((kSelections (vals price) k.val.toNat).image (tastinessOn (vals price))) := by
        rw [maxTastiness, dite_eq_left hne]
        exact Finset.max'_mem _ _
      obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp himg
      exact ⟨S, hS, hSeq⟩
    obtain ⟨S₀, hS₀, hS₀eq⟩ := hat
    obtain ⟨hsub, hcard⟩ := mem_kSelections.mp hS₀
    exact ⟨r, heq, S₀, hsub, hcard, hS₀eq.trans (le_antisymm h2 h1)⟩

  end AegisSpec.MaximumTastiness
