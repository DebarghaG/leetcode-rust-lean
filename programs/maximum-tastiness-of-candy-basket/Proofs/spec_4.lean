import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_4` (maximum-tastiness-of-candy-basket).
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

  /-! ## Helpers for the proof of S4 -/

  /-- `AegisShim.sortInsert` at the `I64` comparison produces a permutation. -/
  private lemma sortInsert_perm (x : Std.I64) (l : List Std.I64) :
      ∃ l', AegisShim.sortInsert core.cmp.OrdI64.cmp x l = ok l' ∧ l'.Perm (x :: l) := by
    induction l with
    | nil => exact ⟨[x], rfl, List.Perm.refl _⟩
    | cons y ys ih =>
      obtain ⟨l', hl', hperm⟩ := ih
      simp only [AegisShim.sortInsert, liftFun2, core.cmp.impls.OrdI64.cmp]
      cases hc : compare x.val y.val
      · refine ⟨x :: y :: ys, ?_, List.Perm.refl _⟩
        simp
      · refine ⟨x :: y :: ys, ?_, List.Perm.refl _⟩
        simp
      · refine ⟨y :: l', ?_, ?_⟩
        · have hEq : AegisShim.sortInsert (liftFun2 core.cmp.impls.OrdI64.cmp) x ys
              = AegisShim.sortInsert core.cmp.OrdI64.cmp x ys := rfl
          rw [hEq, hl']
          simp
        · exact (hperm.cons y).trans (List.Perm.swap x y ys)

  /-- `AegisShim.sortList` at the `I64` comparison produces a permutation. -/
  private lemma sortList_perm (l : List Std.I64) :
      ∃ l', AegisShim.sortList core.cmp.OrdI64.cmp l = ok l' ∧ l'.Perm l := by
    induction l with
    | nil => exact ⟨[], rfl, List.Perm.refl _⟩
    | cons x xs ih =>
      obtain ⟨l', hl', hperm⟩ := ih
      obtain ⟨l'', hl'', hperm''⟩ := sortInsert_perm x l'
      refine ⟨l'', ?_, ?_⟩
      · simp only [AegisShim.sortList]
        have hEqS : AegisShim.sortList (liftFun2 core.cmp.impls.OrdI64.cmp) xs
            = AegisShim.sortList core.cmp.OrdI64.cmp xs := rfl
        rw [hEqS, hl']
        simp only [bind_ok]
        have hEq : AegisShim.sortInsert (liftFun2 core.cmp.impls.OrdI64.cmp) x l'
            = AegisShim.sortInsert core.cmp.OrdI64.cmp x l' := rfl
        rw [hEq, hl'']
      · exact hperm''.trans (hperm.cons x)

  /-- `Slice.sort` produces a permutation of the entries. -/
  private lemma slice_sort_perm (s : Slice Std.I64) :
      ∃ s', alloc.slice.Slice.sort core.cmp.OrdI64 s = ok s' ∧ s'.val.Perm s.val := by
    obtain ⟨l', hl', hperm⟩ := sortList_perm s.val
    unfold alloc.slice.Slice.sort
    rw [hl']
    simp only [bind_ok]
    have hlen : l'.length ≤ Usize.max := by
      rw [hperm.length_eq]
      exact Slice.property s
    refine ⟨Slice.from l' hlen, ?_, ?_⟩
    · simp [dite_eq_left_iff, hlen]
    · simpa using hperm

  /-- `AegisShim.sortInsert` at the `I64` comparison produces a sorted list. -/
  private lemma sortInsert_pairwise (x : Std.I64) (l : List Std.I64)
      (hl : l.Pairwise (fun a b => a.val ≤ b.val)) :
      ∃ l', AegisShim.sortInsert core.cmp.OrdI64.cmp x l = ok l' ∧
        l'.Pairwise (fun a b => a.val ≤ b.val) := by
    revert hl
    induction l with
    | nil =>
      intro _
      exact ⟨[x], rfl, List.Pairwise.cons (by simp) List.Pairwise.nil⟩
    | cons y ys ih =>
      intro hl
      have htail : ys.Pairwise (fun a b => a.val ≤ b.val) := (List.pairwise_cons.mp hl).2
      have hhead : ∀ a ∈ ys, y.val ≤ a.val := (List.pairwise_cons.mp hl).1
      obtain ⟨l', hl', hp'⟩ := ih htail
      simp only [AegisShim.sortInsert, liftFun2, core.cmp.impls.OrdI64.cmp]
      cases hc : compare x.val y.val
      · refine ⟨x :: y :: ys, by simp, ?_⟩
        refine List.Pairwise.cons ?_ hl
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzys
        · have h := compare_lt_iff_lt.mp hc
          omega
        · have h1 := hhead z hzys
          have h2 := compare_lt_iff_lt.mp hc
          omega
      · refine ⟨x :: y :: ys, by simp, ?_⟩
        refine List.Pairwise.cons ?_ hl
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzys
        · have h := compare_eq_iff_eq.mp hc
          omega
        · have h1 := hhead z hzys
          have h2 := compare_eq_iff_eq.mp hc
          omega
      · refine ⟨y :: l', ?_, ?_⟩
        · have hEq : AegisShim.sortInsert (liftFun2 core.cmp.impls.OrdI64.cmp) x ys
              = AegisShim.sortInsert core.cmp.OrdI64.cmp x ys := rfl
          rw [hEq, hl']
          simp
        · have hgt : y.val ≤ x.val := by
            have h := compare_gt_iff_gt.mp hc
            omega
          have hperm : l'.Perm (x :: ys) := by
            obtain ⟨l'', hl'', hp⟩ := sortInsert_perm x ys
            rw [hl'] at hl''
            have heq : l' = l'' := by simpa only [Result.ok.injEq] using hl''
            subst heq
            exact hp
          have hmem : ∀ z ∈ l', y.val ≤ z.val := by
            intro z hz
            rcases List.mem_cons.mp (hperm.mem_iff.mp hz) with rfl | hzys
            · exact hgt
            · exact hhead z hzys
          exact List.Pairwise.cons hmem hp'

  /-- `AegisShim.sortList` at the `I64` comparison produces a sorted list. -/
  private lemma sortList_pairwise (l : List Std.I64) :
      ∃ l', AegisShim.sortList core.cmp.OrdI64.cmp l = ok l' ∧
        l'.Pairwise (fun a b => a.val ≤ b.val) := by
    induction l with
    | nil => exact ⟨[], rfl, List.Pairwise.nil⟩
    | cons x xs ih =>
      obtain ⟨l', hl', hp'⟩ := ih
      obtain ⟨l'', hl'', hp''⟩ := sortInsert_pairwise x l' hp'
      refine ⟨l'', ?_, hp''⟩
      simp only [AegisShim.sortList]
      have hEqS : AegisShim.sortList (liftFun2 core.cmp.impls.OrdI64.cmp) xs
          = AegisShim.sortList core.cmp.OrdI64.cmp xs := rfl
      rw [hEqS, hl']
      simp only [bind_ok]
      have hEq : AegisShim.sortInsert (liftFun2 core.cmp.impls.OrdI64.cmp) x l'
          = AegisShim.sortInsert core.cmp.OrdI64.cmp x l' := rfl
      rw [hEq, hl'']

  /-- `Slice.sort` produces a sorted permutation of the entries. -/
  private lemma slice_sort_perm_pairwise (s : Slice Std.I64) :
      ∃ s', alloc.slice.Slice.sort core.cmp.OrdI64 s = ok s' ∧ s'.val.Perm s.val ∧
        s'.val.Pairwise (fun a b => a.val ≤ b.val) := by
    obtain ⟨l', hl', hp'⟩ := sortList_pairwise s.val
    have hperm : l'.Perm s.val := by
      obtain ⟨l'', hl'', hp⟩ := sortList_perm s.val
      rw [hl'] at hl''
      have heq : l' = l'' := by simpa only [Result.ok.injEq] using hl''
      subst heq
      exact hp
    unfold alloc.slice.Slice.sort
    rw [hl']
    simp only [bind_ok]
    have hlen : l'.length ≤ Usize.max := by
      rw [hperm.length_eq]
      exact Slice.property s
    refine ⟨Slice.from l' hlen, ?_, ?_, ?_⟩
    · simp [dite_eq_left_iff, hlen]
    · simpa using hperm
    · simpa using hp'

  /-- Step-friendly version of `slice_sort_perm_pairwise`. -/
  @[step] private theorem slice_sort_spec (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s ⦃ s' =>
        s'.val.Perm s.val ∧ s'.val.Pairwise (fun a b => a.val ≤ b.val) ⦄ := by
    obtain ⟨s', hs', hperm, hpw⟩ := slice_sort_perm_pairwise s
    rw [hs']
    simp only [Std.WP.spec_ok]
    exact ⟨hperm, hpw⟩

  /-! ### Membership lemmas about `maxPrice` and `minPrice` -/

  private lemma mem_toFinset_of_perm {l₁ l₂ : List ℤ} (h : l₁.Perm l₂) {x : ℤ}
      (hx : x ∈ l₁) : x ∈ l₂.toFinset := by
    rw [List.mem_toFinset]
    exact h.mem_iff.mp hx

  private lemma toFinset_nonempty_of_pos {l : List ℤ} (h : 0 < l.length) :
      l.toFinset.Nonempty := by
    cases l with
    | nil => simp at h
    | cons a t => exact ⟨a, by simp⟩

  private lemma le_maxPrice {l : List ℤ} (h : l.toFinset.Nonempty) {x : ℤ}
      (hx : x ∈ l.toFinset) : x ≤ maxPrice l := by
    unfold maxPrice
    rw [dif_pos h]
    exact Finset.le_max' _ _ hx

  private lemma minPrice_le {l : List ℤ} (h : l.toFinset.Nonempty) {x : ℤ}
      (hx : x ∈ l.toFinset) : minPrice l ≤ x := by
    unfold minPrice
    rw [dif_pos h]
    exact Finset.min'_le _ _ hx

  private lemma spread_nonneg {l : List ℤ} (h : l.toFinset.Nonempty) :
      0 ≤ maxPrice l - minPrice l := by
    have h1 : minPrice l ≤ maxPrice l :=
      minPrice_le h (by
        unfold maxPrice
        rw [dif_pos h]
        exact Finset.max'_mem _ h)
    omega

  private lemma sub_le_spread {l : List ℤ} (h : l.toFinset.Nonempty) {a b : ℤ}
      (ha : a ∈ l.toFinset) (hb : b ∈ l.toFinset) : b - a ≤ maxPrice l - minPrice l := by
    have h1 : b ≤ maxPrice l := le_maxPrice h hb
    have h2 : minPrice l ≤ a := minPrice_le h ha
    omega

  /-! ### Conversion of a total-correctness triple into an existential statement -/

  private lemma spec_exists_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
      ∃ r, m = ok r ∧ P r := by
    cases m using Result.cases with
    | ret r => exact ⟨r, rfl, by simpa using h⟩
    | vis eff k => simp only [Std.WP.spec_vis] at h
    | div => simp only [Std.WP.spec_div] at h

  /-! ### Specs for the loops of `maximum_tastiness` -/

  private theorem loop0_spec_gen (price : Slice Std.I64) (n : Std.Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hn : n.val = price.length) (hi : i.val ≤ price.length)
      (hsorted : sorted.val = price.val.take i.val) (hlen : price.length ≤ 100000) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n sorted i ⦃ v => v.val = price.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
    apply Std.loop.spec_decr_nat
      (fun (p : alloc.vec.Vec Std.I64 × Std.Usize) => n.val - p.2.val)
      (fun p => p.1.val = price.val.take p.2.val ∧ p.2.val ≤ price.length)
      (fun (v : alloc.vec.Vec Std.I64) => v.val = price.val)
    · rintro ⟨sorted0, i0⟩ ⟨hs, hi0⟩
      dsimp only at hs hi0
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
      dsimp only
      by_cases hlt : i0 < n
      · rw [if_pos hlt]
        step*
        have h2 : i0.val < n.val := hlt
        have h3 : n.val = price.length := hn
        refine ⟨?_, ?_, ?_⟩
        · rw [sorted1_post, hs, i1_post, i2_post]
          exact List.take_concat_get' _ _ (by
            have h1 : (↑i0 : Nat) < price.length := by omega
            simpa using h1)
        · rw [i2_post]; omega
        · rw [i2_post]; omega
      · rw [if_neg hlt]
        simp only [Std.WP.spec_ok]
        have h4 : n.val ≤ i0.val := Nat.le_of_not_lt hlt
        have hge : price.length ≤ i0.val := by rw [← hn]; exact h4
        rw [hs]
        exact List.take_of_length_le (by simpa using hge)
    · exact ⟨hsorted, hi⟩

  private theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hne : 0 < sorted.length)
      (hvals : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make sorted k d ⦃ _ => True ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    dsimp only
    by_cases hk : k <= 1#i64
    · rw [if_pos hk]
      simp only [Std.WP.spec_ok]
    · rw [if_neg hk]
      step*
      unfold Aegis.MaximumTastiness.can_make_loop
      apply Std.loop.spec_decr_nat (α := Std.I64 × Std.I64 × Std.Usize) (β := Bool)
        (fun (p : Std.I64 × Std.I64 × Std.Usize) => sorted.val.length - p.2.2.val)
        (fun p => p.2.2.val ≤ sorted.val.length ∧
                  (1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000) ∧
                  (p.1.val < k.val ∨ p.1.val = 1) ∧
                  p.1.val ≤ (p.2.2.val : ℤ) + 1)
        (fun _ => True)
        (fun x => Aegis.MaximumTastiness.can_make_loop.body sorted k d sorted.len x.1 x.2.1 x.2.2)
        (1#i64, last, 1#usize)
      · rintro ⟨count0, last0, i0⟩ ⟨hi0, hlast0b, hcounth, hc1⟩
        dsimp only at hi0 hlast0b hcounth hc1
        unfold Aegis.MaximumTastiness.can_make_loop.body
        dsimp only
        by_cases hlt : i0 < sorted.len
        · rw [if_pos hlt]
          have hi0len : i0.val < sorted.val.length := by
            have h1 : i0.val < (sorted.len).val := hlt
            rw [Slice.len_val] at h1
            exact h1
          have hmem : sorted.val[i0.val] ∈ sorted.val := List.getElem_mem hi0len
          have hb1 : 1 ≤ sorted.val[i0.val].val := (hvals _ hmem).1
          have hb2 : sorted.val[i0.val].val ≤ 1000000000 := (hvals _ hmem).2
          step*
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · rw [i1_post]; exact hb1
            · rw [i1_post]; exact hb2
            · left
              simp only [ge_iff_le, IScalar.le_equiv] at *
              omega
            · rw [count1_post]; omega
            · omega
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · exact hlast0b.1
            · exact hlast0b.2
            · exact hcounth
            · omega
            · omega
        · rw [if_neg hlt]
          simp only [Std.WP.spec_ok]
      · dsimp only
        refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · exact Nat.succ_le_of_lt hne
        · rw [last_post]
          exact (hvals _ (List.getElem_mem (by simpa using hne))).1
        · rw [last_post]
          exact (hvals _ (List.getElem_mem (by simpa using hne))).2
        · right; simp
        · simp

  private theorem loop1_spec_gen (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (lo hi : Std.I64)
      (hne : 0 < sorted.val.length)
      (hvals : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hhi : hi.val ≤ 1000000001) (hlo : 0 ≤ lo.val) (hlohi : lo.val < hi.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi ⦃ r => r.val < hi.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
    apply Std.loop.spec_decr_nat
    case measure => exact fun (p : Std.I64 × Std.I64) => (p.2.val - p.1.val).toNat
    case inv => exact fun p => 0 ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ hi.val
    case hBody =>
      rintro ⟨lo0, hi0⟩ ⟨h1, h2, h3⟩
      simp only at h1 h2 h3
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
      simp only
      step
      spec_split_if as hlt
      · step
        step
        step
        · have hi1nn : (0 : ℤ) ≤ ↑i1 := by rw [i1_post]; omega
          have hi2le : (↑i2 : ℤ) ≤ ↑i1 := by
            rw [i2_post]
            exact Int.tdiv_le_self 2 hi1nn
          have hi1le : (↑i1 : ℤ) ≤ 1000000001 := by rw [i1_post]; omega
          rw [I64.max_eq]
          omega
        · have hne1 : 0 < sorted.deref.length := by
            simpa [alloc.vec.Vec.deref] using hne
          have hv1 : ∀ x ∈ sorted.deref.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
            intro x hx
            exact hvals x (by simpa [alloc.vec.Vec.deref] using hx)
          have hi1nn : (0 : ℤ) ≤ ↑i1 := by rw [i1_post]; omega
          have hi2 : (↑i2 : ℤ) = ↑i1 / 2 := by
            rw [i2_post, Int.tdiv_eq_ediv_of_nonneg hi1nn]
          have hlt' : (↑lo0 + 1 : ℤ) < ↑hi0 := by
            have h : (↑i : ℤ) < ↑hi0 := hlt
            rw [i_post] at h
            exact h
          step with (can_make_spec sorted.deref k mid hne1 hv1)
          spec_split_if as hb
          · rw [Std.WP.spec_ok]
            dsimp only
            exact ⟨by omega, by omega, by omega, by omega⟩
          · rw [Std.WP.spec_ok]
            dsimp only
            exact ⟨h1, by omega, by omega, by omega⟩
      · rw [Std.WP.spec_ok]
        dsimp only
        omega
    case hInv => exact ⟨hlo, hlohi, le_refl _⟩

  /-! ### Main specification used for S4 -/

  private theorem maximum_tastiness_spec (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      maximum_tastiness price k ⦃ r => r.val ≤ maxPrice (vals price) - minPrice (vals price) ⦄ := by
    unfold maximum_tastiness
    dsimp only
    step*
    step with loop0_spec_gen
    · simp
    · simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
      step with slice_sort_spec
      have hsorted_val : sorted.slice.val = price.val := sorted_post
      have r_perm : r.val.Perm price.val := hsorted_val ▸ r_post
      have hEqL : (({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64)
          = (↑r : List Std.I64) := rfl
      have hlen1 : ({ slice := r } : alloc.vec.Vec Std.I64).length = r.val.length := rfl
      have hlen_r : ({ slice := r } : alloc.vec.Vec Std.I64).length = price.length := by
        rw [hlen1]; exact r_perm.length_eq
      have hlen_r' : (↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64).length
          = price.length := by
        rw [hEqL, ← hlen1]; exact hlen_r
      have hv : ∀ x ∈ (↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64),
          1 ≤ x.val ∧ x.val ≤ 1000000000 := by
        intro x hx
        have h1 : x ∈ (↑r : List Std.I64) := hEqL ▸ hx
        have h2 : x ∈ (↑sorted.slice : List Std.I64) := r_post.mem_iff.mp h1
        exact h_price x (hsorted_val ▸ h2)
      have hpw : ((↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64)).Pairwise
          (fun a b => a.val ≤ b.val) := by
        rw [hEqL]; exact r_post1
      have hmapR : ((↑r : List Std.I64).map (fun x => x.val)).Perm (vals price) := by
        simpa [vals] using r_perm.map (fun x => x.val)
      have hmap : (((↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64)).map
          (fun x => x.val)).Perm (vals price) := by
        rw [hEqL]; exact hmapR
      have hne_r : 0 < ({ slice := r } : alloc.vec.Vec Std.I64).length := by
        rw [hlen_r]; omega
      have hzero : (0#i64).val = 0 := by simp
      step
      step
      step
      have hi_nat : i.val = price.length - 1 := by
        have h := i_post
        simp only [Slice.len_val] at h
        exact h
      have hidx1 : i.val
          < (↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64).length := by
        rw [hlen_r', hi_nat]; omega
      have hidx2 : 0
          < (↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64).length := by
        rw [hlen_r']; omega
      have b1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        refine hv _ ?_
        rw [i1_post]
        exact List.getElem_mem hidx1
      have b2 : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        refine hv _ ?_
        rw [i2_post]
        exact List.getElem_mem hidx2
      have hi21 : i2.val ≤ i1.val := by
        have hR : (((↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64))[0]).val
            ≤ (((↑({ slice := r } : alloc.vec.Vec Std.I64) : List Std.I64))[i.val]).val :=
          (List.pairwise_iff_getElem.mp hpw) 0 i.val hidx2 hidx1 (by omega)
        rw [i1_post, i2_post]
        exact hR
      step*
      have hhi : hi.val ≤ 1000000001 := by omega
      have hlohi : (0#i64).val < hi.val := by rw [hzero]; omega
      have hloop : Aegis.MaximumTastiness.maximum_tastiness_loop1 k { slice := r } 0#i64 hi
          ⦃ res => res.val < hi.val ⦄ :=
        loop1_spec_gen k { slice := r } 0#i64 hi hne_r hv hhi (by simp) hlohi
      refine WP.spec_mono hloop ?_
      intro res hres
      have hrs : res.val ≤ i1.val - i2.val := by
        have hh1 : hi.val = (i1.val - i2.val) + 1 := by rw [hi_post, max_diff_post]
        rw [hh1] at hres
        exact Int.lt_add_one_iff.mp hres
      have h1 : i1.val ∈ (vals price).toFinset := by
        refine mem_toFinset_of_perm hmap ?_
        rw [i1_post]
        exact List.mem_map_of_mem (List.getElem_mem hidx1)
      have h2 : i2.val ∈ (vals price).toFinset := by
        refine mem_toFinset_of_perm hmap ?_
        rw [i2_post]
        exact List.mem_map_of_mem (List.getElem_mem hidx2)
      have hne' : (vals price).toFinset.Nonempty := by
        apply toFinset_nonempty_of_pos
        have hlen : (vals price).length = price.length := by simp [vals]
        rw [hlen]
        omega
      have hfin := sub_le_spread hne' h2 h1
      exact le_trans hrs hfin

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
  theorem spec_4 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val ≤ maxPrice (vals price) - minPrice (vals price) := by
    exact spec_exists_ok (maximum_tastiness_spec price k h_n h_len h_price)

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
