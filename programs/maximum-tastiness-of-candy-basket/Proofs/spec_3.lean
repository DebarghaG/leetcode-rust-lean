import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_3` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary lemmas for `spec_S3` -/

  open Aegis.MaximumTastiness

  set_option maxHeartbeats 4000000

  /-- `sortInsert` inserts an element while preserving the multiset of elements. -/
  theorem sortInsert_perm {α : Type} (cmp : α → α → Result Ordering)
      (hcmp : ∀ a b, ∃ c, cmp a b = ok c) :
      ∀ (x : α) (l : List α), ∃ r, AegisShim.sortInsert cmp x l = ok r ∧ r.Perm (x :: l) := by
    intro x l
    induction l with
    | nil => exact ⟨[x], rfl, List.Perm.refl _⟩
    | cons y ys ih =>
      obtain ⟨c, hc⟩ := hcmp x y
      obtain ⟨r, hr, hp⟩ := ih
      cases c
      · exact ⟨x :: y :: ys, by simp [AegisShim.sortInsert, hc], List.Perm.refl _⟩
      · exact ⟨x :: y :: ys, by simp [AegisShim.sortInsert, hc], List.Perm.refl _⟩
      · refine ⟨y :: r, by simp [AegisShim.sortInsert, hc, hr], ?_⟩
        exact (hp.cons y).trans (List.Perm.swap x y ys)

  /-- `sortList` returns a permutation of its input. -/
  theorem sortList_perm {α : Type} (cmp : α → α → Result Ordering)
      (hcmp : ∀ a b, ∃ c, cmp a b = ok c) :
      ∀ (l : List α), ∃ r, AegisShim.sortList cmp l = ok r ∧ r.Perm l := by
    intro l
    induction l with
    | nil => exact ⟨[], rfl, List.Perm.refl _⟩
    | cons x xs ih =>
      obtain ⟨r, hr, hp⟩ := ih
      obtain ⟨r', hr', hp'⟩ := sortInsert_perm cmp hcmp x r
      refine ⟨r', by simp [AegisShim.sortList, hr, hr'], ?_⟩
      exact hp'.trans (hp.cons x)

  /-- The slice `sort` function returns a permutation of its input (in particular it
  preserves the length). -/
  @[step]
  theorem Slice.sort_perm {T : Type} (cmp : core.cmp.Ord T) (s : Slice T)
      (hcmp : ∀ a b, ∃ c, cmp.cmp a b = ok c) :
      alloc.slice.Slice.sort cmp s ⦃ r => r.val.Perm s.val ∧ r.length = s.length ⦄ := by
    obtain ⟨l, hl, hp⟩ := sortList_perm cmp.cmp hcmp s.val
    have hstep :
        (do let l' ← AegisShim.sortList cmp.cmp s.val
            if h : l'.length ≤ Usize.max then Result.ok (Slice.from l' h)
            else Result.fail Error.panic)
          = (if h : l.length ≤ Usize.max then Result.ok (Slice.from l h)
             else Result.fail Error.panic) := by
      rw [hl]; simp
    unfold alloc.slice.Slice.sort
    rw [hstep]
    by_cases h : l.length ≤ Usize.max
    · rw [dif_pos h]
      simp only [WP.spec_ok]
      exact ⟨by simp [Slice.from_val, hp], by simp [Slice.from_val, hp.length_eq]⟩
    · exact absurd (hp.length_eq ▸ s.property) h

  /-- Building the vector of the prices: the loop copies `price` into `sorted`. -/
  @[step]
  theorem maximum_tastiness_loop0_spec (price : Slice Std.I64) (n : Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Usize)
      (hn : n.val = price.length) (hi : i.val ≤ n.val)
      (hs : sorted.val = price.val.take i.val) :
      maximum_tastiness_loop0 price n sorted i
        ⦃ r => r.val.Perm price.val ∧ r.length = price.length ⦄ := by
    unfold maximum_tastiness_loop0
    apply loop.spec_decr_nat
      (fun (p : alloc.vec.Vec Std.I64 × Usize) => n.val - p.2.val)
      (fun (p : alloc.vec.Vec Std.I64 × Usize) =>
        p.2.val ≤ n.val ∧ p.1.val = price.val.take p.2.val)
      (fun (r : alloc.vec.Vec Std.I64) => r.val.Perm price.val ∧ r.length = price.length)
      (fun (p : alloc.vec.Vec Std.I64 × Usize) =>
        maximum_tastiness_loop0.body price n p.1 p.2)
    · intro x hx
      obtain ⟨sl, il⟩ := x
      obtain ⟨hil, hsl⟩ := hx
      simp only [Prod.fst, Prod.snd] at *
      unfold maximum_tastiness_loop0.body
      split
      · rename_i hlt
        step
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · -- (il + 1) ≤ n
          scalar_tac
        · -- the vector is still a prefix
          rw [sorted1_post, hsl, i1_post, i2_post]
          exact List.take_concat_get' price.val il.val (by scalar_tac)
        · -- measure decreases
          scalar_tac
      · simp only [WP.spec_ok]
        refine ⟨?_, ?_⟩
        · -- the prefix is the whole list
          have hge : price.val.length ≤ il.val := by scalar_tac
          have hp : sl.val = price.val := by rw [hsl, List.take_of_length_le hge]
          rw [hp]
        · have hge : price.val.length ≤ il.val := by scalar_tac
          show sl.val.length = price.val.length
          rw [hsl, List.take_of_length_le hge]
    · exact ⟨hi, hs⟩

  /-- `can_make_loop` never fails, as long as the values are small enough. -/
  @[step]
  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Usize)
      (count last : Std.I64) (i : Usize)
      (hval : ∀ x ∈ sorted.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hn : n.val = sorted.length) (hlen : sorted.length ≤ 100000)
      (hi : i.val ≤ n.val)
      (hc1 : 1 ≤ count.val) (hc2 : count.val ≤ (i.val : ℤ) + 1)
      (hl0 : 0 ≤ last.val) (hl1 : last.val ≤ 1000000000) :
      can_make_loop sorted k d n count last i ⦃ _ => True ⦄ := by
    unfold can_make_loop
    apply loop.spec_decr_nat
      (fun (st : Std.I64 × Std.I64 × Usize) => n.val - st.2.2.val)
      (fun (st : Std.I64 × Std.I64 × Usize) =>
        1 ≤ st.1.val ∧ st.1.val ≤ (st.2.2.val : ℤ) + 1 ∧
        0 ≤ st.2.1.val ∧ st.2.1.val ≤ 1000000000 ∧ st.2.2.val ≤ n.val)
      (fun (_ : Bool) => True)
      (fun (st : Std.I64 × Std.I64 × Usize) =>
        can_make_loop.body sorted k d n st.1 st.2.1 st.2.2)
    · rintro ⟨count, last, i⟩ ⟨hc1, hc2, hl0, hl1, hi⟩
      unfold can_make_loop.body
      split
      · rename_i hlt
        step
        have hmem : i1 ∈ sorted.val := by rw [i1_post]; exact List.getElem_mem _
        obtain ⟨hi1a, hi1b⟩ := hval i1 hmem
        step
        split
        · rename_i hge
          step
          split
          · simp only [WP.spec_ok]
          · step
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · scalar_tac
            · scalar_tac
            · scalar_tac
            · exact hi1b
            · scalar_tac
        · step
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · exact hc1
          · scalar_tac
          · exact hl0
          · exact hl1
          · scalar_tac
      · simp only [WP.spec_ok]
    · exact ⟨hc1, hc2, hl0, hl1, hi⟩

  /-- `can_make` never fails (on a non-empty array of small values). -/
  @[step]
  theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hval : ∀ x ∈ sorted.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlen : sorted.length ≤ 100000) (hne : 1 ≤ sorted.length) :
      can_make sorted k d ⦃ _ => True ⦄ := by
    unfold can_make
    split
    · simp only [WP.spec_ok]
    · refine WP.spec_bind (m := Slice.index_usize sorted 0#usize)
        (Pₘ := fun x => x = sorted.val[0]) ?_ ?_
      · exact Slice.index_usize_spec sorted 0#usize (by scalar_tac)
      · intro last hlast
        refine can_make_loop_spec sorted k d (Slice.len sorted) 1#i64 last 1#usize
          hval ?_ hlen ?_ ?_ ?_ ?_ ?_
        · simp
        · simp; scalar_tac
        · simp
        · simp
        · rw [hlast]; exact (hval _ (List.getElem_mem _)).1
        · rw [hlast]; exact (hval _ (List.getElem_mem _)).2

  /-- Truncated division by two of a large enough integer is positive. -/
  theorem tdiv_two_pos {x : ℤ} (h : 2 ≤ x) : 0 < x.tdiv 2 := by
    have hmod : x.tmod 2 < 2 := Int.tmod_lt_of_pos x (by norm_num)
    have hsum := Int.mul_tdiv_add_tmod x 2
    omega

  /-- Truncated division by two of a positive integer is strictly smaller. -/
  theorem tdiv_two_lt {x : ℤ} (h : 2 ≤ x) : x.tdiv 2 < x := by
    have hmod : 0 ≤ x.tmod 2 := Int.tmod_nonneg 2 (by omega)
    have hsum := Int.mul_tdiv_add_tmod x 2
    omega

  /-- The binary search loop returns a nonnegative value. -/
  @[step]
  theorem maximum_tastiness_loop1_spec (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (lo₀ hi₀ : Std.I64)
      (hval : ∀ x ∈ sorted.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlen : sorted.length ≤ 100000) (hne : 1 ≤ sorted.length)
      (hlo : 0 ≤ lo₀.val) (hlo' : lo₀.val ≤ 1000000000) (hhi : hi₀.val ≤ 1000000000) :
      maximum_tastiness_loop1 k sorted lo₀ hi₀ ⦃ r => 0 ≤ r.val ⦄ := by
    unfold maximum_tastiness_loop1
    apply loop.spec_decr_nat
      (fun (p : Std.I64 × Std.I64) => (p.2.val - p.1.val).toNat)
      (fun (p : Std.I64 × Std.I64) =>
        0 ≤ p.1.val ∧ p.1.val ≤ 1000000000 ∧ p.2.val ≤ 1000000000)
      (fun (r : Std.I64) => 0 ≤ r.val)
      (fun (p : Std.I64 × Std.I64) => maximum_tastiness_loop1.body k sorted p.1 p.2)
    · intro st hinv
      obtain ⟨lo, hi⟩ := st
      obtain ⟨hb1, hb2, hb3⟩ := hinv
      simp only [Prod.fst, Prod.snd] at *
      unfold maximum_tastiness_loop1.body
      step
      split
      · rename_i hlt
        simp only [IScalar.lt_equiv] at hlt
        have hgap : 2 ≤ hi.val - lo.val := by omega
        step
        step
        have hi2pos : 0 < i2.val := by
          rw [i2_post, i1_post]
          exact tdiv_two_pos hgap
        have hi2lt : i2.val < hi.val - lo.val := by
          rw [i2_post, i1_post]
          exact tdiv_two_lt hgap
        step
        step
        · -- the values of the sorted array stay in range
          intro x hx
          exact hval x (by simpa [alloc.vec.Vec.deref] using hx)
        · simpa [alloc.vec.Vec.deref] using hlen
        · simpa [alloc.vec.Vec.deref] using hne
        split
        · -- `can_make` returned `true`: continue with `(mid, hi)`
          simp only [WP.spec_ok]
          refine ⟨?_, ?_, ?_, ?_⟩
          · -- `0 ≤ mid`
            omega
          · omega
          · exact hb3
          · rw [Int.toNat_lt_toNat (by omega : (0:ℤ) < hi.val - lo.val)]
            omega
        · -- `can_make` returned `false`: continue with `(lo, mid)`
          simp only [WP.spec_ok]
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact hb1
          · exact hb2
          · -- `mid ≤ 10^9`
            omega
          · rw [Int.toNat_lt_toNat (by omega : (0:ℤ) < hi.val - lo.val)]
            omega
      · -- the loop stops: it returns `lo`
        simp only [WP.spec_ok]
        exact hb1
    · exact ⟨hlo, hlo', hhi⟩

  /-- `deref_mut` returns the underlying slice and the identity re-borrow. -/
  @[step]
  theorem Vec.deref_mut_spec' {T : Type} (v : alloc.vec.Vec T) :
      lift (alloc.vec.Vec.deref_mut v) ⦃ p =>
        p.1 = v.slice ∧ p.2 = (fun s => { slice := s }) ⦄ := by
    simp only [lift, WP.spec_ok, alloc.vec.Vec.deref_mut]
    trivial

  /-- Elements of a permutation of a list of prices stay within `[0, 10^9]`. -/
  theorem perm_bounds {l₁ l₂ : List Std.I64} (h : l₁.Perm l₂)
      (h₂ : ∀ x ∈ l₂, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ x ∈ l₁, 0 ≤ x.val ∧ x.val ≤ 1000000000 := by
    intro x hx
    obtain ⟨h1, h2⟩ := h₂ x (h.subset hx)
    exact ⟨by omega, h2⟩

  /-- A weakest-precondition specification yields an actual result. -/
  theorem Result.spec_exists {α : Type} {f : Result α} {p : α → Prop} (h : f ⦃ p ⦄) :
      ∃ r, f = ok r ∧ p r := by
    cases f using Result.cases with
    | ret x => exact ⟨x, rfl, by simpa using h⟩
    | vis i k => exact absurd h (by simp)
    | div => exact absurd h (by simp)

  /-- Nonnegativity of the result of the main function. -/
  theorem maximum_tastiness_spec (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      maximum_tastiness price k ⦃ r => 0 ≤ r.val ⦄ := by
    unfold maximum_tastiness
    dsimp only
    split
    · simp only [WP.spec_ok]
      norm_num
    · rename_i hn0
      step
      · -- the new vector is empty
        simp
      · step
        step
        subst s
        subst deref_mut_back
        beta_reduce
        have hlen1 : ({ slice := s1 } : alloc.vec.Vec Std.I64).length = price.length := by
          show s1.val.length = price.val.length
          exact s1_post1.trans sorted_post1
        have hperm : (s1.val).Perm price.val := by
          refine s1_post.trans ?_
          simpa [alloc.vec.Vec.val] using sorted_post
        have hval1 : ∀ x ∈ ({ slice := s1 } : alloc.vec.Vec Std.I64).val,
            0 ≤ x.val ∧ x.val ≤ 1000000000 := by
          intro x hx
          exact perm_bounds hperm h_price x hx
        have hprec : ∀ x ∈ ({ slice := s1 } : alloc.vec.Vec Std.I64).val,
            1 ≤ x.val := by
          intro x hx
          exact (h_price x (hperm.subset hx)).1
        step
        step
        step
        obtain ⟨hi1a, hi1b⟩ := hval1 i1 (by rw [i1_post]; exact List.getElem_mem _)
        obtain ⟨hi2a, hi2b⟩ := hval1 i2 (by rw [i2_post]; exact List.getElem_mem _)
        have hi2c : 1 ≤ i2.val := by
          rw [i2_post]
          exact hprec _ (List.getElem_mem _)
        step
        step
        step
        assumption


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
  theorem spec_3 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧ 0 ≤ r.val := by
    exact Result.spec_exists (maximum_tastiness_spec price k h_n h_len h_price)

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
