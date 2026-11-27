import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_2` (maximum-tastiness-of-candy-basket).
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

  /-! ## Internal helper lemmas

  Auxiliary (private) lemmas used to establish the totality statement `spec_S2`. -/

  open Aegis.MaximumTastiness

  private lemma can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize)
      (hn : n.val = sorted.length)
      (hk : k.val ≤ 100000)
      (hi : i.val ≤ n.val)
      (hcount : 1 ≤ count.val ∧ count.val ≤ k.val)
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlast : last ∈ sorted.val) :
      can_make_loop sorted k d n count last i ⦃ fun _ => True ⦄ := by
    unfold can_make_loop
    apply loop.spec_decr_nat
      (measure := fun (s : Std.I64 × Std.I64 × Std.Usize) => n.val - s.2.2.val)
      (inv := fun (s : Std.I64 × Std.I64 × Std.Usize) =>
        s.2.2.val ≤ n.val ∧ s.2.1 ∈ sorted.val ∧ 1 ≤ s.1.val ∧ s.1.val ≤ k.val)
      (post := fun _ => True)
    · rintro ⟨c, l, j⟩ ⟨hile, hlast', hcount1, hcountk⟩
      dsimp only at hile hlast' hcount1 hcountk ⊢
      unfold can_make_loop.body
      step*
      · obtain ⟨h1a, h1b⟩ : (1 : ℤ) ≤ i1.val ∧ i1.val ≤ 1000000000 :=
          hbnd i1 (by rw [i1_post]; exact List.getElem_mem ..)
        obtain ⟨h2a, h2b⟩ : (1 : ℤ) ≤ l.val ∧ l.val ≤ 1000000000 := hbnd l hlast'
        scalar_tac
      · obtain ⟨h1a, h1b⟩ : (1 : ℤ) ≤ i1.val ∧ i1.val ≤ 1000000000 :=
          hbnd i1 (by rw [i1_post]; exact List.getElem_mem ..)
        refine ⟨by scalar_tac, ?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
        rw [i1_post]
        exact List.getElem_mem ..
    · exact ⟨hi, hlast, hcount⟩

  @[step]
  private lemma can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hk : k.val ≤ 100000) (hlen : 1 ≤ sorted.length)
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      can_make sorted k d ⦃ fun _ => True ⦄ := by
    unfold can_make
    step*
    apply can_make_loop_spec
    · simp
    · exact hk
    · scalar_tac
    · exact ⟨by scalar_tac, by scalar_tac⟩
    · exact hbnd
    · rw [last_post]
      exact List.getElem_mem ..

  @[step]
  private lemma loop0_spec (price : Slice Std.I64) (n : Std.Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hn : n.val = price.length)
      (hlen : price.length ≤ 100000)
      (hi : i.val ≤ n.val)
      (hsorted : sorted.val = price.val.take i.val) :
      maximum_tastiness_loop0 price n sorted i ⦃ fun v => v.val = price.val ⦄ := by
    unfold maximum_tastiness_loop0
    apply loop.spec_decr_nat
      (measure := fun (s : alloc.vec.Vec Std.I64 × Std.Usize) => n.val - s.2.val)
      (inv := fun (s : alloc.vec.Vec Std.I64 × Std.Usize) =>
        s.2.val ≤ n.val ∧ s.1.val = price.val.take s.2.val)
      (post := fun (v : alloc.vec.Vec Std.I64) => v.val = price.val)
    · rintro ⟨s, j⟩ ⟨hjn, hs⟩
      dsimp only at hjn hs ⊢
      unfold maximum_tastiness_loop0.body
      step*
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have htake : List.take (↑j + 1) ↑price = List.take ↑j ↑price ++ [i1] := by
          rw [List.take_add_one, i1_post, List.getElem?_eq_getElem (by scalar_tac)]
          simp
        rw [sorted1_post, hs, i1_post, i2_post, htake]
        rw [i1_post]
      · have hj : j.val = n.val := by scalar_tac
        rw [hs, hj, hn, List.take_length]
    · exact ⟨hi, hsorted⟩

  private lemma ordI64_cmp_spec (a b : Std.I64) :
      core.cmp.OrdI64.cmp a b ⦃ fun _ => True ⦄ := by
    simp only [core.cmp.impls.OrdI64.cmp, liftFun2, WP.spec_ok]

  private lemma sortInsert_spec {α : Type _} (cmp : α → α → Result Ordering) (x : α) (l : List α)
      (hcmp : ∀ a b : α, cmp a b ⦃ fun _ => True ⦄) :
      AegisShim.sortInsert cmp x l ⦃ fun r => r.Perm (x :: l) ⦄ := by
    induction l with
    | nil => simp [AegisShim.sortInsert]
    | cons y ys ih =>
      simp only [AegisShim.sortInsert]
      apply WP.spec_bind (hcmp x y)
      intro c _
      split
      · apply WP.spec_bind ih
        intro r hr
        simp only [WP.spec_ok]
        exact (List.Perm.cons y hr).trans (List.Perm.swap x y ys)
      · simp only [WP.spec_ok]
        exact List.Perm.refl _

  private lemma sortList_spec {α : Type _} (cmp : α → α → Result Ordering) (l : List α)
      (hcmp : ∀ a b : α, cmp a b ⦃ fun _ => True ⦄) :
      AegisShim.sortList cmp l ⦃ fun r => r.Perm l ⦄ := by
    induction l with
    | nil => exact WP.spec_ok _ |>.mpr (List.Perm.refl _)
    | cons x xs ih =>
      unfold AegisShim.sortList
      apply WP.spec_bind ih
      intro r hr
      apply WP.spec_mono (sortInsert_spec cmp x r hcmp)
      intro r' hr'
      exact hr'.trans (List.Perm.cons x hr)

  @[step]
  private lemma slice_sort_spec (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s ⦃ fun s' => s'.val.Perm s.val ⦄ := by
    unfold alloc.slice.Slice.sort
    apply WP.spec_bind (sortList_spec core.cmp.OrdI64.cmp s.val (fun a b => ordI64_cmp_spec a b))
    intro l hl
    have hl_len : l.length ≤ Usize.max := by
      rw [hl.length_eq]
      exact s.length_ineq
    simp only [dite_eq_left hl_len, WP.spec_ok]
    rw [Slice.from_val]
    exact hl

  private lemma tdiv_two_nonneg (a : ℤ) (h : 0 ≤ a) :
      0 ≤ a.tdiv 2 ∧ a.tdiv 2 ≤ a := by
    rw [Int.tdiv_eq_ediv]; omega

  private lemma tdiv_two_pos (a : ℤ) (h : 2 ≤ a) :
      1 ≤ a.tdiv 2 ∧ a.tdiv 2 ≤ a - 1 := by
    rw [Int.tdiv_eq_ediv]; omega

  @[step]
  private lemma loop1_spec (k : Std.I64) (sorted : alloc.vec.Vec Std.I64) (lo hi : Std.I64)
      (hk : k.val ≤ 100000)
      (hlen : 1 ≤ sorted.length)
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlo : 0 ≤ lo.val) (hlh : lo.val ≤ 1000000001) (hhi : hi.val ≤ 1000000000) :
      maximum_tastiness_loop1 k sorted lo hi ⦃ fun _ => True ⦄ := by
    unfold maximum_tastiness_loop1
    apply loop.spec_decr_nat
      (measure := fun (s : Std.I64 × Std.I64) => (s.2.val - s.1.val).toNat)
      (inv := fun (s : Std.I64 × Std.I64) =>
        0 ≤ s.1.val ∧ s.1.val ≤ 1000000001 ∧ s.2.val ≤ 1000000000)
      (post := fun _ => True)
    · rintro ⟨l, h⟩ ⟨hl0, hlh', hh⟩
      dsimp only at hl0 hlh' hh ⊢
      unfold maximum_tastiness_loop1.body
      step*
      all_goals
        first
        | simpa [alloc.vec.Vec.deref] using hlen
        | (intro x hx; exact hbnd x (by simpa [alloc.vec.Vec.deref] using hx))
        | (have hi2 : i2.val = (h.val - l.val).tdiv 2 := by rw [i2_post, i1_post]
           have hgt : 2 ≤ h.val - l.val := by scalar_tac
           obtain ⟨hi2a, hi2b⟩ := tdiv_two_pos (h.val - l.val) hgt
           first
           | scalar_tac
           | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_⟩
              rw [Int.toNat_lt_toNat (by scalar_tac)]
              scalar_tac))
    · exact ⟨hlo, hlh, hhi⟩

  /-- A total specification implies the computation terminates with some value. -/
  private lemma spec_ok_exists {α : Type _} {m : Result α} (h : m ⦃ fun _ => True ⦄) :
      ∃ r, m = ok r := by
    revert h
    refine m.cases ?_ ?_ ?_
    · intro r _; exact ⟨r, rfl⟩
    · intro i k h; exact (WP.spec_vis i k).mp h |>.elim
    · intro h; exact (WP.spec_div.mp h).elim

  /-- Price bounds transfer along a permutation. -/
  private lemma perm_bounds {l l' : List Std.I64} (h : l'.Perm l)
      (hb : ∀ x ∈ l, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ x ∈ l', 1 ≤ x.val ∧ x.val ≤ 1000000000 :=
    fun x hx => hb x (h.mem_iff.mp hx)

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
  theorem spec_2 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r := by
    have hmain : maximum_tastiness price k ⦃ fun _ => True ⦄ := by
      unfold maximum_tastiness
      step*
      · simp
      · apply WP.spec_bind (m := lift (alloc.vec.Vec.deref_mut sorted))
          (Pₘ := fun x => x = (sorted.slice, fun s => { slice := s }))
        · simp only [lift, WP.spec_ok]
          rfl
        · rintro ⟨s, back⟩ h
          cases h
          step*
          all_goals
            have hp : (s1.val).Perm (price.val) := by
              have h := s1_post
              have h2 : (sorted.slice).val = price.val := sorted_post
              rwa [h2] at h
            have hs1len : ({ slice := s1 } : alloc.vec.Vec Std.I64).length = price.length := by
              show s1.val.length = price.val.length
              exact hp.length_eq
            have hs1b : ∀ x ∈ ({ slice := s1 } : alloc.vec.Vec Std.I64).val,
                1 ≤ x.val ∧ x.val ≤ 1000000000 := by
              intro x hx
              exact perm_bounds hp h_price x hx
            try have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 :=
              hs1b i1 (by rw [i1_post]; exact List.getElem_mem ..)
            try have hi2b : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 :=
              hs1b i2 (by rw [i2_post]; exact List.getElem_mem ..)
            first
            | exact hs1b
            | scalar_tac
    exact spec_ok_exists hmain

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
