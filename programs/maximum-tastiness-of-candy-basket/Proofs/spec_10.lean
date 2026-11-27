import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_10` (maximum-tastiness-of-candy-basket).
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

  /-! ### Auxiliary lemmas for `spec_S10` -/

  open Aegis.MaximumTastiness

  /-- Generic loop principle for `Aeneas.Std.loop`: if the body always succeeds, the loop
  invariant is preserved while a measure decreases, and the output condition is established
  on `done`, then the loop terminates and satisfies the output condition. -/
  theorem loop_spec {α β : Type} (body : α → Result (ControlFlow α β))
      (P : α → Prop) (Q : β → Prop) (m : α → Nat)
      (hbody : ∀ a, P a → ∃ r, body a = ok r)
      (hstep : ∀ a, P a → ∀ r, body a = ok r →
        ((∀ a', r = ControlFlow.cont a' → P a' ∧ m a' < m a) ∧
         (∀ b, r = ControlFlow.done b → Q b))) :
      ∀ a, P a → ∃ b, loop body a = ok b ∧ Q b := by
    have key : ∀ k a, m a ≤ k → P a → ∃ b, loop body a = ok b ∧ Q b := by
      intro k
      induction k with
      | zero =>
        intro a ha hP
        obtain ⟨r, hr⟩ := hbody a hP
        rcases r with a' | b
        · obtain ⟨-, hlt⟩ := (hstep a hP _ hr).1 a' rfl
          omega
        · exact ⟨b, by rw [Aeneas.Std.loop.eq_def, hr]; simp, (hstep a hP _ hr).2 b rfl⟩
      | succ k ih =>
        intro a ha hP
        obtain ⟨r, hr⟩ := hbody a hP
        rcases r with a' | b
        · obtain ⟨hP', hlt⟩ := (hstep a hP _ hr).1 a' rfl
          obtain ⟨b, hb, hQ⟩ := ih a' (by omega) hP'
          exact ⟨b, by rw [Aeneas.Std.loop.eq_def, hr]; simpa using hb, hQ⟩
        · exact ⟨b, by rw [Aeneas.Std.loop.eq_def, hr]; simp, (hstep a hP _ hr).2 b rfl⟩
    intro a hP
    exact key (m a) a (le_refl _) hP

  theorem absDiff_nonneg (a b : ℤ) : 0 ≤ absDiff a b := by
    unfold absDiff; simp

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    unfold absDiff
    rw [show a - b = -(b - a) by ring, Int.natAbs_neg]

  theorem absDiff_eq_zero_iff {a b : ℤ} : absDiff a b = 0 ↔ a = b := by
    unfold absDiff
    rw [Int.ofNat_eq_zero, Int.natAbs_eq_zero]
    exact sub_eq_zero

  theorem absDiff_of_le {a b : ℤ} (h : a ≤ b) : absDiff a b = b - a := by
    unfold absDiff
    have h0 : (0 : ℤ) ≤ b - a := by linarith
    rw [show a - b = -(b - a) by ring, Int.natAbs_neg, Int.natAbs_of_nonneg h0]

  /-- The gap between the `(j+1)`-th and the `j`-th entry of a list of integers. -/
  def gapZ (s : List ℤ) (j : ℕ) : ℤ := s.getD (j + 1) 0 - s.getD j 0

  /-- The gap between the `(j+1)`-th and the `j`-th entry of a list of prices. -/
  def gapAt (s : List I64) (j : ℕ) : ℤ := (s.getD (j + 1) 0#i64).val - (s.getD j 0#i64).val

  theorem mem_pairDistsOn {l : List ℤ} {S : Finset ℕ} {d : ℤ} :
      d ∈ pairDistsOn l S ↔
        ∃ i ∈ S, ∃ j ∈ S, i < j ∧ absDiff (l.getD i 0) (l.getD j 0) = d := by
    unfold pairDistsOn
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hd⟩
      simp only [Finset.mem_filter] at hp
      have hp' : p.1 ∈ S ∧ p.2 ∈ S := by simpa using hp.1
      exact ⟨p.1, hp'.1, p.2, hp'.2, hp.2, hd⟩
    · rintro ⟨i, hi, j, hj, hlt, hd⟩
      exact ⟨(i, j), by simp [hi, hj, hlt], hd⟩

  theorem pairDistsOn_nonneg (l : List ℤ) (S : Finset ℕ) :
      ∀ d ∈ pairDistsOn l S, 0 ≤ d := by
    intro d hd
    rw [mem_pairDistsOn] at hd
    obtain ⟨i, -, j, -, -, rfl⟩ := hd
    exact absDiff_nonneg _ _

  theorem tastinessOn_nonneg (l : List ℤ) (S : Finset ℕ) : 0 ≤ tastinessOn l S := by
    unfold tastinessOn
    split
    · exact Finset.le_min' _ _ 0 (pairDistsOn_nonneg l S)
    · exact le_refl 0

  theorem tastinessOn_le {l : List ℤ} {S : Finset ℕ} {d : ℤ} (h : d ∈ pairDistsOn l S) :
      tastinessOn l S ≤ d := by
    unfold tastinessOn
    split
    · exact Finset.min'_le _ d h
    · rename_i hn
      exact absurd ⟨d, h⟩ hn

  theorem le_tastinessOn {l : List ℤ} {S : Finset ℕ} {c : ℤ}
      (hne : (pairDistsOn l S).Nonempty) (h : ∀ d ∈ pairDistsOn l S, c ≤ d) :
      c ≤ tastinessOn l S := by
    unfold tastinessOn
    split
    · exact Finset.le_min' _ _ c h
    · rename_i hn
      exact absurd hne hn

  theorem mem_kSelections {l : List ℤ} {k : ℕ} {S : Finset ℕ} :
      S ∈ kSelections l k ↔ S ⊆ Finset.range l.length ∧ S.card = k := by
    simp [kSelections]

  theorem kSelections_full (l : List ℤ) :
      kSelections l l.length = {Finset.range l.length} := by
    ext S
    rw [mem_kSelections, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
    · rintro rfl
      exact ⟨le_refl _, by simp⟩

  theorem maxTastiness_full (l : List ℤ) :
      maxTastiness l l.length = tastinessOn l (Finset.range l.length) := by
    have hne : (kSelections l l.length).Nonempty :=
      ⟨Finset.range l.length, by rw [kSelections_full]; simp⟩
    unfold maxTastiness
    rw [dif_pos hne]
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨S, hS, rfl⟩ := hy
      rw [kSelections_full, Finset.mem_singleton] at hS
      rw [hS]
    · apply Finset.le_max'
      rw [Finset.mem_image]
      exact ⟨_, by rw [kSelections_full]; simp, rfl⟩

  /-- The set of absolute differences of *distinct* values occurring in `l`. -/
  def valueDists (l : List ℤ) : Finset ℤ :=
    ((l.toFinset.product l.toFinset).filter (fun p => p.1 < p.2)).image
      (fun p => absDiff p.1 p.2)

  theorem pairDistsOn_nonempty (l : List ℤ) (h2 : 2 ≤ l.length) :
      (pairDistsOn l (Finset.range l.length)).Nonempty := by
    refine ⟨absDiff (l.getD 0 0) (l.getD 1 0), ?_⟩
    rw [mem_pairDistsOn]
    exact ⟨0, Finset.mem_range.mpr (by omega), 1, Finset.mem_range.mpr (by omega), by omega,
      rfl⟩

  theorem min'_proof_irrel {A : Finset ℤ} (h1 h2 : A.Nonempty) : A.min' h1 = A.min' h2 :=
    le_antisymm (Finset.min'_le A (A.min' h2) (Finset.min'_mem A h2))
      (Finset.min'_le A (A.min' h1) (Finset.min'_mem A h1))

  theorem min'_eq_of_eq {A B : Finset ℤ} (hAB : A = B) (hA : A.Nonempty) (hB : B.Nonempty) :
      A.min' hA = B.min' hB := by
    cases hAB
    exact min'_proof_irrel hA hB

  theorem tastinessOn_eq_min' {l : List ℤ} {S : Finset ℕ}
      (h : (pairDistsOn l S).Nonempty) :
      tastinessOn l S = (pairDistsOn l S).min' h := by
    unfold tastinessOn
    split
    · rename_i h'; exact min'_proof_irrel h' h
    · rename_i h'; exact absurd h h'

  theorem zero_mem_pairDistsOn_of_not_nodup {l : List ℤ} (hn : ¬ l.Nodup) :
      0 ∈ pairDistsOn l (Finset.range l.length) := by
    rw [List.nodup_iff_getElem?_ne_getElem?] at hn
    push Not at hn
    obtain ⟨i, j, hij, hj, heq⟩ := hn
    have hi : i < l.length := lt_trans hij hj
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at heq
    have he : l[i]'(hi) = l[j]'(hj) := Option.some.inj heq
    rw [mem_pairDistsOn]
    refine ⟨i, Finset.mem_range.mpr hi, j, Finset.mem_range.mpr hj, hij, ?_⟩
    rw [List.getD_eq_getElem l 0 hi, List.getD_eq_getElem l 0 hj]
    exact absDiff_eq_zero_iff.mpr he

  theorem valueDists_subset_pairDists (l : List ℤ) (h2 : 2 ≤ l.length) :
      valueDists l ⊆ pairDistsOn l (Finset.range l.length) := by
    have _ := h2
    intro d hd
    rw [valueDists, Finset.mem_image] at hd
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hd
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    rw [List.mem_toFinset, List.mem_iff_getElem] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    have hdi : l.getD i 0 = l[i] := List.getD_eq_getElem l 0 hi
    have hdj : l.getD j 0 = l[j] := List.getD_eq_getElem l 0 hj
    have hne : i ≠ j := by rintro rfl; exact absurd hab (lt_irrefl _)
    rw [mem_pairDistsOn]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, Finset.mem_range.mpr hi, j, Finset.mem_range.mpr hj, hlt,
        by rw [hdi, hdj]⟩
    · exact ⟨j, Finset.mem_range.mpr hj, i, Finset.mem_range.mpr hi, hlt,
        by rw [hdj, hdi, absDiff_comm]⟩

  theorem pairDists_subset_valueDists (l : List ℤ) (h2 : 2 ≤ l.length) :
      pairDistsOn l (Finset.range l.length) ⊆ valueDists l ∪ {0} := by
    have _ := h2
    intro d hd
    rw [mem_pairDistsOn] at hd
    obtain ⟨i, hi, j, hj, hij, rfl⟩ := hd
    rw [Finset.mem_range] at hi hj
    have hdi : l.getD i 0 = l[i] := List.getD_eq_getElem l 0 hi
    have hdj : l.getD j 0 = l[j] := List.getD_eq_getElem l 0 hj
    have hmem_i : l[i] ∈ l.toFinset := List.mem_toFinset.mpr (List.getElem_mem hi)
    have hmem_j : l[j] ∈ l.toFinset := List.mem_toFinset.mpr (List.getElem_mem hj)
    rw [hdi, hdj, Finset.mem_union]
    rcases lt_trichotomy (l[i]) (l[j]) with hlt | heq | hlt
    · left
      rw [valueDists, Finset.mem_image]
      refine ⟨(l[i], l[j]), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨⟨hmem_i, hmem_j⟩, hlt⟩
    · right
      rw [Finset.mem_singleton]
      exact absDiff_eq_zero_iff.mpr heq
    · left
      rw [valueDists, Finset.mem_image]
      refine ⟨(l[j], l[i]), ?_, absDiff_comm _ _⟩
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨⟨hmem_j, hmem_i⟩, hlt⟩

  theorem pairDistsOn_nodup_eq_valueDists (l : List ℤ) (hn : l.Nodup) (h2 : 2 ≤ l.length) :
      pairDistsOn l (Finset.range l.length) = valueDists l := by
    refine Finset.Subset.antisymm ?_ (valueDists_subset_pairDists l h2)
    intro d hd
    have h := pairDists_subset_valueDists l h2 hd
    rw [Finset.mem_union] at h
    rcases h with h | h
    · exact h
    · exfalso
      rw [Finset.mem_singleton] at h
      rw [h] at hd
      rw [mem_pairDistsOn] at hd
      obtain ⟨i, hi, j, hj, hij, hd0⟩ := hd
      rw [Finset.mem_range] at hi hj
      have he : l[i] = l[j] := by
        rw [List.getD_eq_getElem l 0 hi, List.getD_eq_getElem l 0 hj] at hd0
        exact absDiff_eq_zero_iff.mp hd0
      have hinj := hn.getElem_inj_iff (hi := hi) (hj := hj)
      exact absurd (hinj.mp he) (by omega)

  theorem tastinessOn_perm (l₁ l₂ : List ℤ) (h : l₁.Perm l₂) (h2 : 2 ≤ l₂.length) :
      tastinessOn l₁ (Finset.range l₁.length) = tastinessOn l₂ (Finset.range l₂.length) := by
    have h2' : 2 ≤ l₁.length := by rw [h.length_eq]; exact h2
    have hsetV : valueDists l₁ = valueDists l₂ := by
      simp only [valueDists]
      rw [List.toFinset_eq_of_perm l₁ l₂ h]
    have hne1 : (pairDistsOn l₁ (Finset.range l₁.length)).Nonempty :=
      pairDistsOn_nonempty l₁ h2'
    have hne2 : (pairDistsOn l₂ (Finset.range l₂.length)).Nonempty :=
      pairDistsOn_nonempty l₂ h2
    by_cases hnd : l₂.Nodup
    · have hnd1 : l₁.Nodup := h.nodup_iff.mpr hnd
      have hS : pairDistsOn l₁ (Finset.range l₁.length)
          = pairDistsOn l₂ (Finset.range l₂.length) := by
        rw [pairDistsOn_nodup_eq_valueDists l₁ hnd1 h2',
          pairDistsOn_nodup_eq_valueDists l₂ hnd h2, hsetV]
      have hmin := min'_eq_of_eq hS hne1 hne2
      rw [tastinessOn_eq_min' hne1, tastinessOn_eq_min' hne2]
      exact hmin
    · have hnd1 : ¬ l₁.Nodup := fun h1 => hnd (h.nodup_iff.mp h1)
      have e1 : tastinessOn l₁ (Finset.range l₁.length) = 0 :=
        le_antisymm (tastinessOn_le (zero_mem_pairDistsOn_of_not_nodup hnd1))
          (tastinessOn_nonneg _ _)
      have e2 : tastinessOn l₂ (Finset.range l₂.length) = 0 :=
        le_antisymm (tastinessOn_le (zero_mem_pairDistsOn_of_not_nodup hnd))
          (tastinessOn_nonneg _ _)
      rw [e1, e2]

  theorem pairwise_getElem_le {s : List ℤ} (hs : s.Pairwise (· ≤ ·)) {i j : ℕ} (hij : i ≤ j)
      (hj : j < s.length) : s[i] ≤ s[j] := by
    exact List.Pairwise.rel_get_of_le hs hij

  theorem sorted_pair_ge {s : List ℤ} (hs : s.Pairwise (· ≤ ·)) {c : ℤ}
      (hlo : ∀ j, j + 1 < s.length → c ≤ gapZ s j)
      {i j : ℕ} (hij : i < j) (hj : j < s.length) : c ≤ s.getD j 0 - s.getD i 0 := by
    have key : ∀ t, i + 1 ≤ t → t < s.length → c ≤ s.getD t 0 - s.getD i 0 := by
      intro t hit
      induction t, hit using Nat.le_induction with
      | base =>
        intro ht
        exact hlo i ht
      | succ n hmn ih =>
        intro ht
        have hn : n < s.length := by omega
        have hprev := ih hn
        have hmono : s.getD n 0 ≤ s.getD (n + 1) 0 := by
          rw [List.getD_eq_getElem s 0 hn, List.getD_eq_getElem s 0 ht]
          exact List.Pairwise.rel_get_of_le hs (Nat.le_succ n)
        linarith
    exact key j (by omega) hj

  theorem tastinessOn_sorted_eq (s : List ℤ) (hs : s.Pairwise (· ≤ ·)) (h2 : 2 ≤ s.length)
      (c : ℤ) (hlo : ∀ j, j + 1 < s.length → c ≤ gapZ s j)
      (hhi : ∃ j, j + 1 < s.length ∧ gapZ s j = c) :
      tastinessOn s (Finset.range s.length) = c := by
    have _ := h2
    obtain ⟨j0, hj0, hgap⟩ := hhi
    have hmem : c ∈ pairDistsOn s (Finset.range s.length) := by
      rw [mem_pairDistsOn]
      refine ⟨j0, Finset.mem_range.mpr (by omega), j0 + 1, Finset.mem_range.mpr hj0,
        by omega, ?_⟩
      have e1 : s.getD j0 0 = s[j0]'(by omega) := List.getD_eq_getElem s 0 (by omega)
      have e2 : s.getD (j0 + 1) 0 = s[j0 + 1]'(hj0) := List.getD_eq_getElem s 0 hj0
      have hle : s[j0]'(by omega) ≤ s[j0 + 1]'(hj0) :=
        List.Pairwise.rel_get_of_le hs (Nat.le_succ j0)
      rw [gapZ, e1, e2] at hgap
      rw [e1, e2, absDiff_of_le hle, hgap]
    have hne : (pairDistsOn s (Finset.range s.length)).Nonempty := ⟨c, hmem⟩
    rw [tastinessOn_eq_min' hne]
    refine le_antisymm (Finset.min'_le _ c hmem) (Finset.le_min' _ hne c ?_)
    intro d hd
    rw [mem_pairDistsOn] at hd
    obtain ⟨i, hi, j, hj, hij, rfl⟩ := hd
    rw [Finset.mem_range] at hi hj
    have hle : s.getD i 0 ≤ s.getD j 0 := by
      rw [List.getD_eq_getElem s 0 hi, List.getD_eq_getElem s 0 hj]
      exact List.Pairwise.rel_get_of_le hs hij.le
    rw [absDiff_of_le hle]
    exact sorted_pair_ge hs hlo hij hj

  /-! ### Facts about the extracted program -/

  theorem Slice.index_usize_eq (s : Slice I64) (i : Usize) (h : i.val < s.length) :
      s.index_usize i = ok s.val[i.val] := by
    unfold Slice.index_usize
    rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h]

  /-- The comparison function used by the extracted insertion sort: it compares the
  underlying integer values with Lean's `compare`. -/
  theorem cmp_OrdI64_eq (x y : I64) :
      core.cmp.OrdI64.cmp x y = ok (compare x.val y.val) := by
    simp [core.cmp.impls.OrdI64.cmp]

  /-- Insertion of `x` into an already sorted list: the insertion sort succeeds, the result
  is a permutation of `x :: ys` and it is again sorted. -/
  theorem sortInsert_spec (x : I64) (ys : List I64)
      (hs : ys.Pairwise (fun a b => a.val ≤ b.val)) :
      ∃ r, AegisShim.sortInsert core.cmp.OrdI64.cmp x ys = ok r ∧ r.Perm (x :: ys) ∧
        r.Pairwise (fun a b => a.val ≤ b.val) := by
    induction ys with
    | nil => exact ⟨[x], by simp [AegisShim.sortInsert], List.Perm.refl _, by simp⟩
    | cons y ys ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      obtain ⟨r, hr, hperm, hsorted⟩ := ih htail
      cases h : compare x.val y.val
      · refine ⟨x :: y :: ys,
          by simp [AegisShim.sortInsert, core.cmp.impls.OrdI64.cmp, h], List.Perm.refl _, ?_⟩
        have hxy : x.val ≤ y.val := le_of_lt (compare_lt_iff_lt.mp h)
        rw [List.pairwise_cons]
        refine ⟨fun z hz => ?_, hs⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact le_trans hxy (hhead z hz)
      · refine ⟨x :: y :: ys,
          by simp [AegisShim.sortInsert, core.cmp.impls.OrdI64.cmp, h], List.Perm.refl _, ?_⟩
        have hxy : x.val = y.val := compare_eq_iff_eq.mp h
        rw [List.pairwise_cons]
        refine ⟨fun z hz => ?_, hs⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact le_of_eq hxy
        · exact le_trans (le_of_eq hxy) (hhead z hz)
      · have hxy : y.val < x.val := compare_gt_iff_gt.mp h
        refine ⟨y :: r, by simp [AegisShim.sortInsert, core.cmp.impls.OrdI64.cmp, h, hr],
          (hperm.cons y).trans (List.Perm.swap x y ys), ?_⟩
        rw [List.pairwise_cons]
        refine ⟨fun z hz => ?_, hsorted⟩
        have hz' := hperm.mem_iff.mp hz
        rcases List.mem_cons.mp hz' with rfl | hz''
        · exact le_of_lt hxy
        · exact hhead z hz''

  theorem sortList_spec (l : List I64) :
      ∃ l', AegisShim.sortList core.cmp.OrdI64.cmp l = ok l' ∧ l'.Perm l ∧
        l'.Pairwise (fun a b => a.val ≤ b.val) := by
    induction l with
    | nil => exact ⟨[], by simp [AegisShim.sortList], List.Perm.refl _, by simp⟩
    | cons x xs ih =>
      obtain ⟨l', hl', hperm, hsorted⟩ := ih
      obtain ⟨r, hr, hperm', hsorted'⟩ := sortInsert_spec x l' hsorted
      refine ⟨r, ?_, hperm'.trans (hperm.cons x), hsorted'⟩
      simp [AegisShim.sortList, hl', hr]

  theorem Slice.sort_spec (s : Slice I64) :
      ∃ s', alloc.slice.Slice.sort core.cmp.OrdI64 s = ok s' ∧ s'.val.Perm s.val ∧
        s'.val.Pairwise (fun a b => a.val ≤ b.val) := by
    obtain ⟨l', hl', hperm, hsorted⟩ := sortList_spec s.val
    have hb : l'.length ≤ Usize.max := by
      rw [hperm.length_eq]; exact Slice.property s
    refine ⟨Slice.from l' hb, ?_, ?_, ?_⟩
    · simp only [alloc.slice.Slice.sort, hl']
      simp [dite_eq_left hb]
    · simpa using hperm
    · simpa using hsorted

  /-- The consecutive gaps of the list `l` when the element preceding `l` is `prev`. -/
  def gapsConsec : List I64 → I64 → List ℤ
    | [], _ => []
    | x :: xs, prev => (x.val - prev.val) :: gapsConsec xs x

  /-- Simulation of the greedy counting loop `can_make_loop`: the counter after scanning `l`,
  the last accepted price being `prev` and the current counter being `count`. -/
  def scan (l : List I64) (d : I64) (prev : I64) (count : Nat) : Nat :=
    match l with
    | [] => count
    | x :: xs =>
      if d.val ≤ x.val - prev.val then scan xs d x (count + 1) else scan xs d prev count

  theorem scan_ge_count (l : List I64) (d prev : I64) (count : Nat) :
      count ≤ scan l d prev count := by
    induction l generalizing prev count with
    | nil => simp [scan]
    | cons x xs ih =>
      rw [scan]
      split
      · have := ih x (count + 1); omega
      · exact ih prev count

  theorem scan_le (l : List I64) (d prev : I64) (count : Nat) :
      scan l d prev count ≤ count + l.length := by
    induction l generalizing prev count with
    | nil => simp [scan]
    | cons x xs ih =>
      rw [scan]
      split
      · have := ih x (count + 1); simp at *; omega
      · have := ih prev count; simp at *; omega

  theorem scan_eq_iff (l : List I64) (d prev : I64) (count : Nat) :
      scan l d prev count = count + l.length ↔ ∀ g ∈ gapsConsec l prev, d.val ≤ g := by
    induction l generalizing prev count with
    | nil => simp [scan, gapsConsec]
    | cons x xs ih =>
      rw [scan]
      simp only [gapsConsec, List.length_cons, List.mem_cons]
      by_cases hstep : d.val ≤ x.val - prev.val
      · rw [if_pos hstep]
        have e : count + (xs.length + 1) = (count + 1) + xs.length := by omega
        rw [e, ih x (count + 1)]
        constructor
        · intro hall g hg
          rcases hg with rfl | hg
          · exact hstep
          · exact hall g hg
        · intro hall g hg
          exact hall g (Or.inr hg)
      · rw [if_neg hstep]
        have e : count + (xs.length + 1) = count + xs.length + 1 := by omega
        rw [e]
        constructor
        · intro heq
          exfalso
          have := scan_le xs d prev count
          omega
        · intro hall
          exact absurd (hall _ (Or.inl rfl)) hstep

  theorem gapAt_cons_zero (x : I64) (xs : List I64) :
      gapAt (x :: xs) 0 = (xs.getD 0 0#i64).val - x.val := by
    show ((x :: xs).getD (0 + 1) 0#i64).val - ((x :: xs).getD 0 0#i64).val
        = (xs.getD 0 0#i64).val - x.val
    rw [Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ]

  theorem gapAt_cons_succ (x : I64) (xs : List I64) (j : Nat) :
      gapAt (x :: xs) (j + 1) = gapAt xs j := by
    show ((x :: xs).getD (j + 1 + 1) 0#i64).val - ((x :: xs).getD (j + 1) 0#i64).val
        = (xs.getD (j + 1) 0#i64).val - (xs.getD j 0#i64).val
    rw [List.getD_cons_succ, List.getD_cons_succ]

  theorem mem_gapsConsec {l : List I64} {prev : I64} {g : ℤ} :
      g ∈ gapsConsec l prev ↔
        (l ≠ [] ∧ g = (l.getD 0 0#i64).val - prev.val) ∨
          ∃ j, j + 1 < l.length ∧ g = gapAt l j := by
    induction l generalizing prev with
    | nil => simp [gapsConsec]
    | cons x xs ih =>
      rw [show gapsConsec (x :: xs) prev = (x.val - prev.val) :: gapsConsec xs x from rfl,
        List.mem_cons, List.length_cons]
      constructor
      · rintro (h | h)
        · refine Or.inl ⟨by simp, ?_⟩
          rw [h]; simp
        · rcases (ih (prev := x)).mp h with ⟨hne, hg⟩ | ⟨j, hj, hg⟩
          · refine Or.inr ⟨0, ?_, ?_⟩
            · have hpos : 0 < xs.length := by
                cases xs with
                | nil => simp at hne
                | cons y ys => simp
              omega
            · rw [gapAt_cons_zero]; exact hg
          · refine Or.inr ⟨j + 1, ?_, ?_⟩
            · omega
            · rw [gapAt_cons_succ]; exact hg
      · rintro (⟨-, hg⟩ | ⟨j, hj, hg⟩)
        · left; simpa using hg
        · cases j with
          | zero =>
            refine Or.inr ?_
            refine (ih (prev := x)).mpr (Or.inl ⟨?_, ?_⟩)
            · intro hxs; rw [hxs] at hj; simp at hj
            · rw [gapAt_cons_zero] at hg; exact hg
          | succ j' =>
            refine Or.inr ?_
            refine (ih (prev := x)).mpr (Or.inr ⟨j', ?_, ?_⟩)
            · omega
            · rw [gapAt_cons_succ] at hg; exact hg

  theorem mem_gapsConsec_drop_one {L : List I64} (hL : 1 ≤ L.length) {g : ℤ} :
      g ∈ gapsConsec (L.drop 1) L[0] ↔
        ∃ j, j + 1 < L.length ∧ g = gapAt L j := by
    cases L with
    | nil => simp at hL
    | cons x xs =>
      have hd : (x :: xs).drop 1 = xs := rfl
      rw [hd]
      simp only [List.length_cons, List.getElem_cons_zero]
      rw [mem_gapsConsec]
      constructor
      · rintro (⟨hne, hg⟩ | ⟨j, hj, hg⟩)
        · refine ⟨0, ?_, ?_⟩
          · have hpos : 0 < xs.length := by
              cases xs with
              | nil => simp at hne
              | cons y ys => simp
            omega
          · rw [gapAt_cons_zero]; exact hg
        · exact ⟨j + 1, by omega, by rw [gapAt_cons_succ]; exact hg⟩
      · rintro ⟨j, hj, hg⟩
        cases j with
        | zero =>
          refine Or.inl ⟨?_, ?_⟩
          · intro hxs; rw [hxs] at hj; simp at hj
          · rw [gapAt_cons_zero] at hg; exact hg
        | succ j' =>
          exact Or.inr ⟨j', by omega, by rw [gapAt_cons_succ] at hg; exact hg⟩

  theorem cms_I64_sub_eq (x y : I64) (hlo : I64.min ≤ x.val - y.val)
      (hhi : x.val - y.val ≤ I64.max) :
      ∃ r : I64, x - y = ok r ∧ r.val = x.val - y.val := by
    have hmt : -9223372036854775808 ≤ x.val - y.val := by simpa [I64.min_eq] using hlo
    have hlt : x.val - y.val < 9223372036854775808 := by
      have h := hhi; simp only [I64.max_eq] at h; omega
    have hb : IScalar.inBounds IScalarTy.I64 (x.val - y.val) := ⟨hmt, hlt⟩
    have h := IScalar.sub_equiv (ty := IScalarTy.I64) x y
    cases hm : (x - y).match
    · rename_i z
      rw [hm] at h
      exact ⟨z, by simpa using hm, h.2.1⟩
    · rw [hm] at h
      exact h.elim
    · rename_i e k
      cases e
      rw [hm] at h
      exact absurd hb h

  theorem cms_I64_add_eq (x y : I64) (hlo : I64.min ≤ x.val + y.val)
      (hhi : x.val + y.val ≤ I64.max) :
      ∃ r : I64, x + y = ok r ∧ r.val = x.val + y.val := by
    have hmt : -9223372036854775808 ≤ x.val + y.val := by simpa [I64.min_eq] using hlo
    have hlt : x.val + y.val < 9223372036854775808 := by
      have h := hhi; simp only [I64.max_eq] at h; omega
    have hb : IScalar.inBounds IScalarTy.I64 (x.val + y.val) := ⟨hmt, hlt⟩
    have h := IScalar.add_equiv (ty := IScalarTy.I64) x y
    cases hm : (x + y).match
    · rename_i z
      rw [hm] at h
      exact ⟨z, by simpa using hm, h.2.1⟩
    · rw [hm] at h
      exact h.elim
    · rename_i e k
      cases e
      rw [hm] at h
      exact absurd hb h

  theorem cms_Usize_add_eq (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
      ∃ r : Usize, x + y = ok r ∧ r.val = x.val + y.val := by
    have hb : UScalar.inBounds UScalarTy.Usize (x.val + y.val) := by
      have h' : x.val + y.val ≤ UScalar.max UScalarTy.Usize := by
        rw [UScalar.max_USize_eq]; exact h
      simp only [UScalar.inBounds, UScalar.max] at h' ⊢
      have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
      omega
    have heq := UScalar.add_equiv (ty := UScalarTy.Usize) x y
    cases hm : (x + y).match
    · rename_i z
      rw [hm] at heq
      exact ⟨z, by simpa using hm, heq.2.1⟩
    · rw [hm] at heq
      exact heq.elim
    · rename_i e k
      cases e
      rw [hm] at heq
      exact absurd hb heq

  theorem can_make_body_done' (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val ≤ 1000000000)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hge : k.val ≤ count.val + 1) :
      can_make_loop.body s k d n count last i = ok (ControlFlow.done true) := by
    have h1i : (1#i64).val = 1 := by simp
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := cms_I64_sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := cms_I64_add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · rfl
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
      · exfalso
        simp_all
    · exfalso
      simp_all

  theorem can_make_body_cont' (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val ≤ 1000000000)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hlt : count.val + 1 < k.val) :
      ∃ (c' : I64) (u' : Usize), c'.val = count.val + 1 ∧ u'.val = i.val + 1 ∧
        can_make_loop.body s k d n count last i =
          ok (ControlFlow.cont (c', s.val[i.val], u')) := by
    have h1i : (1#i64).val = 1 := by simp
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii s.property)
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := cms_I64_sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := cms_I64_add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
        · rw [h1i] at hc1v
          obtain ⟨u1, hu1, hu1v⟩ := cms_Usize_add_eq i 1#usize hub
          rw [hu1]
          simp only [bind_ok]
          exact ⟨c1, u1, hc1v, hu1v, rfl⟩
      · exfalso
        simp_all <;> omega
    · exfalso
      simp_all <;> omega

  theorem can_make_body_skip' (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hstep : ¬ d.val ≤ s.val[i.val].val - last.val) :
      ∃ u' : Usize, u'.val = i.val + 1 ∧
        can_make_loop.body s k d n count last i =
          ok (ControlFlow.cont (count, last, u')) := by
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii s.property)
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := cms_I64_sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · exfalso
        simp_all <;> omega
      · obtain ⟨u1, hu1, hu1v⟩ := cms_Usize_add_eq i 1#usize hub
        rw [hu1]
        simp only [bind_ok]
        exact ⟨u1, hu1v, rfl⟩
    · exfalso
      simp_all

  theorem can_make_spec (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length) (hlen : s.length ≤ 100000)
      (hk : k.val = (s.length : ℤ)) (hk2 : 2 ≤ k.val)
      (hs : s.val.Pairwise (fun a b => a.val ≤ b.val))
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ b, can_make s k d = ok b ∧
        (b = true ↔ ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g) := by
    have hk1 : ¬ (k <= 1#i64) := by
      intro h
      have h1 : k.val ≤ 1 := by simpa using h
      omega
    set n : Usize := Slice.len s with hn
    have hnval : n.val = s.length := by rw [hn]; exact Slice.len_val s
    have hslen : s.val.length = s.length := rfl
    set M : Nat := scan (s.val.drop 1) d s.val[0] 1 with hM
    have hscan1 : 1 + (s.val.drop 1).length = s.length := by
      rw [List.length_drop, hslen]; omega
    have hMle : M ≤ s.length := by
      rw [hM]
      have h := scan_le (s.val.drop 1) d s.val[0] 1
      rw [hscan1] at h
      exact h
    have hMeq : M = s.length ↔ ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g := by
      have h1 : (M = s.length) ↔
          (scan (s.val.drop 1) d s.val[0] 1 = 1 + (s.val.drop 1).length) := by
        rw [hM, hscan1]
      rw [h1, scan_eq_iff]
    let P : I64 × I64 × Usize → Prop := fun p =>
      1 ≤ p.1.val ∧ p.1.val ≤ k.val ∧ p.2.2.val ≤ n.val ∧
        1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000 ∧
          scan (s.val.drop p.2.2.val) d p.2.1 p.1.toNat = M
    let Q : Bool → Prop := fun b =>
      b = true ↔ ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g
    have hmain : ∀ a : I64 × I64 × Usize, P a →
        ∃ b, loop (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) a = ok b ∧ Q b := by
      refine loop_spec _ P Q (fun p => n.val - p.2.2.val) ?_ ?_
      · rintro ⟨count, last, i⟩ hP
        obtain ⟨hc1, hc2, hi_le, hlast1, hlast2, hscan⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hcnt : count.val ≤ 1000000000 := by omega
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', -, -, hbody⟩ :=
                can_make_body_cont' s k d n count last i hilt hii hnval hbnd hcnt hstepp hlt
              exact ⟨_, hbody⟩
            · have hge : k.val ≤ count.val + 1 := by omega
              exact ⟨_, can_make_body_done' s k d n count last i hilt hii hnval hbnd hcnt
                hstepp hge⟩
          · obtain ⟨u', -, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            exact ⟨_, hbody⟩
        · refine ⟨ControlFlow.done (decide (count >= k)), ?_⟩
          unfold can_make_loop.body
          rw [if_neg (by simpa using hilt)]
      · rintro ⟨count, last, i⟩ hP r hr
        obtain ⟨hc1, hc2, hi_le, hlast1, hlast2, hscan⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hcnt : count.val ≤ 1000000000 := by omega
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', hc'v, hu'v, hbody⟩ :=
                can_make_body_cont' s k d n count last i hilt hii hnval hbnd hcnt hstepp hlt
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.cont (c', s.val[i.val], u') := hr.symm
              subst hrc
              have hc'nat : c'.toNat = count.toNat + 1 := by
                show c'.val.toNat = count.toNat + 1
                have hnn : (0:ℤ) ≤ count.val := by omega
                have h1 : ((count.toNat : ℤ)) = count.val := Int.toNat_of_nonneg hnn
                have hv : c'.val = ((count.toNat + 1 : Nat) : ℤ) := by
                  rw [hc'v, ← h1]; push_cast; ring
                rw [hv, Int.toNat_natCast]
              have hsc : scan (s.val.drop u'.val) d s.val[i.val] c'.toNat = M := by
                rw [hu'v, hc'nat]
                have hd := List.drop_eq_getElem_cons (l := s.val) (i := i.val) hii
                rw [← hscan, hd]
                rw [scan, if_pos hstepp]
              refine ⟨?_, ?_⟩
              · rintro a' heq
                have h2 : a' = (c', s.val[i.val], u') := by
                  have h3 : (c', s.val[i.val], u') = a' := by simpa using heq
                  exact h3.symm
                subst h2
                refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsc⟩, ?_⟩
                · show (1:ℤ) ≤ c'.val; rw [hc'v]; omega
                · rw [hc'v]; omega
                · rw [hu'v]; omega
                · exact hbnd.2.2.1
                · exact hbnd.2.2.2
                · rw [hu'v]; omega
              · rintro b hb
                cases hb
            · have hge : k.val ≤ count.val + 1 := by omega
              have hbody := can_make_body_done' s k d n count last i hilt hii hnval hbnd hcnt
                hstepp hge
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.done true := hr.symm
              subst hrc
              refine ⟨?_, ?_⟩
              · rintro a' heq
                cases heq
              · rintro b hb
                have hbt : b = true := by
                  have h2 : true = b := by simpa using hb
                  exact h2.symm
                subst hbt
                show (true = true ↔ ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g)
                rw [eq_self_iff_true, true_iff]
                apply hMeq.mp
                have hcount_nat : count.val = (count.toNat : ℤ) :=
                  (Int.toNat_of_nonneg (by omega)).symm
                have hsc : scan (s.val.drop (i.val + 1)) d s.val[i.val] (count.toNat + 1) = M := by
                  rw [← hscan]
                  have hd := List.drop_eq_getElem_cons (l := s.val) (i := i.val) hii
                  rw [hd]
                  rw [scan, if_pos hstepp]
                have hge2 : count.toNat + 1 ≤ M := by
                  have := scan_ge_count (s.val.drop (i.val + 1)) d s.val[i.val] (count.toNat + 1)
                  omega
                have hge3 : s.length ≤ count.toNat + 1 := by omega
                omega
          · obtain ⟨u', hu'v, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            rw [hbody] at hr
            simp only [Result.ok.injEq] at hr
            have hrc : r = ControlFlow.cont (count, last, u') := hr.symm
            subst hrc
            have hsc : scan (s.val.drop u'.val) d last count.toNat = M := by
              rw [hu'v]
              have hd := List.drop_eq_getElem_cons (l := s.val) (i := i.val) hii
              rw [← hscan, hd]
              rw [scan, if_neg hstepp]
            refine ⟨?_, ?_⟩
            · rintro a' heq
              have h2 : a' = (count, last, u') := by
                have h3 : (count, last, u') = a' := by simpa using heq
                exact h3.symm
              subst h2
              refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsc⟩, ?_⟩
              · exact hc1
              · exact hc2
              · rw [hu'v]; omega
              · exact hlast1
              · exact hlast2
              · rw [hu'v]; omega
            · rintro b hb
              cases hb
        · have hieq : i.val = s.length := by omega
          have hdrop0 : s.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
          have hMcount : count.toNat = M := by
            have h := hscan
            rw [hdrop0] at h
            simpa [scan] using h
          have hcount_nat : count.val = (count.toNat : ℤ) :=
            (Int.toNat_of_nonneg (by omega)).symm
          have hbd : can_make_loop.body s k d n count last i =
              ok (ControlFlow.done (decide (count >= k))) := by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]
          rw [hbd] at hr
          simp only [Result.ok.injEq] at hr
          have hrc : r = ControlFlow.done (decide (count >= k)) := hr.symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq
            cases heq
          · rintro b hb
            have hbt : b = decide (count >= k) := by
              have h2 : decide (count >= k) = b := by simpa using hb
              exact h2.symm
            subst hbt
            show decide (count >= k) = true ↔
              ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g
            rw [decide_eq_true_iff]
            show k.val ≤ count.val ↔ ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g
            have key : k.val ≤ count.val ↔ M = s.length := by
              rw [hk, hcount_nat, hMcount]
              constructor <;> intro h <;> omega
            rw [key, hMeq]
    have hP0 : P (1#i64, s.val[0], 1#usize) := by
      have h1 : (1#i64).val = 1 := by simp
      have h2 : (1#usize).val = 1 := by simp
      have h3 : (1#i64).toNat = 1 := by simp
      have h4 : 1 ≤ s.val[0].val ∧ s.val[0].val ≤ 1000000000 :=
        hvals _ (List.getElem_mem (by omega : 0 < s.val.length))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (1:ℤ) ≤ (1#i64).val; rw [h1]
      · show (1#i64).val ≤ k.val; rw [h1]; omega
      · show (1#usize).val ≤ n.val; rw [h2]; omega
      · show 1 ≤ s.val[0].val; exact h4.1
      · show s.val[0].val ≤ 1000000000; exact h4.2
      · show scan (s.val.drop (1#usize).val) d s.val[0] (1#i64).toNat = M
        rw [h2, h3]
    obtain ⟨b, hb, hQ⟩ := hmain (1#i64, s.val[0], 1#usize) hP0
    refine ⟨b, ?_, hQ⟩
    have hcan : can_make s k d = (do let last ← s.index_usize 0#usize; can_make_loop s k d (Slice.len s) 1#i64 last 1#usize) := by
      simp [can_make, hk1]
    rw [hcan]
    rw [show s.index_usize 0#usize = ok s.val[0] from
      Slice.index_usize_eq s 0#usize (by
        have h0 : (0#usize).val = 0 := by simp
        omega)]
    simp only [bind_ok]
    rw [← hn]
    exact hb

  theorem pairwise_i64_getElem_le {s : List I64} (hs : s.Pairwise (fun a b => a.val ≤ b.val))
      {i j : ℕ} (hij : i ≤ j) (hj : j < s.length) : s[i].val ≤ s[j].val := by
    exact List.Pairwise.rel_get_of_le hs hij

  theorem I64.sub_eq (x y : I64) (hlo : I64.min ≤ x.val - y.val) (hhi : x.val - y.val ≤ I64.max) :
      ∃ r : I64, x - y = ok r ∧ r.val = x.val - y.val := by
    have hmt : -9223372036854775808 ≤ x.val - y.val := by simpa [I64.min_eq] using hlo
    have hlt : x.val - y.val < 9223372036854775808 := by
      have h := hhi; simp only [I64.max_eq] at h; omega
    have hb : IScalar.inBounds IScalarTy.I64 (x.val - y.val) := ⟨hmt, hlt⟩
    have h := IScalar.sub_equiv (ty := IScalarTy.I64) x y
    cases hm : (x - y).match
    · rename_i z
      rw [hm] at h
      exact ⟨z, by simpa using hm, h.2.1⟩
    · rw [hm] at h
      exact h.elim
    · rename_i e k
      cases e
      rw [hm] at h
      exact absurd hb h

  theorem I64.add_eq (x y : I64) (hlo : I64.min ≤ x.val + y.val) (hhi : x.val + y.val ≤ I64.max) :
      ∃ r : I64, x + y = ok r ∧ r.val = x.val + y.val := by
    have hmt : -9223372036854775808 ≤ x.val + y.val := by simpa [I64.min_eq] using hlo
    have hlt : x.val + y.val < 9223372036854775808 := by
      have h := hhi; simp only [I64.max_eq] at h; omega
    have hb : IScalar.inBounds IScalarTy.I64 (x.val + y.val) := ⟨hmt, hlt⟩
    have h := IScalar.add_equiv (ty := IScalarTy.I64) x y
    cases hm : (x + y).match
    · rename_i z
      rw [hm] at h
      exact ⟨z, by simpa using hm, h.2.1⟩
    · rw [hm] at h
      exact h.elim
    · rename_i e k
      cases e
      rw [hm] at h
      exact absurd hb h

  theorem Usize.sub_eq (x y : Usize) (h : y.val ≤ x.val) :
      ∃ r : Usize, x - y = ok r ∧ r.val = x.val - y.val := by
    have heq := UScalar.sub_equiv (ty := UScalarTy.Usize) x y
    cases hm : (x - y).match
    · rename_i z
      rw [hm] at heq
      refine ⟨z, by simpa using hm, ?_⟩
      omega
    · rw [hm] at heq
      exact heq.elim
    · rename_i e k
      cases e
      rw [hm] at heq
      omega

  theorem Usize.add_eq (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
      ∃ r : Usize, x + y = ok r ∧ r.val = x.val + y.val := by
    have hb : UScalar.inBounds UScalarTy.Usize (x.val + y.val) := by
      have h' : x.val + y.val ≤ UScalar.max UScalarTy.Usize := by
        rw [UScalar.max_USize_eq]; exact h
      simp only [UScalar.inBounds, UScalar.max] at h' ⊢
      have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
      omega
    have heq := UScalar.add_equiv (ty := UScalarTy.Usize) x y
    cases hm : (x + y).match
    · rename_i z
      rw [hm] at heq
      exact ⟨z, by simpa using hm, heq.2.1⟩
    · rw [hm] at heq
      exact heq.elim
    · rename_i e k
      cases e
      rw [hm] at heq
      exact absurd hb heq

  /-- One step of the greedy counting loop, in the case where the current element is accepted
  and the counter reaches `k`: the loop stops with `true`. -/
  theorem can_make_body_done (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val ≤ 1000000000)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hge : k.val ≤ count.val + 1) :
      can_make_loop.body s k d n count last i = ok (ControlFlow.done true) := by
    have h1i : (1#i64).val = 1 := by simp
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := I64.sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := I64.add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · rfl
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
      · exfalso
        simp_all
    · exfalso
      simp_all

  /-- One step of the greedy counting loop, in the case where the current element is accepted
  and the counter stays below `k`: the loop continues. -/
  theorem can_make_body_cont (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val ≤ 1000000000)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hlt : count.val + 1 < k.val) :
      ∃ (c' : I64) (u' : Usize), c'.val = count.val + 1 ∧ u'.val = i.val + 1 ∧
        can_make_loop.body s k d n count last i =
          ok (ControlFlow.cont (c', s.val[i.val], u')) := by
    have h1i : (1#i64).val = 1 := by simp
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii s.property)
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := I64.sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := I64.add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
        · rw [h1i] at hc1v
          obtain ⟨u1, hu1, hu1v⟩ := Usize.add_eq i 1#usize hub
          rw [hu1]
          simp only [bind_ok]
          exact ⟨c1, u1, hc1v, hu1v, rfl⟩
      · exfalso
        simp_all <;> omega
    · exfalso
      simp_all <;> omega

  /-- One step of the greedy counting loop, in the case where the current element is rejected:
  the loop continues with the same counter and last accepted price. -/
  theorem can_make_body_skip (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hstep : ¬ d.val ≤ s.val[i.val].val - last.val) :
      ∃ u' : Usize, u'.val = i.val + 1 ∧
        can_make_loop.body s k d n count last i =
          ok (ControlFlow.cont (count, last, u')) := by
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii s.property)
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := I64.sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · exfalso
        simp_all <;> omega
      · obtain ⟨u1, hu1, hu1v⟩ := Usize.add_eq i 1#usize hub
        rw [hu1]
        simp only [bind_ok]
        exact ⟨u1, hu1v, rfl⟩
    · exfalso
      simp_all

  /-- `Vec.push`, in equational form. -/
  theorem vec_push_eq {α : Type} (v : alloc.vec.Vec α) (x : α)
      (h : v.val.length < Usize.max) :
      ∃ v' : alloc.vec.Vec α, alloc.vec.Vec.push v x = ok v' ∧ v'.val = v.val ++ [x] := by
    have hlen : (v.val ++ [x]).length ≤ Usize.max := by
      have := alloc.vec.Vec.property v
      simp only [List.length_append, List.length_singleton]
      omega
    refine ⟨alloc.vec.Vec.from (v.val ++ [x]) hlen, ?_, alloc.vec.Vec.from_val _ _⟩
    unfold alloc.vec.Vec.push
    simp only [List.concat_eq_append]
    rw [dif_pos (by simp only [decide_eq_true_eq, Bool.or_eq_true]; omega)]

  /-- One step of the copy loop `maximum_tastiness_loop0` when the index is still in range:
  the element is appended and the index is incremented. -/
  theorem loop0_body_cont (price : Slice I64) (n : Usize) (acc : alloc.vec.Vec I64) (i : Usize)
      (hlt : i.val < n.val) (hii : i.val < price.length) (hlen : acc.val.length < Usize.max) :
      ∃ (acc' : alloc.vec.Vec I64) (i' : Usize),
        acc'.val = acc.val ++ [price.val[i.val]] ∧ i'.val = i.val + 1 ∧
          maximum_tastiness_loop0.body price n acc i = ok (ControlFlow.cont (acc', i')) := by
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii price.property)
    unfold maximum_tastiness_loop0.body
    split
    · rw [Slice.index_usize_eq price i hii]
      simp only [bind_ok]
      obtain ⟨acc', hacc', hacc'v⟩ := vec_push_eq acc price.val[i.val] hlen
      rw [hacc']
      simp only [bind_ok]
      obtain ⟨i', hi', hi'v⟩ := Usize.add_eq i 1#usize hub
      rw [hi']
      simp only [bind_ok]
      exact ⟨acc', i', hacc'v, by rw [hi'v, h1u], rfl⟩
    · rename_i h
      exact absurd hlt h

  /-- The copy loop stops (with the accumulator) once the index reaches `n`. -/
  theorem loop0_body_done (price : Slice I64) (n : Usize) (acc : alloc.vec.Vec I64) (i : Usize)
      (hge : n.val ≤ i.val) :
      maximum_tastiness_loop0.body price n acc i = ok (ControlFlow.done acc) := by
    unfold maximum_tastiness_loop0.body
    split
    · rename_i h
      simp only [UScalar.lt_equiv] at h
      omega
    · rfl

  /-- The accumulator of the copy loop always satisfies the size invariant of vectors. -/
  theorem loop0_inv_len (price : Slice I64) (n : Usize) (acc : alloc.vec.Vec I64) (i : Usize)
      (hacc : acc.val = price.val.take i.val) (hilt : i.val < n.val)
      (hn : n.val = price.length) : acc.val.length < Usize.max := by
    rw [hacc]
    have h1 : (price.val.take i.val).length ≤ i.val := List.length_take_le i.val price.val
    have h2 : i.val < price.length := by omega
    have h3 : price.length ≤ Usize.max := price.property
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h2 h3)

  theorem maximum_tastiness_loop0_spec (price : Slice I64) (n : Usize)
      (hn : n.val = price.length) :
      ∃ v : alloc.vec.Vec I64,
        maximum_tastiness_loop0 price n (alloc.vec.Vec.new I64) 0#usize = ok v ∧
          v.val = price.val := by
    have key := loop_spec
      (body := fun (p : alloc.vec.Vec I64 × Usize) =>
        maximum_tastiness_loop0.body price n p.1 p.2)
      (P := fun (p : alloc.vec.Vec I64 × Usize) =>
        p.1.val = price.val.take p.2.val ∧ p.2.val ≤ n.val)
      (Q := fun (v : alloc.vec.Vec I64) => v.val = price.val)
      (m := fun (p : alloc.vec.Vec I64 × Usize) => n.val - p.2.val)
      (fun p hP => by
        obtain ⟨hacc, hile⟩ := hP
        by_cases hlt : p.2.val < n.val
        · have hlen := loop0_inv_len price n p.1 p.2 hacc hlt hn
          obtain ⟨acc', i', -, -, hbody⟩ :=
            loop0_body_cont price n p.1 p.2 hlt (by omega) hlen
          exact ⟨ControlFlow.cont (acc', i'), hbody⟩
        · exact ⟨ControlFlow.done p.1, loop0_body_done price n p.1 p.2 (by omega)⟩)
      (fun p hP r hr => by
        obtain ⟨hacc, hile⟩ := hP
        by_cases hlt : p.2.val < n.val
        · have hlen := loop0_inv_len price n p.1 p.2 hacc hlt hn
          obtain ⟨acc', i', hacc', hi', hbody⟩ :=
            loop0_body_cont price n p.1 p.2 hlt (by omega) hlen
          have hp2 : p.2.val < price.length := by omega
          have htake : acc'.val = price.val.take i'.val := by
            rw [hacc', hi', hacc]
            exact List.take_append_getElem (l := price.val) (i := p.2.val) hp2
          have hile' : i'.val ≤ n.val := by rw [hi']; omega
          rcases r with a2 | b2
          · refine ⟨?_, ?_⟩
            · intro a' ha'
              cases ha'
              rw [hbody] at hr
              cases Result.ok_injective hr
              exact ⟨⟨htake, hile'⟩, by dsimp only; omega⟩
            · intro b hb
              cases hb
          · refine ⟨?_, ?_⟩
            · intro a' ha'
              cases ha'
            · intro b hb
              cases hb
              rw [hbody] at hr
              cases Result.ok_injective hr
        · refine ⟨?_, ?_⟩
          · intro a' ha'
            cases ha'
            rw [loop0_body_done price n p.1 p.2 (by omega)] at hr
            cases Result.ok_injective hr
          · intro b hb
            cases hb
            rw [loop0_body_done price n p.1 p.2 (by omega)] at hr
            cases Result.ok_injective hr
            rw [hacc, show p.2.val = n.val from by omega, hn]
            exact List.take_length)
    obtain ⟨v, hv, hQ⟩ := key (alloc.vec.Vec.new I64, 0#usize) ⟨by simp, by simp⟩
    exact ⟨v, by simpa [maximum_tastiness_loop0] using hv, hQ⟩

  /-- `can_make` never fails when `1 < k`. -/
  theorem can_make_ok_of_gt (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length) (hlen : s.length ≤ 100000)
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hkle : ¬ (k.val ≤ 1)) :
      ∃ b, can_make s k d = ok b := by
    set n : Usize := Slice.len s with hn
    have hnval : n.val = s.length := by rw [hn]; exact Slice.len_val s
    have hslen : s.val.length = s.length := rfl
    have hmain : ∀ a : I64 × I64 × Usize,
        (1 ≤ a.1.val ∧ a.1.toNat ≤ a.2.2.val ∧ a.2.2.val ≤ n.val ∧
          1 ≤ a.2.1.val ∧ a.2.1.val ≤ 1000000000) →
        ∃ b, loop (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) a = ok b ∧ True := by
      refine loop_spec (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2)
        (fun a : I64 × I64 × Usize =>
          1 ≤ a.1.val ∧ a.1.toNat ≤ a.2.2.val ∧ a.2.2.val ≤ n.val ∧
            1 ≤ a.2.1.val ∧ a.2.1.val ≤ 1000000000)
        (fun _ => True) (fun (p : I64 × I64 × Usize) => n.val - p.2.2.val) ?_ ?_
      · rintro ⟨count, last, i⟩ hP
        obtain ⟨hc1, hcn, hi_le, hlast1, hlast2⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hcnt : count.val ≤ 1000000000 := by
            have h1 : count.val = (count.toNat : ℤ) :=
              (Int.toNat_of_nonneg (by omega)).symm
            omega
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', -, -, hbody⟩ :=
                can_make_body_cont' s k d n count last i hilt hii hnval hbnd hcnt hstepp hlt
              exact ⟨_, hbody⟩
            · exact ⟨_, can_make_body_done' s k d n count last i hilt hii hnval hbnd hcnt
                hstepp (by omega)⟩
          · obtain ⟨u', -, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            exact ⟨_, hbody⟩
        · exact ⟨_, by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]⟩
      · rintro ⟨count, last, i⟩ hP r hr
        obtain ⟨hc1, hcn, hi_le, hlast1, hlast2⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hcnt : count.val ≤ 1000000000 := by
            have h1 : count.val = (count.toNat : ℤ) :=
              (Int.toNat_of_nonneg (by omega)).symm
            omega
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', hc'v, hu'v, hbody⟩ :=
                can_make_body_cont' s k d n count last i hilt hii hnval hbnd hcnt hstepp hlt
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.cont (c', s.val[i.val], u') := hr.symm
              subst hrc
              refine ⟨?_, ?_⟩
              · rintro a' heq
                cases heq
                refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · show (1 : ℤ) ≤ c'.val; rw [hc'v]; omega
                · show c'.toNat ≤ u'.val
                  have h2 : c'.val = ((count.toNat + 1 : ℕ) : ℤ) := by
                    rw [hc'v, show count.val = ((count.toNat : ℕ) : ℤ) from
                      (Int.toNat_of_nonneg (by omega)).symm]
                    push_cast; ring
                  have h3 : c'.toNat = count.toNat + 1 := by
                    show (c'.val).toNat = _
                    rw [h2, Int.toNat_natCast]
                  rw [hu'v]; omega
                · show u'.val ≤ n.val; rw [hu'v]; omega
                · exact hbnd.2.2.1
                · exact hbnd.2.2.2
                · show n.val - u'.val < n.val - i.val; rw [hu'v]; omega
              · rintro b hb
                cases hb
            · have hbody := can_make_body_done' s k d n count last i hilt hii hnval hbnd hcnt
                hstepp (by omega)
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.done true := hr.symm
              subst hrc
              refine ⟨?_, ?_⟩
              · rintro a' heq
                cases heq
              · rintro b hb
                trivial
          · obtain ⟨u', hu'v, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            rw [hbody] at hr
            simp only [Result.ok.injEq] at hr
            have hrc : r = ControlFlow.cont (count, last, u') := hr.symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq
              cases heq
              refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · exact hc1
              · show count.toNat ≤ u'.val; rw [hu'v]; omega
              · show u'.val ≤ n.val; rw [hu'v]; omega
              · exact hlast1
              · exact hlast2
              · show n.val - u'.val < n.val - i.val; rw [hu'v]; omega
            · rintro b hb
              cases hb
        · have hbd : can_make_loop.body s k d n count last i =
              ok (ControlFlow.done (decide (count >= k))) := by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]
          rw [hbd] at hr
          simp only [Result.ok.injEq] at hr
          have hrc : r = ControlFlow.done (decide (count >= k)) := hr.symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq
            cases heq
          · rintro b hb
            trivial
    obtain ⟨b, hb, -⟩ := hmain (1#i64, s.val[0], 1#usize) (by
      have h1 : (1#i64).val = 1 := by simp
      have h2 : (1#usize).val = 1 := by simp
      have h3 : (1#i64).toNat = 1 := by simp
      have h4 : 1 ≤ s.val[0].val ∧ s.val[0].val ≤ 1000000000 :=
        hvals _ (List.getElem_mem (by omega : 0 < s.val.length))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (1 : ℤ) ≤ (1#i64).val; rw [h1]
      · show (1#i64).toNat ≤ (1#usize).val; rw [h2, h3]
      · show (1#usize).val ≤ n.val; rw [h2]; omega
      · exact h4.1
      · exact h4.2)
    refine ⟨b, ?_⟩
    have hk1 : ¬ (k <= 1#i64) := by
      intro h
      have h1 : k.val ≤ 1 := by simpa using h
      exact hkle h1
    have hcan : can_make s k d =
        (do let last ← s.index_usize 0#usize
            can_make_loop s k d (Slice.len s) 1#i64 last 1#usize) := by
      simp [can_make, hk1]
    rw [hcan]
    rw [show s.index_usize 0#usize = ok s.val[0] from
      Slice.index_usize_eq s 0#usize (by
        have h0 : (0#usize).val = 0 := by simp
        omega)]
    simp only [bind_ok]
    rw [← hn]
    exact hb

  /-- `can_make` never fails (for arbitrary `k`). -/
  theorem can_make_ok_all (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length) (hlen : s.length ≤ 100000)
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ b, can_make s k d = ok b := by
    by_cases hkle : k.val ≤ 1
    · refine ⟨true, ?_⟩
      have hkk : k <= 1#i64 := by simpa using hkle
      simp [can_make, hkk]
    · exact can_make_ok_of_gt s k d hne hlen hvals hkle

  /-- `can_make` never fails, for any required number of picks in range. -/
  theorem can_make_ok (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length) (hlen : s.length ≤ 100000)
      (hklo : 2 ≤ k.val) (hkhi : k.val ≤ (s.length : ℤ))
      (hs : s.val.Pairwise (fun a b => a.val ≤ b.val))
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ b, can_make s k d = ok b :=
    can_make_ok_all s k d hne hlen hvals

  /-- If no two prices are at distance at least `d`, the greedy counting loop accepts at most
  one price, so `can_make` answers `false` (for `k ≥ 2`). -/
  theorem can_make_false_of_large (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length) (hk2 : 2 ≤ k.val)
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : ∀ x ∈ s.val, ∀ y ∈ s.val, x.val - y.val < d.val) :
      can_make s k d = ok false := by
    have hk1 : ¬ (k <= 1#i64) := by
      intro h
      have h1 : k.val ≤ 1 := by simpa using h
      omega
    set n : Usize := Slice.len s with hn
    have hnval : n.val = s.length := by rw [hn]; exact Slice.len_val s
    let P : I64 × I64 × Usize → Prop := fun p =>
      p.1.val = 1 ∧ p.2.1 ∈ s.val ∧ 1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000 ∧
        p.2.2.val ≤ n.val
    let Q : Bool → Prop := fun b => b = false
    have hsmall : ∀ x ∈ s.val, ∀ y ∈ s.val, ¬ (d.val ≤ x.val - y.val) := by
      intro x hx y hy
      have := hd x hx y hy
      omega
    have hmain : ∀ a : I64 × I64 × Usize, P a →
        ∃ b, loop (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) a = ok b ∧ Q b := by
      refine loop_spec (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) P Q
        (fun p : I64 × I64 × Usize => n.val - p.2.2.val) ?_ ?_
      · rintro ⟨count, last, i⟩ hP
        obtain ⟨hc, hlastmem, hlast1, hlast2, hi_le⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hstep := hsmall (s.val[i.val]) (List.getElem_mem hii) last hlastmem
          obtain ⟨u', -, hbody⟩ :=
            can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstep
          exact ⟨_, hbody⟩
        · exact ⟨_, by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]⟩
      · rintro ⟨count, last, i⟩ hP r hr
        obtain ⟨hc, hlastmem, hlast1, hlast2, hi_le⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          have hstep := hsmall (s.val[i.val]) (List.getElem_mem hii) last hlastmem
          obtain ⟨u', hu'v, hbody⟩ :=
            can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstep
          rw [hbody] at hr
          simp only [Result.ok.injEq] at hr
          have hrc : r = ControlFlow.cont (count, last, u') := hr.symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq
            have h2 : a' = (count, last, u') := by
              have h3 : (count, last, u') = a' := by simpa using heq
              exact h3.symm
            subst h2
            exact ⟨⟨hc, hlastmem, hlast1, hlast2, by rw [hu'v]; omega⟩, by
              show n.val - u'.val < n.val - i.val
              rw [hu'v]; omega⟩
          · rintro b hb
            cases hb
        · have hbd : can_make_loop.body s k d n count last i =
              ok (ControlFlow.done (decide (count >= k))) := by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]
          rw [hbd] at hr
          simp only [Result.ok.injEq] at hr
          have hrc : r = ControlFlow.done (decide (count >= k)) := hr.symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq
            cases heq
          · rintro b hb
            have hbt : b = decide (count >= k) := by
              have h2 : decide (count >= k) = b := by simpa using hb
              exact h2.symm
            subst hbt
            show decide (count >= k) = false
            rw [decide_eq_false_iff_not]
            show ¬ (k.val ≤ count.val)
            rw [hc]
            omega
    have hP0 : P (1#i64, s.val[0], 1#usize) := by
      have h1 : (1#i64).val = 1 := by simp
      have h2 : (1#usize).val = 1 := by simp
      have h4 : s.val[0] ∈ s.val :=
        List.getElem_mem (by rw [show s.val.length = s.length from rfl]; omega)
      refine ⟨h1, h4, (hvals _ h4).1, (hvals _ h4).2, ?_⟩
      show (1#usize).val ≤ n.val
      rw [h2, hnval]
      omega
    obtain ⟨b, hb, hQ⟩ := hmain (1#i64, s.val[0], 1#usize) hP0
    have hcan : can_make s k d =
        (do let last ← s.index_usize 0#usize
            can_make_loop s k d (Slice.len s) 1#i64 last 1#usize) := by
      simp [can_make, hk1]
    rw [hcan]
    rw [show s.index_usize 0#usize = ok s.val[0] from
      Slice.index_usize_eq s 0#usize (by
        have h0 : (0#usize).val = 0 := by simp
        omega)]
    simp only [bind_ok]
    rw [← hn]
    rw [show can_make_loop s k d n 1#i64 s.val[0] 1#usize =
        loop (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) (1#i64, s.val[0], 1#usize) from rfl]
    rw [hb, hQ]

  /-- Elementary bounds for the truncated division by two of a positive integer. -/
  theorem tdiv_two_bounds {x : ℤ} (hx : 2 ≤ x) : 0 < x.tdiv 2 ∧ x.tdiv 2 < x := by
    have h0 : 0 ≤ x := by omega
    have hr0 : 0 ≤ x.tmod 2 := Int.tmod_nonneg 2 h0
    have hr2 : x.tmod 2 < 2 := by
      rw [Int.tmod_eq_emod_of_nonneg h0]
      have h := Int.emod_lt x (show (2 : ℤ) ≠ 0 by norm_num)
      simpa using h
    have heq := Int.tmod_add_tdiv_mul x 2
    constructor <;> omega

  /-- One step of the greedy counting loop, in the case where the current element is accepted
  and the counter reaches `k`: the loop stops with `true`.  Variant of `can_make_body_done`
  where the counter is bounded by `k` rather than by the length of the slice. -/
  theorem cm_body_done_k (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val < k.val)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hge : k.val ≤ count.val + 1) :
      can_make_loop.body s k d n count last i = ok (ControlFlow.done true) := by
    have h1i : (1#i64).val = 1 := by simp
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := cms_I64_sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := cms_I64_add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · rfl
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
      · exfalso
        simp_all
    · exfalso
      simp_all

  /-- One step of the greedy counting loop, in the case where the current element is accepted
  and the counter stays below `k`: the loop continues.  Variant of `can_make_body_cont` where
  the counter is bounded by `k` rather than by the length of the slice. -/
  theorem cm_body_cont_k (s : Slice I64) (k d : I64) (n : Usize) (count last : I64)
      (i : Usize) (hilt : i.val < n.val) (hii : i.val < s.length) (hn : n.val = s.length)
      (hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
        s.val[i.val].val ≤ 1000000000)
      (hcnt : count.val < k.val)
      (hstep : d.val ≤ s.val[i.val].val - last.val)
      (hlt : count.val + 1 < k.val) :
      ∃ (c' : I64) (u' : Usize), c'.val = count.val + 1 ∧ u'.val = i.val + 1 ∧
        can_make_loop.body s k d n count last i =
          ok (ControlFlow.cont (c', s.val[i.val], u')) := by
    have h1i : (1#i64).val = 1 := by simp
    have h1u : (1#usize).val = 1 := by simp
    have hub : i.val + (1#usize).val ≤ Usize.max := by
      show i.val + 1 ≤ Usize.max
      exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hii s.property)
    unfold can_make_loop.body
    split
    · rw [Slice.index_usize_eq s i hii]
      simp only [bind_ok]
      obtain ⟨i2, hi2, hi2v⟩ := cms_I64_sub_eq s.val[i.val] last (by scalar_tac) (by scalar_tac)
      rw [hi2]
      simp only [bind_ok]
      split
      · obtain ⟨c1, hc1, hc1v⟩ := cms_I64_add_eq count 1#i64 (by scalar_tac) (by scalar_tac)
        rw [hc1]
        simp only [bind_ok]
        split
        · exfalso
          rw [h1i] at hc1v
          simp_all <;> omega
        · rw [h1i] at hc1v
          obtain ⟨u1, hu1, hu1v⟩ := cms_Usize_add_eq i 1#usize hub
          rw [hu1]
          simp only [bind_ok]
          exact ⟨c1, u1, hc1v, hu1v, rfl⟩
      · exfalso
        simp_all <;> omega
    · exfalso
      simp_all <;> omega

  /-- `can_make` never fails, for any required number of picks in range: the variant of
  `can_make_ok` which does not need a bound on the length of the slice. -/
  theorem can_make_ok' (s : Slice I64) (k d : I64)
      (hne : 1 ≤ s.length)
      (hklo : 2 ≤ k.val) (hkhi : k.val ≤ (s.length : ℤ))
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ b, can_make s k d = ok b := by
    set n : Usize := Slice.len s with hn
    have hnval : n.val = s.length := by rw [hn]; exact Slice.len_val s
    have hslen : s.val.length = s.length := rfl
    have hmain : ∀ a : I64 × I64 × Usize,
        (1 ≤ a.1.val ∧ a.1.val < k.val ∧ a.2.2.val ≤ n.val ∧
          1 ≤ a.2.1.val ∧ a.2.1.val ≤ 1000000000) →
        ∃ b, loop (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2) a = ok b ∧ True := by
      refine loop_spec (fun p : I64 × I64 × Usize =>
          can_make_loop.body s k d n p.1 p.2.1 p.2.2)
        (fun a : I64 × I64 × Usize =>
          1 ≤ a.1.val ∧ a.1.val < k.val ∧ a.2.2.val ≤ n.val ∧
            1 ≤ a.2.1.val ∧ a.2.1.val ≤ 1000000000)
        (fun _ => True) (fun (p : I64 × I64 × Usize) => n.val - p.2.2.val) ?_ ?_
      · rintro ⟨count, last, i⟩ hP
        obtain ⟨hc1, hck, hi_le, hlast1, hlast2⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', -, -, hbody⟩ :=
                cm_body_cont_k s k d n count last i hilt hii hnval hbnd hck hstepp hlt
              exact ⟨_, hbody⟩
            · exact ⟨_, cm_body_done_k s k d n count last i hilt hii hnval hbnd hck
                hstepp (by omega)⟩
          · obtain ⟨u', -, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            exact ⟨_, hbody⟩
        · exact ⟨_, by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]⟩
      · rintro ⟨count, last, i⟩ hP r hr
        obtain ⟨hc1, hck, hi_le, hlast1, hlast2⟩ := hP
        dsimp only at *
        by_cases hilt : i.val < n.val
        · have hii : i.val < s.length := by omega
          have hbnd : 1 ≤ last.val ∧ last.val ≤ 1000000000 ∧ 1 ≤ s.val[i.val].val ∧
              s.val[i.val].val ≤ 1000000000 :=
            ⟨hlast1, hlast2, (hvals _ (List.getElem_mem hii)).1,
              (hvals _ (List.getElem_mem hii)).2⟩
          by_cases hstepp : d.val ≤ s.val[i.val].val - last.val
          · by_cases hlt : count.val + 1 < k.val
            · obtain ⟨c', u', hc'v, hu'v, hbody⟩ :=
                cm_body_cont_k s k d n count last i hilt hii hnval hbnd hck hstepp hlt
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.cont (c', s.val[i.val], u') := hr.symm
              subst hrc
              refine ⟨?_, ?_⟩
              · rintro a' heq
                cases heq
                refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · show (1 : ℤ) ≤ c'.val; rw [hc'v]; omega
                · show c'.val < k.val; rw [hc'v]; omega
                · show u'.val ≤ n.val; rw [hu'v]; omega
                · exact hbnd.2.2.1
                · exact hbnd.2.2.2
                · show n.val - u'.val < n.val - i.val; rw [hu'v]; omega
              · rintro b hb
                cases hb
            · have hbody := cm_body_done_k s k d n count last i hilt hii hnval hbnd hck
                hstepp (by omega)
              rw [hbody] at hr
              simp only [Result.ok.injEq] at hr
              have hrc : r = ControlFlow.done true := hr.symm
              subst hrc
              refine ⟨?_, ?_⟩
              · rintro a' heq
                cases heq
              · rintro b hb
                trivial
          · obtain ⟨u', hu'v, hbody⟩ :=
              can_make_body_skip' s k d n count last i hilt hii hnval hbnd hstepp
            rw [hbody] at hr
            simp only [Result.ok.injEq] at hr
            have hrc : r = ControlFlow.cont (count, last, u') := hr.symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq
              cases heq
              refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · exact hc1
              · exact hck
              · show u'.val ≤ n.val; rw [hu'v]; omega
              · exact hlast1
              · exact hlast2
              · show n.val - u'.val < n.val - i.val; rw [hu'v]; omega
            · rintro b hb
              cases hb
        · have hbd : can_make_loop.body s k d n count last i =
              ok (ControlFlow.done (decide (count >= k))) := by
            unfold can_make_loop.body
            rw [if_neg (by simpa using hilt)]
          rw [hbd] at hr
          simp only [Result.ok.injEq] at hr
          have hrc : r = ControlFlow.done (decide (count >= k)) := hr.symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq
            cases heq
          · rintro b hb
            trivial
    obtain ⟨b, hb, -⟩ := hmain (1#i64, s.val[0], 1#usize) (by
      have h1 : (1#i64).val = 1 := by simp
      have h2 : (1#usize).val = 1 := by simp
      have h4 : 1 ≤ s.val[0].val ∧ s.val[0].val ≤ 1000000000 :=
        hvals _ (List.getElem_mem (by omega : 0 < s.val.length))
      refine ⟨?_, ?_, ?_, h4.1, h4.2⟩
      · show (1 : ℤ) ≤ (1#i64).val; rw [h1]
      · show (1#i64).val < k.val; rw [h1]; omega
      · show (1#usize).val ≤ n.val; rw [h2]; omega)
    refine ⟨b, ?_⟩
    have hk1 : ¬ (k <= 1#i64) := by
      intro h
      have h1 : k.val ≤ 1 := by simpa using h
      omega
    have hcan : can_make s k d =
        (do let last ← s.index_usize 0#usize
            can_make_loop s k d (Slice.len s) 1#i64 last 1#usize) := by
      simp [can_make, hk1]
    rw [hcan]
    rw [show s.index_usize 0#usize = ok s.val[0] from
      Slice.index_usize_eq s 0#usize (by
        have h0 : (0#usize).val = 0 := by simp
        omega)]
    simp only [bind_ok]
    rw [← hn]
    exact hb

  /-- The body of the binary search loop `maximum_tastiness_loop1` when `lo + 1 < hi`: the loop
  computes a `mid` strictly between `lo` and `hi` and continues at `(mid, hi)` if `can_make`
  succeeds at `mid`, and at `(lo, mid)` otherwise. -/
  theorem loop1_body_cont (k : I64) (sorted : alloc.vec.Vec I64) (lo hi : I64)
      (hlo0 : 0 ≤ lo.val) (hhi : hi.val ≤ 1000000001) (h1 : lo.val + 1 < hi.val) :
      ∃ mid : I64, lo.val < mid.val ∧ mid.val < hi.val ∧
        ∀ b, can_make sorted.slice k mid = ok b →
          maximum_tastiness_loop1.body k sorted lo hi =
            ok (if b then ControlFlow.cont (mid, hi) else ControlFlow.cont (lo, mid)) := by
    have hderef : alloc.vec.Vec.deref sorted = sorted.slice :=
      Slice.ext _ _ (by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    obtain ⟨i, hi_eq, hi_val⟩ := I64.add_eq lo 1#i64 (by scalar_tac) (by scalar_tac)
    have h1i : (↑(1#i64) : ℤ) = 1 := by simp
    have hilt : i < hi := by
      rw [Aeneas.Std.IScalar.lt_equiv]
      rw [hi_val, h1i]
      omega
    obtain ⟨d, hd_eq, hd_val⟩ := I64.sub_eq hi lo (by scalar_tac) (by scalar_tac)
    obtain ⟨z, hz_eq, hz_val, -⟩ :=
      Aeneas.Std.I64.div_bv_spec (x := d) (y := 2#i64) (by simp) (by simp)
    have h2v : (↑(2#i64) : ℤ) = 2 := by simp
    have hd2 : (2 : ℤ) ≤ ↑d := by rw [hd_val]; omega
    have hz1 : 0 < (↑z : ℤ) := by
      rw [hz_val, h2v]; exact (tdiv_two_bounds hd2).1
    have hz2 : (↑z : ℤ) < ↑d := by
      rw [hz_val, h2v]; exact (tdiv_two_bounds hd2).2
    obtain ⟨mid, hmid_eq, hmid_val⟩ := I64.add_eq lo z (by scalar_tac) (by scalar_tac)
    refine ⟨mid, ?_, ?_, ?_⟩
    · rw [hmid_val]; omega
    · rw [hmid_val]; omega
    · intro b hb
      unfold maximum_tastiness_loop1.body
      rw [hi_eq]
      simp only [bind_ok]
      rw [if_pos hilt]
      rw [hd_eq]
      simp only [bind_ok]
      rw [hz_eq]
      simp only [bind_ok]
      rw [hmid_eq]
      simp only [bind_ok]
      rw [hderef]
      rw [hb]
      simp only [bind_ok]
      cases b <;> rfl

  /-- The body of the binary search loop `maximum_tastiness_loop1` when `lo + 1 ≥ hi`: the loop
  stops and answers `lo`. -/
  theorem loop1_body_done (k : I64) (sorted : alloc.vec.Vec I64) (lo hi : I64)
      (hlt : lo.val < hi.val) (h1 : ¬ lo.val + 1 < hi.val) :
      maximum_tastiness_loop1.body k sorted lo hi = ok (ControlFlow.done lo) := by
    obtain ⟨i, hi_eq, hi_val⟩ := I64.add_eq lo 1#i64 (by scalar_tac) (by scalar_tac)
    have h1i : (↑(1#i64) : ℤ) = 1 := by simp
    have hilt : ¬ i < hi := by
      rw [Aeneas.Std.IScalar.lt_equiv]
      rw [hi_val, h1i]
      omega
    unfold maximum_tastiness_loop1.body
    rw [hi_eq]
    simp only [bind_ok]
    rw [if_neg hilt]

  theorem maximum_tastiness_loop1_spec (k : I64) (sorted : alloc.vec.Vec I64) (lo hi : I64)
      (hne : 1 ≤ sorted.length)
      (hk : k.val = (sorted.length : ℤ)) (hk2 : 2 ≤ k.val)
      (hs : sorted.val.Pairwise (fun a b => a.val ≤ b.val))
      (hvals : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlo0 : 0 ≤ lo.val) (hhi : hi.val ≤ 1000000001) (hlt : lo.val < hi.val)
      (hcanlo : can_make sorted.slice k lo = ok true)
      (hcanhi : can_make sorted.slice k hi = ok false) :
      ∃ r, maximum_tastiness_loop1 k sorted lo hi = ok r ∧
        can_make sorted.slice k r = ok true ∧
          (∀ hi' : I64, hi'.val = r.val + 1 → can_make sorted.slice k hi' = ok false) ∧
            0 ≤ r.val := by
    have hlen' : sorted.slice.length = sorted.length := rfl
    have hkhi : k.val ≤ (sorted.slice.length : ℤ) := by rw [hlen', ← hk]
    obtain ⟨r, hr, hQ⟩ := loop_spec
      (body := fun (p : I64 × I64) => maximum_tastiness_loop1.body k sorted p.1 p.2)
      (P := fun p : I64 × I64 =>
        0 ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ 1000000001 ∧
          can_make sorted.slice k p.1 = ok true ∧ can_make sorted.slice k p.2 = ok false)
      (Q := fun r : I64 => can_make sorted.slice k r = ok true ∧
        (∀ hi' : I64, hi'.val = r.val + 1 → can_make sorted.slice k hi' = ok false) ∧
          0 ≤ r.val)
      (m := fun p : I64 × I64 => (p.2.val - p.1.val).toNat)
      (fun p hP => by
        obtain ⟨l, h⟩ := p
        obtain ⟨hl0, hlh, hhh, -, -⟩ := hP
        dsimp only at *
        by_cases h1 : l.val + 1 < h.val
        · obtain ⟨mid, -, -, heq⟩ := loop1_body_cont k sorted l h hl0 hhh h1
          obtain ⟨b, hb⟩ := can_make_ok' sorted.slice k mid hne hk2 hkhi hvals
          exact ⟨_, heq b hb⟩
        · exact ⟨_, loop1_body_done k sorted l h hlh h1⟩)
      (fun p hP r hr => by
        obtain ⟨l, h⟩ := p
        obtain ⟨hl0, hlh, hhh, hcanl, hcanh⟩ := hP
        dsimp only at *
        by_cases h1 : l.val + 1 < h.val
        · obtain ⟨mid, hmid1, hmid2, heq⟩ := loop1_body_cont k sorted l h hl0 hhh h1
          obtain ⟨b, hb⟩ := can_make_ok' sorted.slice k mid hne hk2 hkhi hvals
          cases b with
          | true =>
            have hbody : maximum_tastiness_loop1.body k sorted l h =
                ok (ControlFlow.cont (mid, h)) := by simpa using heq true hb
            rw [hbody] at hr
            have hrc : r = ControlFlow.cont (mid, h) := (Result.ok_injective hr).symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq'
              cases heq'
              dsimp only
              exact ⟨⟨by omega, hmid2, hhh, hb, hcanh⟩,
                (Int.toNat_lt_toNat (show (0:ℤ) < ↑h - ↑l by omega)).mpr (by omega)⟩
            · rintro b' hb'
              cases hb'
          | false =>
            have hbody : maximum_tastiness_loop1.body k sorted l h =
                ok (ControlFlow.cont (l, mid)) := by simpa using heq false hb
            rw [hbody] at hr
            have hrc : r = ControlFlow.cont (l, mid) := (Result.ok_injective hr).symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq'
              cases heq'
              dsimp only
              exact ⟨⟨hl0, hmid1, by omega, hcanl, hb⟩,
                (Int.toNat_lt_toNat (show (0:ℤ) < ↑h - ↑l by omega)).mpr (by omega)⟩
            · rintro b' hb'
              cases hb'
        · have hdone : maximum_tastiness_loop1.body k sorted l h =
              ok (ControlFlow.done l) := loop1_body_done k sorted l h hlh h1
          rw [hdone] at hr
          have hrc : r = ControlFlow.done l := (Result.ok_injective hr).symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq'
            cases heq'
          · rintro b' hb'
            have hb2 : b' = l := by cases hb'; rfl
            subst hb2
            refine ⟨hcanl, ?_, hl0⟩
            intro hi' hhi'
            have hEq : hi' = h :=
              Aeneas.Std.IScalar.eq_of_val_eq (i := hi') (j := h) (by omega)
            rw [hEq]; exact hcanh)
      (lo, hi) ⟨hlo0, hlt, hhi, hcanlo, hcanhi⟩
    refine ⟨r, ?_, hQ⟩
    simpa [maximum_tastiness_loop1] using hr

  /-- The binary-search loop of `maximum_tastiness` never fails (for arbitrary `k`). -/
  theorem maximum_tastiness_loop1_ok (k : I64) (sorted : alloc.vec.Vec I64) (lo hi : I64)
      (hne : 1 ≤ sorted.length) (hlen : sorted.length ≤ 100000)
      (hvals : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlo0 : 0 ≤ lo.val) (hhi : hi.val ≤ 1000000001) (hlt : lo.val < hi.val) :
      ∃ r, maximum_tastiness_loop1 k sorted lo hi = ok r := by
    have hne' : 1 ≤ sorted.slice.length := by
      show 1 ≤ sorted.val.length
      exact hne
    have hlen' : sorted.slice.length ≤ 100000 := by
      show sorted.val.length ≤ 100000
      exact hlen
    obtain ⟨r, hr, -⟩ := loop_spec
      (body := fun (p : I64 × I64) => maximum_tastiness_loop1.body k sorted p.1 p.2)
      (P := fun p : I64 × I64 =>
        0 ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val ≤ 1000000001)
      (Q := fun _ => True)
      (m := fun p : I64 × I64 => (p.2.val - p.1.val).toNat)
      (fun p hP => by
        obtain ⟨l, h⟩ := p
        obtain ⟨hl0, hlh, hhh⟩ := hP
        dsimp only at *
        by_cases h1 : l.val + 1 < h.val
        · obtain ⟨mid, -, -, heq⟩ := loop1_body_cont k sorted l h hl0 hhh h1
          obtain ⟨b, hb⟩ := can_make_ok_all sorted.slice k mid hne' hlen' hvals
          exact ⟨_, heq b hb⟩
        · exact ⟨_, loop1_body_done k sorted l h hlh h1⟩)
      (fun p hP r hr => by
        obtain ⟨l, h⟩ := p
        obtain ⟨hl0, hlh, hhh⟩ := hP
        dsimp only at *
        by_cases h1 : l.val + 1 < h.val
        · obtain ⟨mid, hmid1, hmid2, heq⟩ := loop1_body_cont k sorted l h hl0 hhh h1
          obtain ⟨b, hb⟩ := can_make_ok_all sorted.slice k mid hne' hlen' hvals
          have hbody := heq b hb
          rw [hbody] at hr
          cases b with
          | true =>
            have hrc : r = ControlFlow.cont (mid, h) := (Result.ok_injective hr).symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq'
              cases heq'
              dsimp only
              exact ⟨⟨by omega, hmid2, hhh⟩,
                (Int.toNat_lt_toNat (show (0:ℤ) < ↑h - ↑l by omega)).mpr (by omega)⟩
            · rintro b' hb'
              trivial
          | false =>
            have hrc : r = ControlFlow.cont (l, mid) := (Result.ok_injective hr).symm
            subst hrc
            refine ⟨?_, ?_⟩
            · rintro a' heq'
              cases heq'
              dsimp only
              exact ⟨⟨hl0, hmid1, by omega⟩,
                (Int.toNat_lt_toNat (show (0:ℤ) < ↑h - ↑l by omega)).mpr (by omega)⟩
            · rintro b' hb'
              trivial
        · have hdone : maximum_tastiness_loop1.body k sorted l h =
              ok (ControlFlow.done l) := loop1_body_done k sorted l h hlh h1
          rw [hdone] at hr
          have hrc : r = ControlFlow.done l := (Result.ok_injective hr).symm
          subst hrc
          refine ⟨?_, ?_⟩
          · rintro a' heq'
            cases heq'
          · rintro b' hb'
            trivial)
      (lo, hi) ⟨hlo0, hlt, hhi⟩
    refine ⟨r, ?_⟩
    simpa [maximum_tastiness_loop1] using hr

  /-- Main statement about the extracted function: it returns a result, and when `k` is the
  length of the array the result is the tastiness of the full selection of positions. -/
  theorem vec_index_eq (v : alloc.vec.Vec I64) (i : Usize) (h : i.val < v.val.length) :
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice I64) v i = ok v.val[i.val] := by
    rw [alloc.vec.Vec.index_slice_index]
    simp only [alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq,
      List.getElem?_eq_getElem h]

  /-- The gap `gapAt` of a list of machine integers is the `gapZ` of the corresponding list of
  integers. -/
  theorem gapZ_vals (L : List I64) (j : ℕ) :
      gapZ (L.map (fun x => x.val)) j = gapAt L j := by
    have key : ∀ n : ℕ, (L.map (fun x => x.val)).getD n 0 = (L.getD n 0#i64).val := by
      intro n
      have h2 := List.getD_map (l := L) (d := 0#i64) (n := n) (f := fun x : I64 => x.val)
      simpa using h2
    unfold gapZ gapAt
    rw [key (j + 1), key j]

  theorem gapAt_nonneg {L : List I64} (hs : L.Pairwise (fun a b => a.val ≤ b.val))
      {j : ℕ} (hj : j + 1 < L.length) : 0 ≤ gapAt L j := by
    have hle : (L[j]'(by omega)).val ≤ (L[j+1]'hj).val :=
      List.Pairwise.rel_get_of_le hs (Nat.le_succ j)
    unfold gapAt
    rw [List.getD_eq_getElem L 0#i64 (n := j + 1) (by omega),
      List.getD_eq_getElem L 0#i64 (n := j) (by omega)]
    linarith

  /-- If `can_make` answers `true` at `r` and `false` at `r + 1` (for an array whose length is
  `k`), then `r` is the minimum pairwise distance of all the values of the array. -/
  theorem tastinessOn_eq_of_can_make (s : Slice I64) (k r : I64)
      (hne : 1 ≤ s.length) (hlen : s.length ≤ 100000)
      (hs : s.val.Pairwise (fun a b => a.val ≤ b.val))
      (hvals : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk : k.val = (s.length : ℤ)) (hk2 : 2 ≤ k.val)
      (hr0 : 0 ≤ r.val)
      (htrue : can_make s k r = ok true)
      (hfalse : ∀ hi' : I64, hi'.val = r.val + 1 → can_make s k hi' = ok false) :
      r.val = tastinessOn (vals s) (Finset.range (vals s).length) := by
    have hslen : s.val.length = s.length := rfl
    have h2 : 2 ≤ s.val.length := by rw [hslen]; omega
    have hgapmem : ∀ j : ℕ, j + 1 < s.val.length →
        gapAt s.val j ∈ gapsConsec (s.val.drop 1) s.val[0] := by
      intro j hj
      rw [mem_gapsConsec_drop_one (by omega : 1 ≤ s.val.length)]
      exact ⟨j, hj, rfl⟩
    -- the two `can_make` specifications
    have hspec : ∀ d : I64, can_make s k d = ok true →
        ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g := by
      intro d hd
      obtain ⟨b, hb, hiff⟩ := can_make_spec s k d hne hlen hk hk2 hs hvals
      rw [hd] at hb
      have hbt : b = true := (Result.ok_injective hb).symm
      subst hbt
      exact hiff.mp rfl
    have hspec' : ∀ d : I64, can_make s k d = ok false →
        ¬ (∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], d.val ≤ g) := by
      intro d hd hc
      obtain ⟨b, hb, hiff⟩ := can_make_spec s k d hne hlen hk hk2 hs hvals
      rw [hd] at hb
      have hbf : b = false := (Result.ok_injective hb).symm
      subst hbf
      exact absurd (hiff.mpr hc) (by simp)
    have hlo : ∀ g ∈ gapsConsec (s.val.drop 1) s.val[0], r.val ≤ g := hspec r htrue
    -- an upper bound for `r`
    have hrle : r.val ≤ 1000000000 := by
      have h := hlo _ (hgapmem 0 (by omega))
      unfold gapAt at h
      rw [List.getD_eq_getElem s.val 0#i64 (n := 1) (by omega),
        List.getD_eq_getElem s.val 0#i64 (n := 0) (by omega)] at h
      have h1 : (s.val[1]'(by omega)).val ≤ 1000000000 := (hvals _ (List.getElem_mem _)).2
      have h2' : 1 ≤ (s.val[0]'(by omega)).val := (hvals _ (List.getElem_mem _)).1
      linarith
    -- the successor of `r`
    obtain ⟨w, -, hwv⟩ := I64.add_eq r 1#i64 (by scalar_tac) (by scalar_tac)
    have hwv' : w.val = r.val + 1 := by rw [hwv]; simp
    have hnot := hspec' w (hfalse w hwv') 
    push_neg at hnot
    obtain ⟨g, hg, hgw⟩ := hnot
    have hgr : r.val ≤ g := hlo g hg
    have hgv : g = r.val := by rw [hwv'] at hgw; omega
    have hgmem := hg
    rw [mem_gapsConsec_drop_one (by omega : 1 ≤ s.val.length)] at hgmem
    obtain ⟨j0, hj0, hgap0⟩ := hgmem
    have hsp : (vals s).Pairwise (· ≤ ·) := by
      show (s.val.map (fun x => x.val)).Pairwise (· ≤ ·)
      exact List.Pairwise.map (fun x : I64 => x.val) (fun a b hab => hab) hs
    have h2len : 2 ≤ (vals s).length := by
      show 2 ≤ (s.val.map (fun x => x.val)).length
      rw [List.length_map]; exact h2
    have hlo' : ∀ j, j + 1 < (vals s).length → r.val ≤ gapZ (vals s) j := by
      intro j hj
      show r.val ≤ gapZ (s.val.map (fun x => x.val)) j
      rw [gapZ_vals s.val j]
      have hj' : j + 1 < (s.val.map (fun x => x.val)).length := hj
      rw [List.length_map] at hj'
      exact hlo _ (hgapmem j hj')
    have hhi' : ∃ j, j + 1 < (vals s).length ∧ gapZ (vals s) j = r.val := by
      refine ⟨j0, ?_, ?_⟩
      · show j0 + 1 < (s.val.map (fun x => x.val)).length
        rw [List.length_map]; exact hj0
      · show gapZ (s.val.map (fun x => x.val)) j0 = r.val
        rw [gapZ_vals s.val j0, ← hgap0, hgv]
    have hres := tastinessOn_sorted_eq (vals s) hsp h2len r.val hlo' hhi'
    rw [hres]

  theorem maximum_tastiness_aux (price : Slice I64) (k : I64)
      (h2 : 2 ≤ price.length) (hlen : price.length ≤ 100000)
      (hvals : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length)) := by
    unfold maximum_tastiness
    have hnval : (Slice.len price).val = price.length := Slice.len_val price
    have h1u : (1#usize).val = 1 := by simp
    have h0u : (0#usize).val = 0 := by simp
    have h1i : (1#i64).val = 1 := by simp
    have h0i : (0#i64).val = 0 := by simp
    have hn0 : ¬ (Slice.len price = 0#usize) := by
      intro h
      have h1 : (Slice.len price).val = 0 := by rw [h]; simp
      omega
    rw [ite_eq_right (by simpa using hn0)]
    obtain ⟨v, hv, hvval⟩ := maximum_tastiness_loop0_spec price (Slice.len price) hnval
    rw [hv]
    simp only [bind_ok]
    simp only [alloc.vec.Vec.deref_mut, lift, bind_ok]
    show ∃ r, (do
          let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 v.slice
          let i ← price.len - 1#usize
          let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice I64) { slice := s1 } i
          let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice I64) { slice := s1 } 0#usize
          let max_diff ← i1 - i2
          let hi ← max_diff + 1#i64
          maximum_tastiness_loop1 k { slice := s1 } 0#i64 hi) = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length))
    obtain ⟨s1, hs1, hs1perm, hs1sorted⟩ := Slice.sort_spec v.slice
    rw [hs1]
    simp only [bind_ok]
    have hvlen : v.slice.val = price.val := hvval
    have hs1vals : ∀ x ∈ s1.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      have hmemv : x ∈ v.slice.val := hs1perm.subset hx
      rw [hvlen] at hmemv
      exact hvals x hmemv
    have hs1len : s1.val.length = price.length := by
      have h := hs1perm.length_eq
      rw [hvlen] at h
      simpa using h
    obtain ⟨i0, hi0, hi0v⟩ := Usize.sub_eq (Slice.len price) 1#usize (by omega)
    rw [hi0]
    simp only [bind_ok]
    have hi1 : i0.val < s1.val.length := by rw [hi0v, hs1len]; omega
    have hs1pos : 0 < s1.val.length := by rw [hs1len]; omega
    rw [vec_index_eq { slice := s1 } i0 (by exact hi1)]
    simp only [bind_ok]
    rw [vec_index_eq { slice := s1 } 0#usize (by
      show (0#usize).val < s1.val.length
      rw [h0u]; exact hs1pos)]
    simp only [bind_ok]
    simp only [h0u]
    -- the value of the index `n - 1` and the ordering facts
    have hi0pos : 0 ≤ i0.val := by rw [hi0v, hnval, h1u]; omega
    have hi0ge1 : 1 ≤ i0.val := by rw [hi0v, hnval, h1u]; omega
    have hbnd0 : 1 ≤ s1.val[0].val ∧ s1.val[0].val ≤ 1000000000 :=
      hs1vals _ (List.getElem_mem hs1pos)
    have hbnd1 : 1 ≤ s1.val[i0.val].val ∧ s1.val[i0.val].val ≤ 1000000000 :=
      hs1vals _ (List.getElem_mem hi1)
    have hcmp0 : s1.val[0].val ≤ s1.val[i0.val].val :=
      pairwise_i64_getElem_le hs1sorted hi0pos hi1
    show ∃ r, (do
          let max_diff ← s1.val[i0.val] - s1.val[0]
          let hi ← max_diff + 1#i64
          maximum_tastiness_loop1 k { slice := s1 } 0#i64 hi) = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length))
    obtain ⟨md, hmd, hmdv⟩ := I64.sub_eq s1.val[i0.val] s1.val[0]
      (by scalar_tac) (by scalar_tac)
    rw [hmd]
    simp only [bind_ok]
    obtain ⟨hi, hhi, hhiv⟩ := I64.add_eq md 1#i64 (by scalar_tac) (by scalar_tac)
    rw [hhi]
    simp only [bind_ok]
    -- facts about `hi`
    have hmdv' : md.val = s1.val[i0.val].val - s1.val[0].val := hmdv
    have hmdrng : 0 ≤ md.val ∧ md.val ≤ 1000000000 := by
      rw [hmdv']; constructor <;> [skip; skip] <;> linarith [hbnd0, hbnd1, hcmp0]
    have hhiv' : hi.val = md.val + 1 := by rw [hhiv, h1i]
    have hvlo : (0#i64).val < hi.val := by rw [h0i, hhiv']; linarith [hmdrng.1]
    have hvhi : hi.val ≤ 1000000001 := by rw [hhiv']; linarith [hmdrng.2]
    -- the array as a vector
    have hne' : 1 ≤ ({ slice := s1 } : alloc.vec.Vec I64).length := by
      show 1 ≤ s1.val.length
      rw [hs1len]; omega
    have hlen' : ({ slice := s1 } : alloc.vec.Vec I64).length ≤ 100000 := by
      show s1.val.length ≤ 100000
      rw [hs1len]; exact hlen
    have hneS : 1 ≤ s1.length := by
      show 1 ≤ s1.val.length
      rw [hs1len]; omega
    have hlenS : s1.length ≤ 100000 := by
      show s1.val.length ≤ 100000
      rw [hs1len]; exact hlen
    by_cases hk : k.val = (price.length : ℤ)
    · have hklen : k.val = (({ slice := s1 } : alloc.vec.Vec I64).length : ℤ) := by
        show k.val = (s1.val.length : ℤ)
        rw [hs1len]; exact hk
      have hklenS : k.val = (s1.length : ℤ) := by
        show k.val = (s1.val.length : ℤ)
        rw [hs1len]; exact hk
      have hk2 : 2 ≤ k.val := by rw [hk]; omega
      -- `can_make` at `0` is `true`
      have hcanlo : can_make s1 k 0#i64 = ok true := by
        obtain ⟨b, hb, hiff⟩ := can_make_spec s1 k 0#i64 hneS hlenS hklenS hk2
          hs1sorted hs1vals
        have hall : ∀ g, g ∈ gapsConsec (s1.val.drop 1) s1.val[0] → (0#i64).val ≤ g := by
          intro g hg
          obtain ⟨j, hj, hgj⟩ :=
            (mem_gapsConsec_drop_one (L := s1.val) (by omega : 1 ≤ s1.val.length)).mp hg
          rw [hgj, h0i]
          exact gapAt_nonneg hs1sorted hj
        have hbt : b = true := hiff.mpr hall
        rw [hbt] at hb
        exact hb
      -- `can_make` at `hi` is `false`
      have hcanhi : can_make s1 k hi = ok false := by
        obtain ⟨b, hb, hiff⟩ := can_make_spec s1 k hi hneS hlenS hklenS hk2
          hs1sorted hs1vals
        have hnot : ¬ (∀ g, g ∈ gapsConsec (s1.val.drop 1) s1.val[0] → hi.val ≤ g) := by
          intro hall
          have hmem : gapAt s1.val 0 ∈ gapsConsec (s1.val.drop 1) s1.val[0] :=
            (mem_gapsConsec_drop_one (L := s1.val) (by omega : 1 ≤ s1.val.length)).mpr
              ⟨0, by omega, rfl⟩
          have hle := hall _ hmem
          have hg0 : gapAt s1.val 0 = s1.val[1].val - s1.val[0].val := by
            unfold gapAt
            rw [List.getD_eq_getElem s1.val 0#i64 (n := 1) (by omega),
              List.getD_eq_getElem s1.val 0#i64 (n := 0) (by omega)]
          have hcmp1 : s1.val[1].val ≤ s1.val[i0.val].val := by
            exact pairwise_i64_getElem_le hs1sorted hi0ge1 hi1
          rw [hg0] at hle
          linarith [hmdv']
        have hbf : b = false := by
          cases b with
          | false => rfl
          | true => exact absurd (hiff.mp rfl) hnot
        rw [hbf] at hb
        exact hb
      obtain ⟨r, hr, htrue, hfalse, hr0⟩ :=
        maximum_tastiness_loop1_spec k { slice := s1 } 0#i64 hi hne' hklen hk2
          hs1sorted hs1vals (by rw [h0i]) hvhi hvlo hcanlo hcanhi
      refine ⟨r, hr, ?_⟩
      intro _
      have hmin := tastinessOn_eq_of_can_make s1 k r hneS hlenS hs1sorted hs1vals
        hklenS hk2 hr0 htrue hfalse
      rw [hmin]
      have hperm : (vals s1).Perm (vals price) := by
        show (s1.val.map (fun x => x.val)).Perm (price.val.map (fun x => x.val))
        have hp : s1.val.Perm price.val := by
          have h := hs1perm
          rw [hvlen] at h
          exact h
        exact List.Perm.map (fun x : I64 => x.val) hp
      have h2lenp : 2 ≤ (vals price).length := by
        show 2 ≤ (price.val.map (fun x => x.val)).length
        rw [List.length_map]; exact h2
      exact tastinessOn_perm (vals s1) (vals price) hperm h2lenp
    · obtain ⟨r, hr⟩ := maximum_tastiness_loop1_ok k { slice := s1 } 0#i64 hi hne' hlen'
        hs1vals (by rw [h0i]) hvhi hvlo
      exact ⟨r, hr, fun h => absurd h hk⟩

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
  theorem spec_10 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (k.val = (price.length : ℤ) →
          r.val = tastinessOn (vals price) (Finset.range (vals price).length)) := by
    exact maximum_tastiness_aux price k h_n h_len h_price

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
