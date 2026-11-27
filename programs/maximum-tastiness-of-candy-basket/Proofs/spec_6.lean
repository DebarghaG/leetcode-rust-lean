import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_6` (maximum-tastiness-of-candy-basket).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumTastiness (maximum_tastiness)

  set_option maxHeartbeats 2000000
  set_option maxRecDepth 4096

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

  /-! ## Auxiliary list notions used in the proof of `spec_S6` -/

  /-- `ConsecGaps d l` says that consecutive elements of `l` differ by at least `d`. -/
  def ConsecGaps (d : ℤ) : List ℤ → Prop
    | [] => True
    | [_] => True
    | x :: y :: l => x + d ≤ y ∧ ConsecGaps d (y :: l)

  /-- `PairDists d l` says that every pair of distinct positions of `l` is at distance at
  least `d`. -/
  def PairDists (d : ℤ) (l : List ℤ) : Prop :=
    ∀ i j, i < j → j < l.length → d ≤ absDiff (l.getD i 0) (l.getD j 0)

  /-- Greedy chain with threshold `v`: take the first element which is `≥ v`, then continue
  with threshold `x + d` where `x` is the element just taken. -/
  def gsel (d : ℤ) : ℤ → List ℤ → List ℤ
    | _, [] => []
    | v, x :: xs => if v ≤ x then x :: gsel d (x + d) xs else gsel d v xs

  /-- The greedy selection of a nonempty list: the head is always taken. -/
  def greed (d : ℤ) (l : List ℤ) : List ℤ :=
    match l with
    | [] => []
    | x :: xs => x :: gsel d (x + d) xs

  @[simp] theorem gsel_nil (d v : ℤ) : gsel d v [] = [] := rfl

  @[simp] theorem gsel_cons (d v x : ℤ) (xs : List ℤ) :
      gsel d v (x :: xs) = if v ≤ x then x :: gsel d (x + d) xs else gsel d v xs := rfl

  @[simp] theorem greed_nil (d : ℤ) : greed d [] = [] := rfl

  @[simp] theorem greed_cons (d x : ℤ) (xs : List ℤ) :
      greed d (x :: xs) = x :: gsel d (x + d) xs := rfl

  theorem consecGaps_cons_cons (d x y : ℤ) (l : List ℤ) :
      ConsecGaps d (x :: y :: l) ↔ x + d ≤ y ∧ ConsecGaps d (y :: l) := Iff.rfl

  theorem consecGaps_tail {d x : ℤ} {l : List ℤ} (h : ConsecGaps d (x :: l)) :
      ConsecGaps d l := by
    cases l with
    | nil => trivial
    | cons y ys => exact (consecGaps_cons_cons d x y ys).1 h |>.2

  theorem consecGaps_all_ge {d : ℤ} (hd : 0 ≤ d) :
      ∀ {x : ℤ} {l : List ℤ}, ConsecGaps d (x :: l) → ∀ y ∈ l, x + d ≤ y
    | x, [], h => by intro y hy; simp at hy
    | x, y :: ys, h => by
        obtain ⟨h1, h2⟩ := (consecGaps_cons_cons d x y ys).1 h
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h1
        · have := consecGaps_all_ge hd h2 z hz
          omega

  theorem consecGaps_mono {d d' : ℤ} (hdd : d' ≤ d) : ∀ {l : List ℤ},
      ConsecGaps d l → ConsecGaps d' l
    | [], _ => trivial
    | [_], _ => trivial
    | _ :: _ :: _, h => by
        obtain ⟨h1, h2⟩ := h
        exact ⟨by omega, consecGaps_mono hdd h2⟩

  theorem consecGaps_take {d : ℤ} (hd : 0 ≤ d) : ∀ (l : List ℤ) (k : ℕ),
      ConsecGaps d l → ConsecGaps d (l.take k)
    | [], _, _ => by simp only [List.take_nil]; trivial
    | _ :: _, 0, _ => trivial
    | x :: xs, k + 1, h => by
        have hx : ConsecGaps d xs := consecGaps_tail h
        have ih := consecGaps_take hd xs k hx
        rw [List.take_succ_cons]
        cases hL : xs.take k with
        | nil => trivial
        | cons y ys =>
            rw [hL] at ih
            have hy : y ∈ xs := by
              have hs := List.take_sublist (l := xs) (i := k)
              rw [hL] at hs
              exact hs.subset (by simp)
            have h1 : x + d ≤ y := by
              have h2 := consecGaps_all_ge (d := d) hd h y hy
              simpa using h2
            exact ⟨h1, ih⟩

  theorem absDiff_eq_of_le {a b : ℤ} (h : a ≤ b) : absDiff a b = b - a := by
    show ((a - b).natAbs : ℤ) = b - a
    have h2 : ((a - b).natAbs : ℤ) = -(a - b) := by
      have h3 : ((-(a - b)).natAbs : ℤ) = -(a - b) := Int.natAbs_of_nonneg (by omega)
      rwa [Int.natAbs_neg] at h3
    omega

  theorem le_absDiff_of_le {d a b : ℤ} (h : a ≤ b) : (d ≤ absDiff a b ↔ a + d ≤ b) := by
    rw [absDiff_eq_of_le h]; omega

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    show ((a - b).natAbs : ℤ) = ((b - a).natAbs : ℤ)
    rw [show a - b = -(b - a) by omega, Int.natAbs_neg]

  theorem absDiff_nonneg (a b : ℤ) : 0 ≤ absDiff a b := by
    show (0 : ℤ) ≤ ((a - b).natAbs : ℤ)
    exact Int.natCast_nonneg _

  theorem pairDists_mono {d d' : ℤ} (hdd : d' ≤ d) {l : List ℤ} (h : PairDists d l) :
      PairDists d' l := by
    intro i j hij hj
    exact le_trans hdd (h i j hij hj)

  theorem consecGaps_of_pairDists {d : ℤ} :
      ∀ {l : List ℤ}, l.Pairwise (· ≤ ·) → PairDists d l → ConsecGaps d l
    | [], _, _ => trivial
    | [_], _, _ => trivial
    | x :: y :: ys, hord, h => by
        refine ⟨?_, consecGaps_of_pairDists (List.Pairwise.of_cons hord) ?_⟩
        · have hxy : d ≤ absDiff x y := by
            have h0 := h 0 1 (by omega) (by simp)
            simpa using h0
          have hle : x ≤ y := List.rel_of_pairwise_cons hord (by simp)
          rw [le_absDiff_of_le hle] at hxy
          linarith
        · intro i j hij hj
          have h0 := h (i + 1) (j + 1) (by omega) (by simp at hj ⊢; omega)
          simpa using h0

  theorem sublist_tail_cons {c a : ℤ} {T' l' : List ℤ}
      (h : (c :: T').Sublist (a :: l')) : T'.Sublist l' := by
    rcases List.sublist_cons_iff.1 h with h1 | ⟨r, hr, hs⟩
    · exact List.sublist_of_cons_sublist h1
    · rw [List.cons.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact hs

  theorem sublist_cons_of_notMem {a : ℤ} {l T : List ℤ} (h : T.Sublist (a :: l))
      (hna : a ∉ T) : T.Sublist l := by
    rcases List.sublist_cons_iff.1 h with h1 | ⟨r, hr, hs⟩
    · exact h1
    · rw [hr] at hna
      exact absurd (by simp) hna

  theorem gsel_sublist (d v : ℤ) : ∀ l : List ℤ, (gsel d v l).Sublist l
    | [] => by simp
    | x :: xs => by
        rw [gsel_cons]
        by_cases h : v ≤ x
        · rw [if_pos h]
          exact List.Sublist.cons_cons x (gsel_sublist d (x + d) xs)
        · rw [if_neg h]
          exact List.Sublist.cons x (gsel_sublist d v xs)

  theorem gsel_ok (d : ℤ) (hd : 0 ≤ d) : ∀ (l : List ℤ) (v : ℤ),
      (∀ y ∈ gsel d v l, v ≤ y) ∧ ConsecGaps d (gsel d v l)
    | [], _ => by simp only [gsel_nil]; exact ⟨by simp, trivial⟩
    | x :: xs, v => by
        rw [gsel_cons]
        by_cases h : v ≤ x
        · rw [if_pos h]
          obtain ⟨h1, h2⟩ := gsel_ok d hd xs (x + d)
          refine ⟨?_, ?_⟩
          · intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact h
            · have := h1 y hy
              omega
          · cases hg : gsel d (x + d) xs with
            | nil => trivial
            | cons c cs =>
                have hc : x + d ≤ c := h1 c (by rw [hg]; simp)
                rw [hg] at h2
                exact ⟨hc, h2⟩
        · rw [if_neg h]
          exact gsel_ok d hd xs v

  theorem gsel_optimal (d : ℤ) (hd : 0 ≤ d) (l : List ℤ) (hord : l.Pairwise (· ≤ ·)) :
      ∀ (v : ℤ) (T : List ℤ), T.Sublist l → T ≠ [] → (∀ y ∈ T, v ≤ y) →
        ConsecGaps d T → T.length ≤ (gsel d v l).length := by
    induction l with
    | nil =>
        intro v T hsub hne _ _
        exact absurd (by simpa using hsub) hne
    | cons a l' ih =>
        intro v T hsub hne hge hcg
        by_cases hv : v ≤ a
        · rw [gsel_cons, if_pos hv]
          rcases T with _ | ⟨c, T'⟩
          · exact absurd rfl hne
          · have hc_le : a ≤ c := by
              have hmem : c ∈ a :: l' := hsub.subset (by simp)
              rcases List.mem_cons.1 hmem with hc0 | hc
              · omega
              · exact List.rel_of_pairwise_cons hord hc
            have hT' : T'.Sublist l' := sublist_tail_cons hsub
            rcases T' with _ | ⟨e, es⟩
            · simp
            · have hge' : ∀ y ∈ e :: es, a + d ≤ y := by
                intro y hy
                have h1 : c + d ≤ y := consecGaps_all_ge hd hcg y hy
                omega
              have hcg' : ConsecGaps d (e :: es) := consecGaps_tail hcg
              have hres := ih (List.Pairwise.of_cons hord) (a + d) (e :: es) hT' (by simp) hge' hcg'
              simp only [List.length_cons] at hres ⊢
              omega
        · rw [gsel_cons, if_neg hv]
          have hna : a ∉ T := by
            intro hmem
            have := hge a hmem
            omega
          exact ih (List.Pairwise.of_cons hord) v T (sublist_cons_of_notMem hsub hna) hne hge hcg

  theorem greed_sublist (d : ℤ) : ∀ l : List ℤ, (greed d l).Sublist l
    | [] => by simp
    | x :: xs => by
        rw [greed_cons]
        exact List.Sublist.cons_cons x (gsel_sublist d (x + d) xs)

  theorem greed_optimal (d : ℤ) (hd : 0 ≤ d) (l : List ℤ) (hord : l.Pairwise (· ≤ ·)) :
      ∀ (T : List ℤ), T.Sublist l → T ≠ [] → ConsecGaps d T →
        T.length ≤ (greed d l).length := by
    cases l with
    | nil => intro T hsub hne; exact absurd (by simpa using hsub) hne
    | cons x xs =>
        intro T hsub hne hcg
        rcases T with _ | ⟨c, T'⟩
        · exact absurd rfl hne
        · rw [greed_cons]
          have hc_le : x ≤ c := by
            have hmem : c ∈ x :: xs := hsub.subset (by simp)
            rcases List.mem_cons.1 hmem with hc0 | hc
            · omega
            · exact List.rel_of_pairwise_cons hord hc
          have hT' : T'.Sublist xs := sublist_tail_cons hsub
          rcases T' with _ | ⟨e, es⟩
          · simp
          · have hge : ∀ y ∈ e :: es, x + d ≤ y := by
              intro y hy
              have h1 : c + d ≤ y := consecGaps_all_ge hd hcg y hy
              omega
            have hres := gsel_optimal d hd xs (List.Pairwise.of_cons hord) (x + d) (e :: es) hT'
              (by simp) hge (consecGaps_tail hcg)
            simp only [List.length_cons] at hres ⊢
            omega

  theorem greed_ok (d : ℤ) (hd : 0 ≤ d) (s : List ℤ) : ConsecGaps d (greed d s) := by
    cases s with
    | nil => trivial
    | cons x xs =>
        rw [greed_cons]
        obtain ⟨h1, h2⟩ := gsel_ok d hd xs (x + d)
        cases hg : gsel d (x + d) xs with
        | nil => trivial
        | cons c cs =>
            have hc : x + d ≤ c := h1 c (by rw [hg]; simp)
            rw [hg] at h2
            exact ⟨hc, h2⟩

  /-! ### The pure model of `can_make` -/

  /-- Pure model of `can_make`: can `k` points be picked from `s` such that consecutive
  picked elements are at distance at least `d`? -/
  def canMake (k d : ℤ) (s : List ℤ) : Bool :=
    if k ≤ 1 then true else decide (k.toNat ≤ (greed d s).length)

  theorem canMake_complete {k d : ℤ} {s T : List ℤ} (hs : s.Pairwise (· ≤ ·)) (hd : 0 ≤ d)
      (hlen : T.length = k.toNat) (hsub : T.Sublist s) (hcg : ConsecGaps d T) (hk1 : 1 ≤ k) :
      canMake k d s = true := by
    have hne : T ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    have hle : T.length ≤ (greed d s).length := greed_optimal d hd s hs T hsub hne hcg
    by_cases h : k ≤ 1
    · simp only [canMake, if_pos h]
    · simp only [canMake, if_neg h, decide_eq_true_eq]
      omega

  theorem consecGaps_short {d : ℤ} {l : List ℤ} (h : l.length ≤ 1) : ConsecGaps d l := by
    match l with
    | [] => trivial
    | [_] => trivial
    | _ :: _ :: _ => simp at h

  theorem canMake_sound {k d : ℤ} {s : List ℤ} (hd : 0 ≤ d) (hks : k.toNat ≤ s.length)
      (h : canMake k d s = true) :
      ∃ T, T.Sublist s ∧ T.length = k.toNat ∧ ConsecGaps d T := by
    by_cases hk : k ≤ 1
    · refine ⟨s.take k.toNat, List.take_sublist _ _, ?_, consecGaps_short ?_⟩
      · rw [List.length_take, Nat.min_eq_left hks]
      · rw [List.length_take, Nat.min_eq_left hks]
        omega
    · have hk' : k.toNat ≤ (greed d s).length := by
        simpa [canMake, hk] using h
      refine ⟨(greed d s).take k.toNat, ?_, ?_, ?_⟩
      · exact (List.take_sublist _ _).trans (greed_sublist d s)
      · rw [List.length_take, Nat.min_eq_left hk']
      · exact consecGaps_take hd _ _ (greed_ok d hd s)

  theorem canMake_mono {k d d' : ℤ} {s : List ℤ} (hdd : d' ≤ d) (hd : 0 ≤ d) (hd' : 0 ≤ d')
      (hks : k.toNat ≤ s.length) (hs : s.Pairwise (· ≤ ·)) (hk1 : 1 ≤ k)
      (h : canMake k d s = true) : canMake k d' s = true := by
    obtain ⟨T, hsub, hlen, hcg⟩ := canMake_sound hd hks h
    exact canMake_complete hs hd' hlen hsub (consecGaps_mono hdd hcg) hk1

  /-! ### Selections as sublists, and the distance bound -/

  theorem pairDistsOn_mem {l : List ℤ} {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S)
      (hij : i < j) : absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := by
    have hmem : (i, j) ∈ ((S.product S).filter (fun p => p.1 < p.2)) := by
      simp only [Finset.mem_filter]
      exact ⟨by simp [Finset.mem_product, hi, hj], hij⟩
    simp only [pairDistsOn]
    exact Finset.mem_image.2 ⟨(i, j), hmem, rfl⟩

  theorem pairDistsOn_nonempty {l : List ℤ} {S : Finset ℕ} (h : 1 < S.card) :
      (pairDistsOn l S).Nonempty := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨_, pairDistsOn_mem hi hj hlt⟩
    · refine ⟨absDiff (l.getD j 0) (l.getD i 0), ?_⟩
      exact pairDistsOn_mem (i := j) (j := i) hj hi hlt

  theorem tastinessOn_le_absDiff {l : List ℤ} {S : Finset ℕ} {i j : ℕ} (h2 : 1 < S.card)
      (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) :
      tastinessOn l S ≤ absDiff (l.getD i 0) (l.getD j 0) := by
    have hmem : absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := pairDistsOn_mem hi hj hij
    have hne : (pairDistsOn l S).Nonempty := pairDistsOn_nonempty h2
    rw [tastinessOn, dif_pos hne]
    exact Finset.min'_le _ _ hmem

  /-- The increasing list of the elements of `S` below `n`. -/
  def selIdx (n : ℕ) (S : Finset ℕ) : List ℕ :=
    (List.range n).filter (fun i => decide (i ∈ S))

  theorem selIdx_sublist (n : ℕ) (S : Finset ℕ) : (selIdx n S).Sublist (List.range n) :=
    List.filter_sublist

  theorem selIdx_pairwise (n : ℕ) (S : Finset ℕ) :
      List.Pairwise (· < ·) (selIdx n S) :=
    List.Pairwise.sublist (selIdx_sublist n S) List.pairwise_lt_range

  theorem selIdx_mem {n : ℕ} {S : Finset ℕ} {i : ℕ} (h : i ∈ selIdx n S) : i < n ∧ i ∈ S := by
    simp only [selIdx, List.mem_filter, List.mem_range] at h
    exact ⟨h.1, by simpa using h.2⟩

  theorem length_selIdx {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
      (selIdx n S).length = S.card := by
    have hnodup : (selIdx n S).Nodup :=
      List.Nodup.sublist (selIdx_sublist n S) List.nodup_range
    rw [← List.toFinset_card_of_nodup hnodup]
    simp only [selIdx, List.toFinset_filter, List.toFinset_range]
    congr 1
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hx⟩; simpa using hx
    · intro hx; exact ⟨by simpa using hS hx, by simpa using hx⟩

  theorem range_getD {n i : ℕ} (h : i < n) : (List.range n).getD i 0 = i := by
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_range]

  theorem range_map_getD (L : List ℤ) : (List.range L.length).map (fun i => L.getD i 0) = L := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_map]
      simp only [List.getElem_range]
      rw [List.getD_eq_getElem _ _ h2]

  theorem getD_map_getD (idx : List ℕ) (L : List ℤ) (i : ℕ) (hi : i < idx.length)
      (hL : ∀ x ∈ idx, x < L.length) :
      (idx.map (fun k => L.getD k 0)).getD i 0 = L.getD (idx.getD i 0) 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (hL _ (List.getElem_mem hi))]

  /-- A `k`-element selection of positions of `L`, with all pairwise distances at least `d`,
  gives a `k`-element sublist of `L` with the same property. -/
  theorem exists_sublist_pairDists {L : List ℤ} {S : Finset ℕ} (hS : S ⊆ Finset.range L.length)
      {k : ℕ} (hk : S.card = k) {d : ℤ}
      (hmin : ∀ i ∈ S, ∀ j ∈ S, i < j → d ≤ absDiff (L.getD i 0) (L.getD j 0)) :
      ∃ T : List ℤ, T.Sublist L ∧ T.length = k ∧ PairDists d T := by
    refine ⟨(selIdx L.length S).map (fun i => L.getD i 0), ?_, ?_, ?_⟩
    · have h1 : ((selIdx L.length S).map (fun i => L.getD i 0)).Sublist
          ((List.range L.length).map (fun i => L.getD i 0)) :=
        List.Sublist.map _ (selIdx_sublist _ _)
      rwa [range_map_getD] at h1
    · rw [List.length_map, length_selIdx hS, hk]
    · intro i j hij hj
      have hj' : j < (selIdx L.length S).length := by simpa using hj
      have hi' : i < (selIdx L.length S).length := lt_trans hij hj'
      have hLmem : ∀ x ∈ selIdx L.length S, x < L.length := fun x hx => (selIdx_mem hx).1
      rw [getD_map_getD _ _ i hi' hLmem, getD_map_getD _ _ j hj' hLmem]
      have hlt : (selIdx L.length S).getD i 0 < (selIdx L.length S).getD j 0 := by
        rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
        exact List.Pairwise.rel_getElem_of_lt hi' hj' (selIdx_pairwise _ _) hij
      have hiS : (selIdx L.length S).getD i 0 ∈ S := by
        rw [List.getD_eq_getElem _ _ hi']
        exact (selIdx_mem (List.getElem_mem _)).2
      have hjS : (selIdx L.length S).getD j 0 ∈ S := by
        rw [List.getD_eq_getElem _ _ hj']
        exact (selIdx_mem (List.getElem_mem _)).2
      exact hmin _ hiS _ hjS hlt

  theorem head_le_of_mem {s : List ℤ} (hs : s.Pairwise (· ≤ ·)) {y : ℤ} (hy : y ∈ s) :
      s.getD 0 0 ≤ y := by
    cases s with
    | nil => simp at hy
    | cons a l =>
        have h1 : a ≤ y := by
          rcases List.mem_cons.1 hy with rfl | hyl
          · omega
          · exact List.rel_of_pairwise_cons hs hyl
        simpa using h1

  theorem le_last_of_mem (s : List ℤ) (hs : s.Pairwise (· ≤ ·)) (y : ℤ) (hy : y ∈ s) :
      y ≤ s.getD (s.length - 1) 0 := by
    induction s generalizing y with
    | nil => simp at hy
    | cons a l ih =>
        cases l with
        | nil =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            subst hy
            simp
        | cons b rest =>
            have hord' : (b :: rest).Pairwise (· ≤ ·) := List.Pairwise.of_cons hs
            have hb : a ≤ b := List.rel_of_pairwise_cons hs (by simp)
            rcases List.mem_cons.1 hy with h0 | hy'
            · rw [h0]
              have h1 : b ≤ (b :: rest).getD ((b :: rest).length - 1) 0 :=
                ih hord' b (by simp)
              have h2 : (a :: b :: rest).getD ((a :: b :: rest).length - 1) 0
                  = (b :: rest).getD ((b :: rest).length - 1) 0 := by simp
              rw [h2]
              omega
            · exact ih hord' y hy'

  theorem gap_le_spread {s T : List ℤ} {d : ℤ} (hs : s.Pairwise (· ≤ ·))
      (hsub : T.Sublist s) (h2 : 2 ≤ T.length) (hcg : ConsecGaps d T) :
      d ≤ s.getD (s.length - 1) 0 - s.getD 0 0 := by
    rcases T with _ | ⟨c, rest⟩
    · simp at h2
    · rcases rest with _ | ⟨e, es⟩
      · simp at h2
      · have hd : d ≤ e - c := by
          have h1 : c + d ≤ e := ((consecGaps_cons_cons d c e es).1 hcg).1
          omega
        have hc : s.getD 0 0 ≤ c := head_le_of_mem hs (hsub.subset (by simp))
        have he : e ≤ s.getD (s.length - 1) 0 := le_last_of_mem s hs e (hsub.subset (by simp))
        omega

  /-! ### Correctness of the insertion-sort model of `sort` -/

  theorem i64_cmp_eq (x y : Std.I64) : core.cmp.OrdI64.cmp x y = ok (compare x.val y.val) := by
    simp [core.cmp.OrdI64, liftFun2]

  theorem cmp_gt_val {x y : Std.I64} (h : (compare x.val y.val == Ordering.gt) = true) :
      y.val < x.val :=
    compare_gt_iff_gt.1 (beq_iff_eq.1 h)

  theorem cmp_le_val {x y : Std.I64} (h : ¬ ((compare x.val y.val == Ordering.gt) = true)) :
      x.val ≤ y.val := by
    have h1 : compare x.val y.val ≠ Ordering.gt := fun hc => h (by simp [hc])
    by_contra hc
    push_neg at hc
    exact h1 (compare_gt_iff_gt.2 hc)

  theorem pairwise_le_cons_val {a : Std.I64} {l : List Std.I64}
      (h1 : ∀ z ∈ l, a.val ≤ z.val)
      (h2 : l.Pairwise (fun a b : Std.I64 => a.val ≤ b.val)) :
      (a :: l).Pairwise (fun a b : Std.I64 => a.val ≤ b.val) :=
    List.pairwise_cons.2 ⟨h1, h2⟩

  theorem sortInsert_cons_val (x y : Std.I64) (ys : List Std.I64) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x (y :: ys) =
        (if (compare x.val y.val == Ordering.gt) = true then
          (do let r ← AegisShim.sortInsert core.cmp.OrdI64.cmp x ys; ok (y :: r))
         else ok (x :: y :: ys)) := by
    simp [AegisShim.sortInsert, core.cmp.OrdI64, liftFun2]

  theorem sortList_cons_val (x : Std.I64) (xs : List Std.I64) :
      AegisShim.sortList core.cmp.OrdI64.cmp (x :: xs) =
        (do let r ← AegisShim.sortList core.cmp.OrdI64.cmp xs
            AegisShim.sortInsert core.cmp.OrdI64.cmp x r) := by
    simp [AegisShim.sortList]

  theorem sortInsert_spec (x : Std.I64) :
      ∀ (l : List Std.I64), l.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) →
        ∃ l', AegisShim.sortInsert core.cmp.OrdI64.cmp x l = ok l' ∧
          l'.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) ∧ l'.Perm (x :: l)
    | [], _ => ⟨[x], by simp [AegisShim.sortInsert], by simp, by simp⟩
    | y :: ys, hs => by
        obtain ⟨hy, hs'⟩ := List.pairwise_cons.1 hs
        obtain ⟨r, hr, hrsorted, hrperm⟩ := sortInsert_spec x ys hs'
        by_cases hgt : (compare x.val y.val == Ordering.gt) = true
        · have hxy : y.val ≤ x.val := le_of_lt (cmp_gt_val hgt)
          refine ⟨y :: r, ?_, ?_, ?_⟩
          · rw [sortInsert_cons_val, if_pos hgt]
            simp [hr]
          · exact pairwise_le_cons_val
              (fun z hz => by
                have hmem : z ∈ x :: ys := hrperm.subset hz
                rcases List.mem_cons.1 hmem with rfl | hz'
                · omega
                · exact hy z hz')
              hrsorted
          · exact (List.Perm.cons y hrperm).trans (List.Perm.swap x y ys)
        · have hxy : x.val ≤ y.val := cmp_le_val hgt
          refine ⟨x :: y :: ys, ?_, pairwise_le_cons_val ?_ (pairwise_le_cons_val hy hs'), ?_⟩
          · rw [sortInsert_cons_val, if_neg hgt]
          · intro z hz
            rcases List.mem_cons.1 hz with rfl | hz'
            · omega
            · exact le_trans hxy (hy z hz')
          · exact List.Perm.refl _

  theorem sortList_spec :
      ∀ (l : List Std.I64),
        ∃ l', AegisShim.sortList core.cmp.OrdI64.cmp l = ok l' ∧
          l'.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) ∧ l'.Perm l
    | [] => ⟨[], by simp [AegisShim.sortList], by simp, by simp⟩
    | x :: xs => by
        obtain ⟨r, hr, hrsorted, hrperm⟩ := sortList_spec xs
        obtain ⟨l', hl', hl'sorted, hl'perm⟩ := sortInsert_spec x r hrsorted
        refine ⟨l', ?_, hl'sorted, hl'perm.trans (List.Perm.cons x hrperm)⟩
        rw [sortList_cons_val, hr]
        simp [hl']

  theorem slice_sort_spec (s : Slice Std.I64) :
      ∃ s', alloc.slice.Slice.sort (T := Std.I64) core.cmp.OrdI64 s = ok s' ∧
        s'.val.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) ∧ s'.val.Perm s.val := by
    obtain ⟨l, hl, hlsorted, hlperm⟩ := sortList_spec s.val
    have hlen : l.length ≤ Usize.max := by
      rw [hlperm.length_eq]
      exact s.property
    refine ⟨Slice.from l hlen, ?_, ?_, ?_⟩
    · simp only [alloc.slice.Slice.sort]
      rw [hl]
      simp [hlen]
    · simpa using hlsorted
    · simpa using hlperm

  /-! ### The copy loop `maximum_tastiness_loop0` -/

  theorem loop0_aux (price : Slice Std.I64) (n : Std.Usize) (hn : n.val = price.val.length)
      (hmax : price.val.length < Usize.max) (v : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hi : i.val ≤ n.val) (hval : v.val = price.val.take i.val) :
      loop (fun p : alloc.vec.Vec Std.I64 × Std.Usize =>
          Aegis.MaximumTastiness.maximum_tastiness_loop0.body price n p.1 p.2) (v, i)
        ⦃ (r : alloc.vec.Vec Std.I64) => r.val = price.val ⦄ := by
    apply loop.spec_decr_nat
      (fun p : alloc.vec.Vec Std.I64 × Std.Usize => n.val - p.2.val)
      (fun p => p.2.val ≤ n.val ∧ p.1.val = price.val.take p.2.val)
      (fun r : alloc.vec.Vec Std.I64 => r.val = price.val)
    · rintro ⟨sorted, i'⟩ ⟨hi', hval'⟩
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
      by_cases hlt : i' < n
      · rw [if_pos hlt]
        have hltv : i'.val < n.val := by simpa using hlt
        have hilen : i'.val < price.val.length := by rw [← hn]; exact hltv
        apply WP.spec_bind (Slice.index_usize_spec price i' hilen)
        intro i1 hi1
        have hlen_take : sorted.val.length < Usize.max := by
          have h1 : sorted.val.length ≤ price.val.length := by
            rw [hval', List.length_take]; exact Nat.min_le_right _ _
          exact Nat.lt_of_le_of_lt h1 hmax
        apply WP.spec_bind (alloc.vec.Vec.push_spec sorted i1 hlen_take)
        intro sorted1 hsorted1
        apply WP.spec_bind (Usize.add_spec (x := i') (y := 1#usize) (by
          have h1 : i'.val + 1 ≤ price.val.length := hn ▸ Nat.succ_le_of_lt hltv
          exact Nat.le_trans h1 (Nat.le_of_lt hmax)))
        intro i2 hi2
        have hi2v : i2.val = i'.val + 1 := hi2
        simp only [WP.spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hsorted1, hval', hi2v, List.take_add_one, hi1]
        rw [List.getElem?_eq_getElem (by omega : i'.val < price.val.length)]
        simp
      · rw [if_neg hlt]
        have hgev : price.val.length ≤ i'.val := by
          have h1 : ¬ (i'.val < n.val) := by simpa using hlt
          have h2 : n.val ≤ i'.val := Nat.le_of_not_lt h1
          rwa [hn] at h2
        simp only [WP.spec_ok]
        rw [hval', List.take_of_length_le hgev]
    · exact ⟨hi, hval⟩

  theorem loop0_spec (price : Slice Std.I64) (n : Std.Usize) (hn : n.val = price.val.length)
      (hmax : price.val.length < Usize.max) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n (alloc.vec.Vec.new Std.I64) 0#usize
        ⦃ (r : alloc.vec.Vec Std.I64) => r.val = price.val ⦄ := by
    have h := loop0_aux price n hn hmax (alloc.vec.Vec.new Std.I64) 0#usize (by simp) (by
      show (alloc.vec.Vec.new Std.I64).val = price.val.take 0
      simp [alloc.vec.Vec.new])
    exact h

  /-! ### The `can_make` decision procedure -/

  /-- The integer values of a list of machine integers. -/
  def toZ (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  @[simp] theorem toZ_nil : toZ [] = [] := rfl

  @[simp] theorem toZ_cons (x : Std.I64) (l : List Std.I64) : toZ (x :: l) = x.val :: toZ l := rfl

  theorem toZ_drop (l : List Std.I64) (i : ℕ) : toZ (l.drop i) = (toZ l).drop i :=
    List.map_drop

  theorem toZ_length (l : List Std.I64) : (toZ l).length = l.length := List.length_map _

  theorem head_le_of_mem_i64 {l : List Std.I64}
      (hs : l.Pairwise (fun a b : Std.I64 => a.val ≤ b.val)) {y : Std.I64} (hy : y ∈ l) :
      (l.getD 0 (0#i64)).val ≤ y.val := by
    cases l with
    | nil => simp at hy
    | cons a l' =>
        have h1 : a.val ≤ y.val := by
          rcases List.mem_cons.1 hy with rfl | hyl
          · omega
          · exact List.rel_of_pairwise_cons hs hyl
        simpa using h1

  theorem le_of_mem_drop {l : List Std.I64}
      (hs : l.Pairwise (fun a b : Std.I64 => a.val ≤ b.val)) {i : ℕ} (hi : i < l.length)
      {y : Std.I64} (hy : y ∈ l.drop (i + 1)) : (l[i]).val ≤ y.val := by
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.1 hy
    have hjl : i + 1 + j < l.length := by
      have := hj
      rw [List.length_drop] at this
      omega
    have : (l.drop (i + 1))[j] = l[i + 1 + j] := List.getElem_drop
    rw [← hjy, this]
    exact List.Pairwise.rel_getElem_of_lt hi hjl hs (by omega)

  theorem can_make_loop_aux (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize) (C : ℤ)
      (hn : n.val = sorted.val.length) (hnb : n.val ≤ 100000)
      (hsorted : sorted.val.Pairwise (fun a b : Std.I64 => a.val ≤ b.val))
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : 0 ≤ d.val) (hk : 2 ≤ k.val) :
      ∀ (count last : Std.I64) (i : Std.Usize), i.val ≤ n.val →
        (∀ x ∈ sorted.val.drop i.val, last.val ≤ x.val) →
        1 ≤ last.val → last.val ≤ 1000000000 →
        0 ≤ count.val → count.val ≤ (i.val : ℤ) + 1 →
        count.val +
          ((gsel d.val (last.val + d.val) (toZ (sorted.val.drop i.val))).length : ℤ) = C →
        loop (fun p : Std.I64 × Std.I64 × Std.Usize =>
          Aegis.MaximumTastiness.can_make_loop.body sorted k d n p.1 p.2.1 p.2.2)
          (count, last, i) ⦃ b => b = decide (C ≥ k.val) ⦄ := by
    intro count0 last0 i0 hic0 hlast0 hlb0 hlu0 hc0 hcu0 hC0
    apply loop.spec_decr_nat
      (fun p : Std.I64 × Std.I64 × Std.Usize => n.val - p.2.2.val)
      (fun p => p.2.2.val ≤ n.val ∧ (∀ x ∈ sorted.val.drop p.2.2.val, p.2.1.val ≤ x.val) ∧
        1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000 ∧ 0 ≤ p.1.val ∧
        p.1.val ≤ (p.2.2.val : ℤ) + 1 ∧
        p.1.val +
          ((gsel d.val (p.2.1.val + d.val) (toZ (sorted.val.drop p.2.2.val))).length : ℤ) = C)
      (fun b => b = decide (C ≥ k.val))
    · rintro ⟨count, last, i⟩ ⟨hic, hlast, hlb, hlu, hc, hcu, hC⟩
      dsimp only at *
      unfold Aegis.MaximumTastiness.can_make_loop.body
      by_cases hlt : i < n
      · rw [if_pos hlt]
        have hltv : i.val < n.val := by simpa using hlt
        have hiv : i.val < sorted.val.length := by rw [← hn]; exact hltv
        apply WP.spec_bind (Slice.index_usize_spec sorted i hiv)
        intro i1 hi1
        obtain ⟨hi1lo, hi1hi⟩ := hbnd i1 (by rw [hi1]; exact List.getElem_mem hiv)
        apply WP.spec_bind (I64.sub_spec (x := i1) (y := last) (by scalar_tac) (by scalar_tac))
        intro i2 hi2
        have hd1 : sorted.val.drop i.val = i1 :: sorted.val.drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hiv, hi1]
        have hd1Z : toZ (sorted.val.drop i.val) =
            i1.val :: toZ (sorted.val.drop (i.val + 1)) := by
          rw [hd1, toZ_cons]
        by_cases hge : i2 >= d
        · rw [if_pos hge]
          have hge' : last.val + d.val ≤ i1.val := by
            have h1 : d.val ≤ i2.val := by simpa using hge
            omega
          apply WP.spec_bind (I64.add_spec (x := count) (y := 1#i64) (by scalar_tac)
            (by scalar_tac))
          intro count1 hcount1
          have hcount1v : count1.val = count.val + 1 := hcount1
          by_cases hck : count1 >= k
          · rw [if_pos hck]
            simp only [WP.spec_ok]
            have h1 : k.val ≤ count1.val := by simpa using hck
            have hlen1 : 1 ≤ (gsel d.val (last.val + d.val)
                (toZ (sorted.val.drop i.val))).length := by
              rw [hd1Z, gsel_cons, if_pos hge']
              simp
            have hCP : C ≥ k.val := by omega
            simp [hCP]
          · rw [if_neg hck]
            apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
            intro i3 hi3
            have hi3v : i3.val = i.val + 1 := hi3
            have hd3 : sorted.val.drop i3.val = sorted.val.drop (i.val + 1) := by rw [hi3v]
            simp only [WP.spec_ok]
            have hlen' : (gsel d.val (last.val + d.val)
                (toZ (sorted.val.drop i.val))).length =
                1 + (gsel d.val (i1.val + d.val)
                  (toZ (sorted.val.drop (i.val + 1)))).length := by
              rw [hd1Z, gsel_cons, if_pos hge']
              simp only [List.length_cons]
              omega
            refine ⟨⟨by omega, ?_, hi1lo, hi1hi, by omega, by omega, ?_⟩, by omega⟩
            · intro y hy
              rw [hd3] at hy
              have h := le_of_mem_drop hsorted hiv hy
              rw [hi1]
              exact h
            · rw [hd3]
              omega
        · rw [if_neg hge]
          have hge' : ¬ (last.val + d.val ≤ i1.val) := by
            intro h1
            apply hge
            have h2 : i2.val = i1.val - last.val := hi2
            have h3 : d.val ≤ i2.val := by omega
            simpa using h3
          apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          intro i3 hi3
          have hi3v : i3.val = i.val + 1 := hi3
          have hd3 : sorted.val.drop i3.val = sorted.val.drop (i.val + 1) := by rw [hi3v]
          simp only [WP.spec_ok]
          have hlen' : (gsel d.val (last.val + d.val)
              (toZ (sorted.val.drop i.val))).length =
              (gsel d.val (last.val + d.val)
                (toZ (sorted.val.drop (i.val + 1)))).length := by
            rw [hd1Z, gsel_cons, if_neg hge']
          refine ⟨⟨by omega, ?_, hlb, hlu, hc, by omega, ?_⟩, by omega⟩
          · intro y hy
            rw [hd3] at hy
            exact hlast y (by rw [hd1]; exact List.mem_cons_of_mem i1 hy)
          · rw [hd3]
            rw [hlen'] at hC
            exact hC
      · rw [if_neg hlt]
        have hge : n.val ≤ i.val := by
          have h1 : ¬ (i.val < n.val) := by simpa using hlt
          exact Nat.le_of_not_lt h1
        have hnil : sorted.val.drop i.val = [] := by
          apply List.drop_eq_nil_of_le
          rw [← hn]; exact hge
        have hgz : gsel d.val (last.val + d.val) (toZ (sorted.val.drop i.val)) = [] := by
          rw [hnil]; rfl
        rw [hgz] at hC
        simp only [List.length_nil, Nat.cast_zero, add_zero] at hC
        simp only [WP.spec_ok]
        simp [hC]
    · exact ⟨hic0, hlast0, hlb0, hlu0, hc0, hcu0, hC0⟩

  theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hnb : sorted.val.length ≤ 100000)
      (hsorted : sorted.val.Pairwise (fun a b : Std.I64 => a.val ≤ b.val))
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hd : 0 ≤ d.val) (hk : 2 ≤ k.val) (hlen : 2 ≤ sorted.val.length) :
      Aegis.MaximumTastiness.can_make sorted k d
        ⦃ b => b = canMake k.val d.val (toZ sorted.val) ⦄ := by
    have hnlen : (Slice.len sorted).val = sorted.val.length := rfl
    obtain ⟨x, xs, hxs⟩ : ∃ x xs, sorted.val = x :: xs := by
      match hv : sorted.val with
      | [] => rw [hv] at hlen; simp at hlen
      | y :: ys => exact ⟨y, ys, rfl⟩
    unfold Aegis.MaximumTastiness.can_make
    by_cases hks : k <= 1#i64
    · exfalso
      have h1 : k.val ≤ 1 := by simpa using hks
      omega
    · rw [if_neg hks]
      apply WP.spec_bind (Slice.index_usize_spec sorted 0#usize (by
        show (0#usize).val < sorted.val.length
        have h0 : (0#usize).val = 0 := by simp
        omega))
      intro last hlast
      have hlastv : last = x := by
        rw [hlast]
        simp [hxs]
      have hdrop : (sorted.val.drop (1#usize).val) = xs := by rw [hxs]; rfl
      have hlen' : ∀ y ∈ sorted.val.drop (1#usize).val, last.val ≤ y.val := by
        intro y hy
        rw [hlastv]
        rw [hdrop] at hy
        have hs' : (x :: xs).Pairwise (fun a b : Std.I64 => a.val ≤ b.val) := by
          rw [← hxs]; exact hsorted
        exact List.rel_of_pairwise_cons hs' hy
      have hlastb : 1 ≤ last.val ∧ last.val ≤ 1000000000 := by
        rw [hlastv]
        have hm : x ∈ sorted.val := by rw [hxs]; exact List.mem_cons_self
        exact hbnd x hm
      have hlen1 : (1#usize).val ≤ (Slice.len sorted).val := by
        show (1#usize).val ≤ sorted.val.length
        have h1 : (1#usize).val = 1 := by simp
        omega
      have hC' : (1#i64).val +
          ((gsel d.val (last.val + d.val) (toZ (sorted.val.drop (1#usize).val))).length : ℤ) =
          1 + ((gsel d.val (last.val + d.val)
            (toZ (sorted.val.drop (1#usize).val))).length : ℤ) := by norm_num
      have hres := can_make_loop_aux sorted k d (Slice.len sorted)
        (1 + ((gsel d.val (last.val + d.val)
          (toZ (sorted.val.drop (1#usize).val))).length : ℤ))
        hnlen hnb hsorted hbnd hd hk (1#i64) last 1#usize hlen1 hlen'
        hlastb.1 hlastb.2 (by norm_num) (by norm_num) hC'
      apply WP.spec_mono hres
      intro b hb
      rw [hb, canMake, if_neg (by omega : ¬ k.val ≤ 1)]
      have hgreed : greed d.val (toZ sorted.val) =
          x.val :: gsel d.val (x.val + d.val) (toZ xs) := by
        rw [hxs]
        rfl
      rw [hgreed, List.length_cons, hdrop, hlastv]
      have hiff : (1 + ((gsel d.val (x.val + d.val) (toZ xs)).length : ℤ) ≥ k.val) ↔
          (k.val.toNat ≤ (gsel d.val (x.val + d.val) (toZ xs)).length + 1) := by
        rw [Int.toNat_le]
        constructor <;> intro h <;> omega
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      exact hiff

  /-! ### The binary search loop `maximum_tastiness_loop1` -/

  theorem tdiv_two_lt {a : ℤ} (h : 0 < a) : a.tdiv 2 < a := by
    have h2 : a.tdiv 2 = a / 2 := by
      rw [Int.tdiv_eq_ediv, if_pos (Or.inl (by omega)), add_zero]
    rw [h2, Int.ediv_lt_iff_lt_mul (by norm_num)]
    omega

  theorem one_le_tdiv_two {a : ℤ} (h : 2 ≤ a) : 1 ≤ a.tdiv 2 := by
    have := Int.le_tdiv_of_mul_le (c := (2 : ℤ)) (a := (1 : ℤ)) (b := a) (by norm_num) (by omega)
    simpa using this

  theorem loop1_aux (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (hsorted : sorted.val.Pairwise (fun a b : Std.I64 => a.val ≤ b.val))
      (hbnd : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hslen : sorted.val.length ≤ 100000)
      (hklen : k.val.toNat ≤ sorted.val.length) (hk : 2 ≤ k.val) :
      ∀ (lo hi : Std.I64), 0 ≤ lo.val → lo.val ≤ hi.val → hi.val ≤ 1000000001 →
        (∀ d : ℤ, hi.val ≤ d → canMake k.val d (toZ sorted.val) = false) →
        loop (fun p : Std.I64 × Std.I64 =>
          Aegis.MaximumTastiness.maximum_tastiness_loop1.body k sorted p.1 p.2) (lo, hi)
          ⦃ (r : Std.I64) => lo.val ≤ r.val ∧
            ∀ d : ℤ, r.val + 1 ≤ d → canMake k.val d (toZ sorted.val) = false ⦄ := by
    intro lo hi hlo hlohi hhi hinv
    apply loop.spec_decr_nat
      (fun p : Std.I64 × Std.I64 => (p.2.val - p.1.val).toNat)
      (fun p => lo.val ≤ p.1.val ∧ 0 ≤ p.1.val ∧ p.1.val ≤ p.2.val ∧ p.2.val ≤ 1000000001 ∧
        (∀ d : ℤ, p.2.val ≤ d → canMake k.val d (toZ sorted.val) = false))
      (fun r : Std.I64 => lo.val ≤ r.val ∧
        ∀ d : ℤ, r.val + 1 ≤ d → canMake k.val d (toZ sorted.val) = false)
    · rintro ⟨lo', hi'⟩ ⟨hle_lo, hlo', hle', hhi', hinv'⟩
      dsimp only at *
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
      apply WP.spec_bind (I64.add_spec (x := lo') (y := 1#i64) (by scalar_tac) (by scalar_tac))
      intro i hiadd
      have hiv : i.val = lo'.val + 1 := by
        have h1 : (1#i64).val = 1 := by norm_num
        rw [hiadd, h1]
      by_cases hlt : i < hi'
      · rw [if_pos hlt]
        have hltv : i.val < hi'.val := by simpa using hlt
        apply WP.spec_bind (I64.sub_spec (x := hi') (y := lo') (by scalar_tac) (by scalar_tac))
        intro i1 hi1
        have hi1v : i1.val = hi'.val - lo'.val := hi1
        have hi1ge : 2 ≤ i1.val := by omega
        have hi1nn : 0 ≤ i1.val := by omega
        apply WP.spec_bind (I64.div_spec (x := i1) (y := 2#i64) (by norm_num) (by norm_num))
        intro i2 hi2
        have hi2v : i2.val = i1.val.tdiv 2 := hi2
        have hi2nn : 0 ≤ i2.val := by
          rw [hi2v]; exact Int.tdiv_nonneg hi1nn (by norm_num)
        have hi2le : i2.val ≤ i1.val := by
          rw [hi2v]; exact Int.tdiv_le_self 2 hi1nn
        have hi2ge1 : 1 ≤ i2.val := by rw [hi2v]; exact one_le_tdiv_two hi1ge
        have hi2lt : i2.val < i1.val := by rw [hi2v]; exact tdiv_two_lt (by omega)
        apply WP.spec_bind (I64.add_spec (x := lo') (y := i2) (by scalar_tac) (by scalar_tac))
        intro mid hmid
        have hmidv : mid.val = lo'.val + i2.val := hmid
        have hmidlo : lo'.val < mid.val := by omega
        have hmidhi : mid.val < hi'.val := by omega
        have hmidnn : 0 ≤ mid.val := by omega
        have hmidhi2 : mid.val ≤ 1000000001 := by omega
        have hderef : (alloc.vec.Vec.deref sorted).val = sorted.val := by
          simp [alloc.vec.Vec.deref]
        apply WP.spec_bind (can_make_spec (alloc.vec.Vec.deref sorted) k mid
          (by rw [hderef]; exact hslen) (by rw [hderef]; exact hsorted)
          (by rw [hderef]; exact hbnd) hmidnn hk (by rw [hderef]; omega))
        intro b hb
        rw [hderef] at hb
        by_cases hbt : b = true
        · rw [if_pos hbt]
          simp only [WP.spec_ok]
          have hmeas : (hi'.val - mid.val).toNat < (hi'.val - lo'.val).toNat := by
            rw [Int.toNat_lt_toNat (by omega)]
            omega
          exact ⟨⟨by omega, by omega, by omega, hhi', hinv'⟩, hmeas⟩
        · rw [if_neg hbt]
          simp only [WP.spec_ok]
          have hbf : b = false := by
            cases b
            · rfl
            · exact absurd rfl hbt
          have hcmf : canMake k.val mid.val (toZ sorted.val) = false := by
            rw [← hb, hbf]
          have hmeas : (mid.val - lo'.val).toNat < (hi'.val - lo'.val).toNat := by
            rw [Int.toNat_lt_toNat (by omega)]
            omega
          refine ⟨⟨hle_lo, hlo', by omega, by omega, ?_⟩, hmeas⟩
          intro d hd
          by_contra hc
          have hcd : canMake k.val d (toZ sorted.val) = true := by
            cases h : canMake k.val d (toZ sorted.val)
            · exact absurd h hc
            · rfl
          have hks' : k.val.toNat ≤ (toZ sorted.val).length := by
            rw [toZ_length]; exact hklen
          have hs' : (toZ sorted.val).Pairwise (· ≤ ·) :=
            hsorted.map (fun x : Std.I64 => x.val) (fun a b h => h)
          have hmono : canMake k.val mid.val (toZ sorted.val) = true :=
            canMake_mono (k := k.val) (d := d) (d' := mid.val) (s := toZ sorted.val)
              hd (by omega) hmidnn hks' hs' (by omega) hcd
          rw [hcmf] at hmono
          exact absurd hmono (by simp)
      · rw [if_neg hlt]
        have hge : hi'.val ≤ lo'.val + 1 := by
          have h1 : ¬ (i.val < hi'.val) := by simpa using hlt
          omega
        simp only [WP.spec_ok]
        refine ⟨hle_lo, ?_⟩
        intro d hd
        exact hinv' d (by omega)
    · dsimp only
      exact ⟨by omega, hlo, hlohi, hhi, hinv⟩

  /-! ### Extracting an `ok` result from a total-correctness specification -/

  unseal Aeneas.Std.Result in
  theorem spec_exists_ok {α : Type} {m : Result α} {p : WP.Post α} (h : WP.spec m p) :
      ∃ r : α, m = ok r ∧ p r := by
    have hmain := Aeneas.Data.Coinductive.DWP.induction (θ := WP.effectWP)
      (Q := fun value (_ : Unit) => p value)
      (P := fun t (_ : Unit) => ∃ r : α, t = Aeneas.Data.Coinductive.ITree.ret r ∧ p r)
      (by intro value s hv; exact ⟨value, rfl, hv⟩)
      (by
        intro effect kk s hwp
        cases effect with
        | fail e => exact absurd hwp (by simp [WP.effectWP]))
      h
    exact hmain

  /-! ### More lemmas about `PairDists` and `ConsecGaps` -/

  theorem absDiff_self (a : ℤ) : absDiff a a = 0 := by
    simp [absDiff]

  theorem pairDists_tail {d a : ℤ} {l : List ℤ} (h : PairDists d (a :: l)) : PairDists d l := by
    intro i j hij hj
    have h0 := h (i + 1) (j + 1) (by omega) (by simpa using hj)
    simpa using h0

  theorem pairDists_head {d a : ℤ} {l : List ℤ} (h : PairDists d (a :: l)) :
      ∀ y ∈ l, d ≤ absDiff a y := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := List.mem_iff_getElem.1 hy
    have h0 := h 0 (p + 1) (by omega) (by simp [hp])
    have h1 : (a :: l).getD 0 (0 : ℤ) = a := rfl
    have h2 : (a :: l).getD (p + 1) (0 : ℤ) = l[p] := by
      rw [List.getD_eq_getElem _ _ (by simp [hp])]
      simp
    rw [h1, h2, hpy] at h0
    exact h0

  theorem pairDists_distinct {d : ℤ} {T : List ℤ} (h : PairDists d T) :
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → d ≤ absDiff a b := by
    intro a ha b hb hab
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 ha
    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.1 hb
    have hne : i ≠ j := by
      intro hij
      subst hij
      exact hab (by rw [← hia, hjb])
    rcases Nat.lt_or_gt_of_ne hne with hij | hij
    · have h0 := h i j hij hj
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hia, hjb] at h0
      exact h0
    · have h0 := h j i hij hi
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi, hjb, hia,
        absDiff_comm] at h0
      exact h0

  theorem nodup_of_pairDists {d : ℤ} {T : List ℤ} (hd : 0 < d) (h : PairDists d T) :
      T.Nodup := by
    match T with
    | [] => simp
    | a :: l =>
        rw [List.nodup_cons]
        refine ⟨?_, nodup_of_pairDists hd (pairDists_tail h)⟩
        intro ha
        have h1 := pairDists_head h a ha
        rw [absDiff_self] at h1
        omega

  theorem consecGaps_of_sorted_of_nonpos {d : ℤ} (hd : d ≤ 0) :
      ∀ {T : List ℤ}, T.Pairwise (· ≤ ·) → ConsecGaps d T
    | [], _ => trivial
    | [_], _ => trivial
    | a :: b :: rest, hord => by
        have hle : a ≤ b := List.rel_of_pairwise_cons hord (by simp)
        exact ⟨by omega, consecGaps_of_sorted_of_nonpos hd (List.Pairwise.of_cons hord)⟩

  theorem consecGaps_of_sorted_distinct {d : ℤ} :
      ∀ {T : List ℤ}, T.Pairwise (· ≤ ·) → T.Nodup →
        (∀ a ∈ T, ∀ b ∈ T, a ≠ b → d ≤ absDiff a b) → ConsecGaps d T
    | [], _, _, _ => trivial
    | [_], _, _, _ => trivial
    | a :: b :: rest, hord, hnd, hdist => by
        have hle : a ≤ b := List.rel_of_pairwise_cons hord (by simp)
        have hne : a ≠ b := by
          intro hab
          have h1 := (List.nodup_cons.1 hnd).1
          exact h1 (hab ▸ List.mem_cons_self)
        have h1 : a + d ≤ b := by
          have h2 := hdist a (by simp) b (by simp) hne
          rw [absDiff_eq_of_le hle] at h2
          omega
        refine ⟨h1, consecGaps_of_sorted_distinct (List.Pairwise.of_cons hord)
          (List.Nodup.of_cons hnd) ?_⟩
        intro x hx y hy hxy
        exact hdist x (by simp [hx]) y (by simp [hy]) hxy

  theorem consecGaps_of_perm {d : ℤ} {T T' : List ℤ} (hp : T.Perm T')
      (hs : T'.Pairwise (· ≤ ·)) (h : PairDists d T) : ConsecGaps d T' := by
    by_cases hpos : 0 < d
    · exact consecGaps_of_sorted_distinct hs ((nodup_of_pairDists hpos h).perm hp)
        (fun a ha b hb hab =>
          pairDists_distinct h a (hp.symm.subset ha) b (hp.symm.subset hb) hab)
    · exact consecGaps_of_sorted_of_nonpos (by omega) hs

  /-! ### From a selection to the decision procedure -/

  theorem canMake_of_selection {s L : List ℤ} {S : Finset ℕ} {d kk : ℤ}
      (hs : s.Pairwise (· ≤ ·)) (hperm : s.Perm L) (hd : 0 ≤ d)
      (hSsub : S ⊆ Finset.range L.length) (hScard : S.card = kk.toNat)
      (hmin : ∀ i ∈ S, ∀ j ∈ S, i < j → d ≤ absDiff (L.getD i 0) (L.getD j 0))
      (hk1 : 1 ≤ kk) : canMake kk d s = true := by
    obtain ⟨T, hTsub, hTlen, hTpd⟩ := exists_sublist_pairDists hSsub hScard hmin
    have hT'perm : (T.insertionSort (· ≤ ·)).Perm T := List.perm_insertionSort _ T
    have hT'sorted : (T.insertionSort (· ≤ ·)).Pairwise (· ≤ ·) :=
      List.pairwise_insertionSort _ T
    have hT'len : (T.insertionSort (· ≤ ·)).length = kk.toNat := by
      rw [List.length_insertionSort, hTlen]
    have hT'sub : (T.insertionSort (· ≤ ·)).Sublist s := by
      refine List.sublist_of_subperm_of_pairwise ?_ hT'sorted hs
      exact (List.Perm.subperm hT'perm).trans ((List.Sublist.subperm hTsub).trans
        (List.Perm.subperm hperm.symm))
    have hcg : ConsecGaps d (T.insertionSort (· ≤ ·)) :=
      consecGaps_of_perm hT'perm.symm hT'sorted hTpd
    exact canMake_complete hs hd hT'len hT'sub hcg hk1

  theorem canMake_eq_false_of_gt {s : List ℤ} {kk d : ℤ} (hs : s.Pairwise (· ≤ ·))
      (hks : kk.toNat ≤ s.length) (hk2 : 2 ≤ kk.toNat) (hd : 0 ≤ d)
      (hspread : s.getD (s.length - 1) 0 - s.getD 0 0 < d) : canMake kk d s = false := by
    cases h : canMake kk d s with
    | false => rfl
    | true =>
        obtain ⟨T, hTsub, hTlen, hcg⟩ := canMake_sound hd hks h
        have h2 : 2 ≤ T.length := by rw [hTlen]; exact hk2
        have := gap_le_spread hs hTsub h2 hcg
        omega

  theorem tastinessOn_nonneg (l : List ℤ) (S : Finset ℕ) : 0 ≤ tastinessOn l S := by
    rw [tastinessOn]
    split
    · rename_i h
      refine Finset.le_min' _ h 0 ?_
      intro y hy
      simp only [pairDistsOn, Finset.mem_image] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact absDiff_nonneg (l.getD p.1 0) (l.getD p.2 0)
    · norm_num

  theorem toZ_getD (l : List Std.I64) (j : ℕ) :
      (toZ l).getD j 0 = (l.getD j (0#i64)).val := by
    have h := List.getD_map l (0#i64) (f := fun x : Std.I64 => x.val) (n := j)
    simpa [toZ] using h

  /-! ### The total-correctness proof of the main loop for `spec_S6` -/

  theorem tail_spec (price : Slice Std.I64) (k : Std.I64)
      (s : Slice Std.I64) (back : Slice Std.I64 → alloc.vec.Vec Std.I64)
      (hs : s.val = price.val) (hb : ∀ t, (back t).val = t.val)
      (h_n : 2 ≤ price.length) (h_k_lo : 2 ≤ k.val)
      (h_k_hi : k.val ≤ (price.length : ℤ)) (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      (do
        let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 s
        let i ← Slice.len price - 1#usize
        let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) (back s1) i
        let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) (back s1) 0#usize
        let max_diff ← i1 - i2
        let hi ← max_diff + 1#i64
        Aegis.MaximumTastiness.maximum_tastiness_loop1 k (back s1) 0#i64 hi) ⦃
        (r : Std.I64) => ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length →
          S.card = k.val.toNat → tastinessOn (vals price) S ≤ r.val ⦄ := by
    obtain ⟨s1, hs1eq, hs1sorted, hs1perm⟩ := slice_sort_spec s
    rw [hs1eq]
    simp only [bind_ok]
    have hlen_eq : price.length = price.val.length := rfl
    have h1us : (1#usize).val = 1 := by simp
    have h0us : (0#usize).val = 0 := by simp
    have h1i : (1#i64).val = 1 := by simp
    have h0i : (0#i64).val = 0 := by simp
    have hs1len : s1.val.length = price.length := by rw [hs1perm.length_eq, hs]
    have hblen : (back s1).val.length = s1.val.length := by rw [hb]
    have hblen' : (back s1).val.length = price.length := by rw [hblen, hs1len]
    -- bounds of the elements of the sorted array
    have hs1mem : ∀ y ∈ s1.val, y ∈ price.val := fun y hy => by
      rw [← hs]; exact hs1perm.subset hy
    have hs1bnd : ∀ y ∈ s1.val, 1 ≤ y.val ∧ y.val ≤ 1000000000 := fun y hy =>
      h_price y (hs1mem y hy)
    apply WP.spec_bind (Usize.sub_spec (x := Slice.len price) (y := 1#usize) (by
      rw [Slice.len_val]; omega))
    intro i hi
    obtain ⟨hiv, -⟩ := hi
    have hiv' : i.val = price.length - 1 := by
      rw [hiv, Slice.len_val, h1us]
    have hib : i.val < (back s1).val.length := by omega
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec (back s1) i hib)
    intro i1 hi1
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec (back s1) 0#usize (by
      have h : (back s1).length = price.length := hblen'
      omega))
    intro i2 hi2
    have hi1' : i1 = (back s1).val.getD (price.length - 1) (0#i64) := by
      have h1 : (back s1).val.getD i.val (0#i64) = (back s1).val[i.val] :=
        List.getD_eq_getElem _ _ hib
      simp only [hiv'] at h1
      rw [hi1]
      simp only [hiv']
      exact h1.symm
    have hi2' : i2 = (back s1).val.getD 0 (0#i64) := by
      have h1 : (back s1).val.getD 0 (0#i64) = (back s1).val[0] :=
        List.getD_eq_getElem _ _ (by omega)
      rw [hi2]
      exact h1.symm
    have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
      rw [hi1']
      have hmem : (back s1).val.getD (price.length - 1) (0#i64) ∈ s1.val := by
        rw [hb, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem (by omega)
      exact hs1bnd _ hmem
    have hi2b : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
      rw [hi2']
      have hmem : (back s1).val.getD 0 (0#i64) ∈ s1.val := by
        rw [hb, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem (by omega)
      exact hs1bnd _ hmem
    have hsorted1 : (back s1).val.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) := by
      rw [hb]; exact hs1sorted
    have hi1mem : i1 ∈ (back s1).val := by
      rw [hi1]; exact List.getElem_mem hib
    have hi2le : i2.val ≤ i1.val := by
      have h1 := head_le_of_mem_i64 hsorted1 hi1mem
      have h2 : ((back s1).val.getD 0 (0#i64)).val = i2.val := by rw [hi2']
      omega
    apply WP.spec_bind (I64.sub_spec (x := i1) (y := i2) (by scalar_tac) (by scalar_tac))
    intro max_diff hmd
    have hmdv : max_diff.val = i1.val - i2.val := hmd
    apply WP.spec_bind (I64.add_spec (x := max_diff) (y := 1#i64) (by scalar_tac)
      (by scalar_tac))
    intro hi' hhi
    have hhiv : hi'.val = max_diff.val + 1 := by
      rw [hhi]; norm_num
    -- spread facts
    have hfirstZ : (toZ (back s1).val).getD 0 0 = i2.val := by
      rw [toZ_getD, ← hi2']
    have hlastZ : (toZ (back s1).val).getD ((toZ (back s1).val).length - 1) 0 = i1.val := by
      rw [toZ_getD, toZ_length, hblen', ← hi1']
    have hlenZ : (toZ (back s1).val).length = price.length := by
      rw [toZ_length, hblen']
    -- sortedness and permutation in `ℤ`
    have hsZ : (toZ (back s1).val).Pairwise (· ≤ ·) := by
      rw [show toZ (back s1).val = toZ s1.val by rw [hb]]
      exact hs1sorted.map (fun x : Std.I64 => x.val) (fun a b h => h)
    have hpermZ : (toZ (back s1).val).Perm (vals price) := by
      rw [show toZ (back s1).val = toZ s1.val by rw [hb]]
      have h2 := hs1perm.map (fun x : Std.I64 => x.val)
      rw [hs] at h2
      simpa [toZ, vals] using h2
    have hslenZ : (back s1).val.length ≤ 100000 := by omega
    have hks : k.val.toNat ≤ (toZ (back s1).val).length := by
      rw [hlenZ]
      have hk0 : 0 ≤ k.val := by omega
      have h1 : ((k.val.toNat : ℤ)) ≤ (price.length : ℤ) := by
        rw [Int.toNat_of_nonneg hk0]; exact h_k_hi
      exact_mod_cast h1
    have hk2 : 2 ≤ k.val.toNat := by
      have hk0 : 0 ≤ k.val := by omega
      have h1 : ((2 : ℤ)) ≤ ((k.val.toNat : ℤ)) := by
        rw [Int.toNat_of_nonneg hk0]; exact h_k_lo
      exact_mod_cast h1
    have hinv : ∀ d : ℤ, hi'.val ≤ d → canMake k.val d (toZ (back s1).val) = false := by
      intro d hd
      have hd0 : 0 ≤ d := by omega
      refine canMake_eq_false_of_gt hsZ hks hk2 hd0 ?_
      rw [hlastZ, hfirstZ]
      omega
    have hbnd1 : ∀ x ∈ (back s1).val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      rw [hb]; exact hs1bnd
    have hklen1 : k.val.toNat ≤ (back s1).val.length := by
      rw [hblen']
      have hk0 : 0 ≤ k.val := by omega
      have h1 : ((k.val.toNat : ℤ)) ≤ (price.length : ℤ) := by
        rw [Int.toNat_of_nonneg hk0]; exact h_k_hi
      exact_mod_cast h1
    refine WP.spec_mono (loop1_aux k (back s1) hsorted1 hbnd1 hslenZ hklen1 h_k_lo
      0#i64 hi' (by omega) (by omega) (by omega) hinv) ?_
    rintro r ⟨hr0, hinv'⟩ S hSsub hScard
    by_contra hcon
    push_neg at hcon
    have hmin : ∀ a ∈ S, ∀ b ∈ S, a < b →
        (r.val + 1) ≤ absDiff ((vals price).getD a 0) ((vals price).getD b 0) := by
      intro a ha b hb' hab
      have h2 : 1 < S.card := by rw [hScard]; omega
      have h3 := tastinessOn_le_absDiff (l := vals price) h2 ha hb' hab
      omega
    have hcan : canMake k.val (r.val + 1) (toZ (back s1).val) = true :=
      canMake_of_selection hsZ hpermZ (by omega) hSsub hScard hmin (by omega)
    have hfalse := hinv' (r.val + 1) (by omega)
    rw [hcan] at hfalse
    exact absurd hfalse (by simp)

  theorem maxT_spec (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_k_lo : 2 ≤ k.val)
      (h_k_hi : k.val ≤ (price.length : ℤ)) (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      maximum_tastiness price k ⦃ (r : Std.I64) =>
        ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length →
          S.card = k.val.toNat → tastinessOn (vals price) S ≤ r.val ⦄ := by
    have hmax : price.val.length < Usize.max := by
      have h1 : (100000 : ℕ) < Usize.max := by scalar_tac
      simp only [Slice.length] at h_len
      omega
    unfold maximum_tastiness
    dsimp only
    by_cases hz : Slice.len price = 0#usize
    · rw [if_pos hz]
      exfalso
      have h1 : price.val.length = 0 := by
        have h2 := Slice.len_val price
        rw [hz] at h2
        simpa using h2
      simp only [Slice.length] at h_n
      omega
    · rw [if_neg hz]
      apply WP.spec_bind (loop0_spec price (Slice.len price) (by simp) hmax)
      intro sorted hsorted
      refine WP.spec_bind (m := lift (alloc.vec.Vec.deref_mut sorted))
        (Pₘ := fun p : Slice Std.I64 × (Slice Std.I64 → alloc.vec.Vec Std.I64) =>
          p.1.val = price.val ∧ ∀ t, (p.2 t).val = t.val) ?_ ?_
      · simp only [lift, WP.spec_ok]
        exact ⟨hsorted, fun t => rfl⟩
      · rintro ⟨s, back⟩ ⟨hs, hb⟩
        change (do
          let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 s
          let i ← price.len - 1#usize
          let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64)
            (back s1) i
          let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64)
            (back s1) 0#usize
          let max_diff ← i1 - i2
          let hi ← max_diff + 1#i64
          Aegis.MaximumTastiness.maximum_tastiness_loop1 k (back s1) 0#i64 hi) ⦃
          (r : Std.I64) => ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length →
            S.card = k.val.toNat → tastinessOn (vals price) S ≤ r.val ⦄
        exact tail_spec price k s back hs hb h_n h_k_lo h_k_hi h_len h_price

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
  theorem spec_6 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ S : Finset ℕ, S ⊆ Finset.range (vals price).length → S.card = k.val.toNat →
          tastinessOn (vals price) S ≤ r.val := by
    obtain ⟨r, hr, hpost⟩ :=
      spec_exists_ok (maxT_spec price k h_n h_k_lo h_k_hi h_len h_price)
    exact ⟨r, hr, hpost⟩

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
