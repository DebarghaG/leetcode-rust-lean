import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_1` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary notions used in the proof of `spec_S1` -/

  /-- A selection of indices whose pairwise price differences are all at least `d`
  (increasing-index form). -/
  def SelOK (L : List ℤ) (d : ℤ) (S : Finset ℕ) : Prop :=
    ∀ i ∈ S, ∀ j ∈ S, i < j → d ≤ L.getD j 0 - L.getD i 0

  /-- There is a selection of `k` positions whose prices are pairwise at distance at
  least `d` (form matching the specification statements). -/
  def Pfair (L : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    ∃ S : Finset ℕ, S ⊆ Finset.range L.length ∧ S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d ≤ absDiff (L.getD i 0) (L.getD j 0)

  /-- There is a selection of `k` positions whose prices are pairwise at distance at
  least `d` (increasing-index form). -/
  def Pgood (L : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    ∃ S : Finset ℕ, S ⊆ Finset.range L.length ∧ SelOK L d S ∧ S.card = k

  /-- Loop invariant of the greedy test in `can_make`.  After scanning the prefix of
  length `i`, the greedy selection uses `cnt` positions, its largest index is `li`,
  no selection in the prefix is longer, and among the selections of maximal length it
  has the smallest largest index. -/
  def GInv (L : List ℤ) (d : ℤ) (i cnt li : ℕ) : Prop :=
    1 ≤ cnt ∧ li < i ∧
    (∃ S : Finset ℕ, S ⊆ Finset.range i ∧ SelOK L d S ∧ S.card = cnt ∧ S.sup id = li) ∧
    (∀ S : Finset ℕ, S ⊆ Finset.range i → SelOK L d S →
      S.card < cnt ∨ (S.card = cnt ∧ li ≤ S.sup id))

  /-! ### Elementary facts about `absDiff` and `getD` -/

  /-- Extract the value returned by a computation that satisfies a total-correctness
  specification. -/
  theorem spec_ok_exists {α : Type _} {m : Result α} {p : Aeneas.Std.WP.Post α}
      (h : m ⦃ p ⦄) : ∃ y, m = ok y ∧ p y := by
    revert h
    refine Result.cases m (motive := fun t => t ⦃ p ⦄ → ∃ y, t = ok y ∧ p y) ?_ ?_ ?_
    · intro r h; exact ⟨r, rfl, by simpa using h⟩
    · intro e k h; simp at h
    · intro h; simp at h

  theorem absDiff_nonneg (a b : ℤ) : 0 ≤ absDiff a b := Int.natCast_nonneg _

  theorem absDiff_self (a : ℤ) : absDiff a a = 0 := by
    simp [absDiff]

  theorem absDiff_of_le {a b : ℤ} (h : a ≤ b) : absDiff a b = b - a := by
    have h' : (0:ℤ) ≤ b - a := by omega
    unfold absDiff
    rw [show a - b = -(b - a) by ring, Int.natAbs_neg, Int.natAbs_of_nonneg h']

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    rw [absDiff, absDiff, show a - b = -(b - a) by ring, Int.natAbs_neg]

  theorem absDiff_eq_zero_iff {a b : ℤ} : absDiff a b = 0 ↔ a = b := by
    unfold absDiff
    rw [Int.natCast_eq_zero, Int.natAbs_eq_zero, sub_eq_zero]

  theorem getD_of_lt {L : List ℤ} {i : ℕ} (h : i < L.length) : L.getD i 0 = L[i] :=
    List.getD_eq_getElem L 0 h

  theorem getD_mono {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {i j : ℕ} (hij : i ≤ j)
      (hj : j < L.length) : L.getD i 0 ≤ L.getD j 0 := by
    rw [List.pairwise_iff_getElem] at hL
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · rw [getD_of_lt (lt_of_le_of_lt hij hj), getD_of_lt hj]
      exact hL i j (lt_of_le_of_lt hij hj) hj hlt

  /-! ### The threshold predicates and `maxTastiness` -/

  theorem mem_kSelections {l : List ℤ} {k : ℕ} {S : Finset ℕ} :
      S ∈ kSelections l k ↔ S ⊆ Finset.range l.length ∧ S.card = k := by
    simp [kSelections]

  theorem kSelections_nonempty {l : List ℤ} {k : ℕ} (h : k ≤ l.length) :
      (kSelections l k).Nonempty := by
    obtain ⟨S, hsub, hS⟩ := Finset.exists_subset_card_eq (s := Finset.range l.length)
      (by simpa using h)
    exact ⟨S, (mem_kSelections).2 ⟨hsub, hS⟩⟩

  theorem tastinessOn_nonneg (l : List ℤ) (S : Finset ℕ) : 0 ≤ tastinessOn l S := by
    unfold tastinessOn
    split_ifs with h
    · refine Finset.le_min' _ h _ ?_
      intro y hy
      unfold pairDistsOn at hy
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact absDiff_nonneg _ _
    · exact le_rfl

  theorem maxTastiness_nonneg (l : List ℤ) (k : ℕ) : 0 ≤ maxTastiness l k := by
    unfold maxTastiness
    split_ifs with h
    · obtain ⟨x, hx⟩ := Finset.Nonempty.image h (tastinessOn l)
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hx
      exact le_trans (tastinessOn_nonneg l S)
        (Finset.le_max' _ _ (Finset.mem_image.2 ⟨S, hS, rfl⟩))
    · exact le_rfl

  theorem le_maxTastiness_iff (l : List ℤ) {k : ℕ} {d : ℤ} (hk : 2 ≤ k)
      (hkn : k ≤ l.length) (hd : 0 ≤ d) : d ≤ maxTastiness l k ↔ Pfair l k d := by
    have _ : 0 ≤ d := hd
    have hne : (kSelections l k).Nonempty := kSelections_nonempty hkn
    constructor
    · intro hle
      unfold maxTastiness at hle
      rw [dite_eq_left hne] at hle
      have hmem := Finset.max'_mem ((kSelections l k).image (tastinessOn l))
        (Finset.Nonempty.image hne (tastinessOn l))
      obtain ⟨S, hS, hval⟩ := Finset.mem_image.1 hmem
      have hdS : d ≤ tastinessOn l S := by rw [hval]; exact hle
      have key : ∀ x ∈ pairDistsOn l S, tastinessOn l S ≤ x := by
        intro x hx
        unfold tastinessOn
        split_ifs with h
        · exact Finset.min'_le _ _ hx
        · exact absurd ⟨x, hx⟩ h
      obtain ⟨hsub, hcard⟩ := mem_kSelections.1 hS
      refine ⟨S, hsub, hcard, ?_⟩
      intro i hi j hj hij
      rcases Nat.lt_or_ge i j with hlt | hlt
      · have hmem2 : absDiff (l.getD i 0) (l.getD j 0) ∈ pairDistsOn l S := by
          unfold pairDistsOn
          exact Finset.mem_image.2
            ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hj⟩, hlt⟩, rfl⟩
        exact le_trans hdS (key _ hmem2)
      · have hmem2 : absDiff (l.getD j 0) (l.getD i 0) ∈ pairDistsOn l S := by
          unfold pairDistsOn
          exact Finset.mem_image.2
            ⟨(j, i), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hj, hi⟩, by omega⟩, rfl⟩
        rw [absDiff_comm]
        exact le_trans hdS (key _ hmem2)
    · intro hP
      obtain ⟨S, hsub, hcard, hP'⟩ := hP
      have hne2 : (pairDistsOn l S).Nonempty := by
        have hcard2 : 1 < S.card := by omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard2
        rcases lt_or_gt_of_ne hab with h | h
        · exact ⟨_, Finset.mem_image.2
            ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, h⟩, rfl⟩⟩
        · exact ⟨_, Finset.mem_image.2
            ⟨(b, a), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hb, ha⟩, h⟩, rfl⟩⟩
      have hdmin : d ≤ tastinessOn l S := by
        unfold tastinessOn
        rw [dite_eq_left hne2]
        refine Finset.le_min' _ hne2 _ ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨hpprod, hplt⟩ := Finset.mem_filter.1 hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hpprod
        exact hP' p.1 hp1 p.2 hp2 (ne_of_lt hplt)
      have hmax : tastinessOn l S ≤ maxTastiness l k := by
        unfold maxTastiness
        rw [dite_eq_left hne]
        exact Finset.le_max' _ _
          (Finset.mem_image.2 ⟨S, mem_kSelections.2 ⟨hsub, hcard⟩, rfl⟩)
      exact le_trans hdmin hmax

  theorem Pfair_iff_Pgood {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {k : ℕ} {d : ℤ}
      (hd : 0 ≤ d) : Pfair L k d ↔ Pgood L k d := by
    constructor
    · rintro ⟨S, hS, hcard, h⟩
      refine ⟨S, hS, ?_, hcard⟩
      intro i hi j hj hij
      have hle := getD_mono hL (le_of_lt hij) (Finset.mem_range.1 (hS hj))
      calc d ≤ absDiff (L.getD i 0) (L.getD j 0) := h i hi j hj (ne_of_lt hij)
        _ = L.getD j 0 - L.getD i 0 := absDiff_of_le hle
    · rintro ⟨S, hS, hOK, hcard⟩
      refine ⟨S, hS, hcard, ?_⟩
      intro i hi j hj hne
      rcases Nat.lt_or_gt_of_ne hne with hij | hij
      · have hle := getD_mono hL (le_of_lt hij) (Finset.mem_range.1 (hS hj))
        calc d ≤ L.getD j 0 - L.getD i 0 := hOK i hi j hj hij
          _ = absDiff (L.getD i 0) (L.getD j 0) := (absDiff_of_le hle).symm
      · have hle := getD_mono hL (le_of_lt hij) (Finset.mem_range.1 (hS hi))
        calc d ≤ L.getD i 0 - L.getD j 0 := hOK j hj i hi hij
          _ = absDiff (L.getD j 0) (L.getD i 0) := (absDiff_of_le hle).symm
          _ = absDiff (L.getD i 0) (L.getD j 0) := absDiff_comm _ _

  /-! ### Relabelling indices along a permutation -/

  /-- `IdxMap l l' σ` says that `σ` maps the index positions of `l` to index positions of
  `l'` injectively and preserves the stored values. -/
  def IdxMap (l l' : List ℤ) (σ : ℕ → ℕ) : Prop :=
    (∀ i, i < l.length → σ i < l'.length) ∧
      (∀ i, i < l.length → ∀ j, j < l.length → σ i = σ j → i = j) ∧
        (∀ i, i < l.length → l'.getD (σ i) 0 = l.getD i 0)

  theorem getD_cons_two (a b : ℤ) (l : List ℤ) (n : ℕ) :
      (a :: b :: l).getD (n + 2) 0 = l.getD n 0 := by
    rw [show n + 2 = n + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]

  theorem IdxMap_comp {l₁ l₂ l₃ : List ℤ} {σ τ : ℕ → ℕ} (hσ : IdxMap l₁ l₂ σ)
      (hτ : IdxMap l₂ l₃ τ) : IdxMap l₁ l₃ (fun i => τ (σ i)) := by
    obtain ⟨a1, a2, a3⟩ := hσ
    obtain ⟨b1, b2, b3⟩ := hτ
    refine ⟨fun i hi => b1 (σ i) (a1 i hi), ?_, ?_⟩
    · intro i hi j hj hij
      exact a2 i hi j hj (b2 (σ i) (a1 i hi) (σ j) (a1 j hj) hij)
    · intro i hi
      rw [b3 (σ i) (a1 i hi), a3 i hi]

  theorem exists_idxMap_of_perm {l l' : List ℤ} (h : l.Perm l') : ∃ σ, IdxMap l l' σ := by
    refine List.Perm.recOn h (motive := fun l l' _ => ∃ σ, IdxMap l l' σ) ?_ ?_ ?_ ?_
    · -- `nil`
      exact ⟨fun _ => 0, fun i hi => by simp at hi, fun i hi => by simp at hi,
        fun i hi => by simp at hi⟩
    · -- `cons`
      intro a l₁ l₂ _ ih
      obtain ⟨σ, h1, h2, h3⟩ := ih
      refine ⟨fun n => match n with | 0 => 0 | m + 1 => σ m + 1, ?_, ?_, ?_⟩
      · intro i hi
        rcases i with _ | m
        · show (0 : ℕ) < (a :: l₂).length
          simp
        · show σ m + 1 < (a :: l₂).length
          simp only [List.length_cons] at hi ⊢
          have hm : m < l₁.length := by omega
          have := h1 m hm
          omega
      · intro i hi j hj hij
        rcases i with _ | m <;> rcases j with _ | n
        · rfl
        · dsimp only at hij
          omega
        · dsimp only at hij
          omega
        · dsimp only at hij ⊢
          simp only [List.length_cons] at hi hj
          have hm : m < l₁.length := by omega
          have hn : n < l₁.length := by omega
          have hσ : σ m = σ n := by omega
          have := h2 m hm n hn hσ
          omega
      · intro i hi
        rcases i with _ | m
        · show (a :: l₂).getD 0 0 = (a :: l₁).getD 0 0
          rw [List.getD_cons_zero, List.getD_cons_zero]
        · show (a :: l₂).getD (σ m + 1) 0 = (a :: l₁).getD (m + 1) 0
          rw [List.getD_cons_succ, List.getD_cons_succ]
          simp only [List.length_cons] at hi
          exact h3 m (by omega)
    · -- `swap`
      intro x y l₀
      refine ⟨fun n => match n with | 0 => 1 | 1 => 0 | m + 2 => m + 2, ?_, ?_, ?_⟩
      · intro i hi
        rcases i with _ | _ | m
        · show (1 : ℕ) < (x :: y :: l₀).length
          simp
        · show (0 : ℕ) < (x :: y :: l₀).length
          simp
        · show m + 2 < (x :: y :: l₀).length
          simp only [List.length_cons] at hi ⊢
          omega
      · intro i hi j hj hij
        rcases i with _ | _ | m <;> rcases j with _ | _ | n <;>
          dsimp only at hij ⊢ <;> omega
      · intro i hi
        rcases i with _ | _ | m
        · show (x :: y :: l₀).getD 1 0 = (y :: x :: l₀).getD 0 0
          rw [List.getD_cons_succ, List.getD_cons_zero, List.getD_cons_zero]
        · show (x :: y :: l₀).getD 0 0 = (y :: x :: l₀).getD 1 0
          rw [List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
        · show (x :: y :: l₀).getD (m + 2) 0 = (y :: x :: l₀).getD (m + 2) 0
          rw [getD_cons_two, getD_cons_two]
    · -- `trans`
      intro l₁ l₂ l₃ _ _ ih1 ih2
      obtain ⟨σ, hσ⟩ := ih1
      obtain ⟨τ, hτ⟩ := ih2
      exact ⟨fun i => τ (σ i), IdxMap_comp hσ hτ⟩

  theorem Pfair_of_idxMap {l l' : List ℤ} {k : ℕ} {d : ℤ} {σ : ℕ → ℕ}
      (hm : ∀ i, i < l.length → σ i < l'.length)
      (hinj : ∀ i, i < l.length → ∀ j, j < l.length → σ i = σ j → i = j)
      (hval : ∀ i, i < l.length → l'.getD (σ i) 0 = l.getD i 0) :
      Pfair l k d → Pfair l' k d := by
    rintro ⟨S, hS, hcard, hOK⟩
    have hSl : ∀ i ∈ S, i < l.length := fun i hi => Finset.mem_range.1 (hS hi)
    refine ⟨S.image σ, ?_, ?_, ?_⟩
    · intro m hm'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm'
      exact Finset.mem_range.2 (hm i (hSl i hi))
    · rw [Finset.card_image_of_injOn]
      · exact hcard
      · intro i hi j hj hij
        simp only [Finset.mem_coe] at hi hj
        exact hinj i (hSl i hi) j (hSl j hj) hij
    · intro m hm' n hn' hmn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hn'
      have hi' := hSl i hi
      have hj' := hSl j hj
      rw [hval i hi', hval j hj']
      exact hOK i hi j hj (fun he => hmn (by rw [he]))

  theorem Pfair_perm_forward {l l' : List ℤ} (h : l.Perm l') {k : ℕ} {d : ℤ} :
      Pfair l k d → Pfair l' k d := by
    obtain ⟨σ, hσ⟩ := exists_idxMap_of_perm h
    obtain ⟨h1, h2, h3⟩ := hσ
    exact Pfair_of_idxMap h1 h2 h3

  theorem Pfair_perm {l l' : List ℤ} (h : l.Perm l') {k : ℕ} {d : ℤ} :
      Pfair l k d ↔ Pfair l' k d := by
    exact ⟨Pfair_perm_forward h, Pfair_perm_forward h.symm⟩

  theorem Pgood_mono {L : List ℤ} {k : ℕ} {d e : ℤ} (hde : e ≤ d) (h : Pgood L k d) :
      Pgood L k e := by
    obtain ⟨S, hS, hOK, hcard⟩ := h
    refine ⟨S, hS, ?_, hcard⟩
    intro i hi j hj hij
    exact le_trans hde (hOK i hi j hj hij)

  theorem absDiff_le_spread {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {i j : ℕ}
      (hi : i < L.length) (hj : j < L.length) :
      absDiff (L.getD i 0) (L.getD j 0) ≤ L.getD (L.length - 1) 0 - L.getD 0 0 := by
    have hlast : L.length - 1 < L.length := by omega
    have key : ∀ a b : ℕ, a < L.length → b < L.length → a ≤ b →
        L.getD b 0 - L.getD a 0 ≤ L.getD (L.length - 1) 0 - L.getD 0 0 := by
      intro a b ha hb hab
      have h1 : L.getD b 0 ≤ L.getD (L.length - 1) 0 := getD_mono hL (by omega) hlast
      have h2 : L.getD 0 0 ≤ L.getD a 0 := getD_mono hL (Nat.zero_le a) ha
      omega
    rcases Nat.le_total i j with h | h
    · rw [absDiff_of_le (getD_mono hL h hj)]
      exact key i j hi hj h
    · rw [absDiff_comm, absDiff_of_le (getD_mono hL h hi)]
      exact key j i hj hi h

  theorem Pgood_zero {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {k : ℕ} (hk : k ≤ L.length) :
      Pgood L k 0 := by
    obtain ⟨S, hsub, hS⟩ := Finset.exists_subset_card_eq (s := Finset.range L.length)
      (by simpa using hk)
    refine ⟨S, hsub, ?_, hS⟩
    intro i hi j hj hij
    have hi' : i < L.length := by simpa using hsub hi
    have hj' : j < L.length := by simpa using hsub hj
    have h := getD_mono hL (le_of_lt hij) hj'
    omega

  theorem not_Pgood_spread {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {k : ℕ} (hk : 2 ≤ k) :
      ¬ Pgood L k (L.getD (L.length - 1) 0 - L.getD 0 0 + 1) := by
    rintro ⟨S, hsub, hOK, hcard⟩
    have hcard2 : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard2
    have ha' : a < L.length := by simpa using hsub ha
    have hb' : b < L.length := by simpa using hsub hb
    have hlast : L.length - 1 < L.length := by omega
    have key : ∀ x y : ℕ, x < L.length → y < L.length → x < y →
        L.getD y 0 - L.getD x 0 ≤ L.getD (L.length - 1) 0 - L.getD 0 0 := by
      intro x y hx hy hxy
      have h1 : L.getD y 0 ≤ L.getD (L.length - 1) 0 := getD_mono hL (by omega) hlast
      have h2 : L.getD 0 0 ≤ L.getD x 0 := getD_mono hL (Nat.zero_le x) hx
      omega
    rcases lt_or_gt_of_ne hab with h | h
    · have h1 := hOK a ha b hb h
      have h2 := key a b ha' hb' h
      omega
    · have h1 := hOK b hb a ha h
      have h2 := key b a hb' ha' h
      omega

  theorem eq_maxTastiness {l L : List ℤ} (hL : L.Pairwise (· ≤ ·)) (hperm : L.Perm l)
      {k : ℕ} {d : ℤ} (hk : 2 ≤ k) (hkn : k ≤ l.length) (h1 : Pgood L k d)
      (h2 : ∀ e, Pgood L k e → e ≤ d) : d = maxTastiness l k := by
    have hlen : L.length = l.length := hperm.length_eq
    have hkL : k ≤ L.length := by omega
    have hd0 : 0 ≤ d := h2 0 (Pgood_zero hL hkL)
    have hmt : 0 ≤ maxTastiness l k := maxTastiness_nonneg l k
    refine le_antisymm ?_ ?_
    · have hp : Pfair L k d := (Pfair_iff_Pgood hL hd0).2 h1
      exact (le_maxTastiness_iff l hk hkn hd0).2 ((Pfair_perm hperm).1 hp)
    · have hpl : Pfair l k (maxTastiness l k) :=
        (le_maxTastiness_iff l hk hkn hmt).1 (le_refl _)
      exact h2 _ ((Pfair_iff_Pgood hL hmt).1 ((Pfair_perm hperm).2 hpl))

  /-! ### The greedy chain argument for `can_make` -/

  theorem SelOK_subset {L : List ℤ} {d : ℤ} {S S' : Finset ℕ} (h : SelOK L d S)
      (hsub : S' ⊆ S) : SelOK L d S' := by
    intro i hi j hj hij
    exact h i (hsub hi) j (hsub hj) hij

  theorem GInv_init {L : List ℤ} {d : ℤ} (h : 1 ≤ L.length) : GInv L d 1 1 0 := by
    refine ⟨le_refl 1, Nat.zero_lt_one, ⟨{0}, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      simp at hx ⊢
      omega
    · intro i hi j hj hij
      simp at hi hj
      omega
    · simp
    · simp
    · intro S hS hOK
      have hcard : S.card ≤ 1 := by
        calc S.card ≤ (Finset.range 1).card := Finset.card_le_card hS
          _ = 1 := by simp
      omega

  theorem GInv_step_pos {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {d : ℤ} {i cnt li : ℕ}
      (hinv : GInv L d i cnt li) (hi : i < L.length)
      (hstep : d ≤ L.getD i 0 - L.getD li 0) : GInv L d (i + 1) (cnt + 1) i := by
    obtain ⟨hcnt1, hlii, ⟨S, hSsub, hOK, hScard, hSsup⟩, hmax⟩ := hinv
    have hilt : li < L.length := lt_trans hlii hi
    have hni : i ∉ S := fun hmem => absurd (Finset.mem_range.1 (hSsub hmem)) (Nat.lt_irrefl i)
    have hsup : (S ∪ {i}).sup id = i := by
      rw [Finset.sup_union, hSsup, Finset.sup_singleton, id_eq]
      exact max_eq_right (le_of_lt hlii)
    refine ⟨by omega, by omega, ⟨S ∪ {i}, ?_, ?_, ?_, hsup⟩, ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hSsub hx)))
      · rw [Finset.mem_singleton] at hx
        exact Finset.mem_range.2 (by omega)
    · intro a ha b hb hab
      rcases Finset.mem_union.1 ha with ha | ha
      · rcases Finset.mem_union.1 hb with hb | hb
        · exact hOK a ha b hb hab
        · rw [Finset.mem_singleton] at hb
          rw [hb]
          have hale : a ≤ li := by
            have h1 : id a ≤ S.sup id := Finset.le_sup (f := id) ha
            rw [hSsup] at h1
            simpa using h1
          have hgle : L.getD a 0 ≤ L.getD li 0 := getD_mono hL hale hilt
          omega
      · rw [Finset.mem_singleton] at ha
        rw [ha] at hab ⊢
        rcases Finset.mem_union.1 hb with hb | hb
        · have h1 : b < i := Finset.mem_range.1 (hSsub hb)
          omega
        · rw [Finset.mem_singleton] at hb
          rw [hb] at hab
          omega
    · rw [Finset.union_singleton, Finset.card_insert_of_notMem hni, hScard]
    · intro S' hS' hOK'
      by_cases hmem : i ∈ S'
      · have hsup' : S'.sup id = i := by
          refine le_antisymm ?_ (Finset.le_sup (f := id) hmem)
          exact Finset.sup_le (fun x hx => by
            have h1 := Finset.mem_range.1 (hS' hx)
            show x ≤ i
            omega)
        have hsub : S'.erase i ⊆ Finset.range i := by
          intro x hx
          rw [Finset.mem_erase] at hx
          exact Finset.mem_range.2 (by have := Finset.mem_range.1 (hS' hx.2); omega)
        have herase := hmax (S'.erase i) hsub (SelOK_subset hOK' (Finset.erase_subset i S'))
        have hcard' : (S'.erase i).card + 1 = S'.card := Finset.card_erase_add_one hmem
        omega
      · have hsub : S' ⊆ Finset.range i := by
          intro x hx
          exact Finset.mem_range.2 (by
            have h1 := Finset.mem_range.1 (hS' hx)
            have h2 : x ≠ i := fun he => hmem (he ▸ hx)
            omega)
        have := hmax S' hsub hOK'
        omega

  theorem GInv_step_neg {L : List ℤ} (hL : L.Pairwise (· ≤ ·)) {d : ℤ} {i cnt li : ℕ}
      (hinv : GInv L d i cnt li) (hi : i < L.length)
      (hstep : ¬ d ≤ L.getD i 0 - L.getD li 0) : GInv L d (i + 1) cnt li := by
    obtain ⟨hcnt1, hlii, ⟨S, hSsub, hOK, hScard, hSsup⟩, hmax⟩ := hinv
    have hilt : li < L.length := lt_trans hlii hi
    refine ⟨hcnt1, by omega, ⟨S, ?_, hOK, hScard, hSsup⟩, ?_⟩
    · intro x hx
      exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hSsub hx)))
    · intro S' hS' hOK'
      by_cases hmem : i ∈ S'
      · have hsup' : S'.sup id = i := by
          refine le_antisymm ?_ (Finset.le_sup (f := id) hmem)
          exact Finset.sup_le (fun x hx => by
            have h1 := Finset.mem_range.1 (hS' hx)
            show x ≤ i
            omega)
        have hsub : S'.erase i ⊆ Finset.range i := by
          intro x hx
          rw [Finset.mem_erase] at hx
          exact Finset.mem_range.2 (by have := Finset.mem_range.1 (hS' hx.2); omega)
        have hOKe : SelOK L d (S'.erase i) := SelOK_subset hOK' (Finset.erase_subset i S')
        have hcard' : (S'.erase i).card + 1 = S'.card := Finset.card_erase_add_one hmem
        have hle_sup : li ≤ S'.sup id := by rw [hsup']; exact le_of_lt hlii
        rcases hmax (S'.erase i) hsub hOKe with hlt | ⟨heq, hlisup⟩
        · omega
        · have hpos : 0 < (S'.erase i).card := by omega
          obtain ⟨j, hjT, hjsup⟩ :=
            Finset.exists_mem_eq_sup (S'.erase i) (Finset.card_pos.1 hpos) (id : ℕ → ℕ)
          have hjS' : j ∈ S' := (Finset.mem_erase.1 hjT).2
          have hji : j < i := Finset.mem_range.1 (hsub hjT)
          rw [hjsup] at hlisup
          have hli_j : li ≤ j := by simpa using hlisup
          have hgj : L.getD li 0 ≤ L.getD j 0 := getD_mono hL hli_j (lt_trans hji hi)
          have hdij : d ≤ L.getD i 0 - L.getD j 0 := hOK' j hjS' i hmem hji
          omega
      · have hsub : S' ⊆ Finset.range i := by
          intro x hx
          exact Finset.mem_range.2 (by
            have h1 := Finset.mem_range.1 (hS' hx)
            have h2 : x ≠ i := fun he => hmem (he ▸ hx)
            omega)
        exact hmax S' hsub hOK'

  theorem GInv_final {L : List ℤ} {d : ℤ} {cnt li k : ℕ} (hinv : GInv L d L.length cnt li) :
      k ≤ cnt ↔ Pgood L k d := by
    obtain ⟨hcnt1, hlii, ⟨S, hSsub, hOK, hScard, hSsup⟩, hmax⟩ := hinv
    constructor
    · intro hk
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := k) (by omega)
      exact ⟨T, hTsub.trans hSsub, SelOK_subset hOK hTsub, hTcard⟩
    · rintro ⟨T, hTsub, hOKT, hTcard⟩
      have := hmax T hTsub hOKT
      omega

  /-! ### Correctness of the insertion sort used by the extracted code -/

  /-- One step of `AegisShim.sortInsert` on a nonempty list, with the comparison
  `core.cmp.OrdI64.cmp` unfolded to `compare` of the integer values. -/
  theorem sortInsert_cons (x y : Std.I64) (ys : List Std.I64) :
      AegisShim.sortInsert core.cmp.OrdI64.cmp x (y :: ys) =
        (if compare x.val y.val == Ordering.gt then
          (do let r ← AegisShim.sortInsert core.cmp.OrdI64.cmp x ys
              ok (y :: r))
        else ok (x :: y :: ys)) := by
    simp [AegisShim.sortInsert, core.cmp.impls.OrdI64.cmp]

  /-- One step of `AegisShim.sortList` on a nonempty list. -/
  theorem sortList_cons (x : Std.I64) (xs : List Std.I64) :
      AegisShim.sortList core.cmp.OrdI64.cmp (x :: xs) =
        (do let r ← AegisShim.sortList core.cmp.OrdI64.cmp xs
            AegisShim.sortInsert core.cmp.OrdI64.cmp x r) := by
    simp [AegisShim.sortList]

  /-- `AegisShim.sortInsert` is correct: inserting `x` into a sorted list yields a
  sorted rearrangement of the list with `x` added. -/
  theorem sortInsert_spec (x : Std.I64) (ys : List Std.I64)
      (hys : (ys.map (fun y => y.val)).Pairwise (· ≤ ·)) :
      ∃ r : List Std.I64, AegisShim.sortInsert core.cmp.OrdI64.cmp x ys = ok r ∧
        (r.map (fun y => y.val)).Perm (x.val :: ys.map (fun y => y.val)) ∧
        (r.map (fun y => y.val)).Pairwise (· ≤ ·) := by
    induction ys with
    | nil =>
      exact ⟨[x], by simp [AegisShim.sortInsert], List.Perm.refl _,
        List.pairwise_singleton _ _⟩
    | cons y ys ih =>
      have hcons : (y.val :: ys.map (fun z => z.val)).Pairwise (· ≤ ·) := by
        simpa using hys
      obtain ⟨hyl, hys'⟩ := List.pairwise_cons.mp hcons
      by_cases hlt : y.val < x.val
      · have hcond : (compare x.val y.val == Ordering.gt) = true := by
          rw [beq_iff_eq, compare_gt_iff_gt]; exact hlt
        obtain ⟨r', hr', hperm, hsorted⟩ := ih hys'
        refine ⟨y :: r', ?_, ?_, ?_⟩
        · rw [sortInsert_cons, ite_eq_left hcond, hr']; simp
        · exact (hperm.cons y.val).trans (List.Perm.swap x.val y.val _)
        · refine List.pairwise_cons.mpr ⟨?_, hsorted⟩
          intro a ha
          rcases List.mem_cons.mp (hperm.mem_iff.mp ha) with rfl | h
          · exact le_of_lt hlt
          · exact hyl a h
      · have hcond : ¬ (compare x.val y.val == Ordering.gt) = true := by
          rw [beq_iff_eq, compare_gt_iff_gt]; exact hlt
        refine ⟨x :: y :: ys, ?_, ?_, ?_⟩
        · rw [sortInsert_cons, ite_eq_right hcond]
        · exact List.Perm.refl _
        · refine List.pairwise_cons.mpr ⟨?_, by simpa using hys⟩
          intro a ha
          have hle : x.val ≤ y.val := not_lt.mp hlt
          rcases List.mem_cons.mp ha with rfl | h
          · exact hle
          · exact le_trans hle (hyl a h)

  theorem sortList_spec (l : List Std.I64) :
      ∃ l' : List Std.I64, AegisShim.sortList core.cmp.OrdI64.cmp l = ok l' ∧
        (l'.map (fun x => x.val)).Perm (l.map (fun x => x.val)) ∧
        (l'.map (fun x => x.val)).Pairwise (· ≤ ·) := by
    induction l with
    | nil => exact ⟨[], by simp [AegisShim.sortList], List.Perm.refl _, by simp⟩
    | cons x xs ih =>
      obtain ⟨r', hr', hperm, hsorted⟩ := ih
      obtain ⟨r, hr, hperm2, hsorted2⟩ := sortInsert_spec x r' hsorted
      refine ⟨r, ?_, ?_, ?_⟩
      · rw [sortList_cons, hr']
        simpa using hr
      · exact hperm2.trans (hperm.cons x.val)
      · exact hsorted2

  open Aegis.MaximumTastiness in
  /-- The first loop copies the values of the price array into a vector. -/
  theorem loop0_spec (price : Slice Std.I64) (hnl : price.length ≤ 100000) :
      ∃ v : alloc.vec.Vec Std.I64,
        maximum_tastiness_loop0 price (Slice.len price)
          (alloc.vec.Vec.new Std.I64) 0#usize = ok v ∧ v.val = price.val := by
    have aux : ∀ (n : Std.Usize) (v : alloc.vec.Vec Std.I64) (i : Std.Usize),
        n.val = price.length → i.val ≤ n.val → v.val = price.val.take i.val →
        WP.spec (maximum_tastiness_loop0 price n v i)
          (fun (w : alloc.vec.Vec Std.I64) => w.val = price.val) := by
      intro n v i hn hi hv
      unfold maximum_tastiness_loop0
      apply Aeneas.Std.loop.spec_decr_nat
        (measure := fun p : alloc.vec.Vec Std.I64 × Std.Usize => n.val - p.2.val)
        (inv := fun p : alloc.vec.Vec Std.I64 × Std.Usize =>
          p.2.val ≤ n.val ∧ p.1.val = price.val.take p.2.val)
        (post := fun (w : alloc.vec.Vec Std.I64) => w.val = price.val) _ _
      · rintro ⟨v', i'⟩ ⟨hi', hv'⟩
        simp only [Prod.fst, Prod.snd] at hi' hv' ⊢
        unfold maximum_tastiness_loop0.body
        by_cases hlt : i' < n
        · rw [if_pos hlt]
          have hlt' : i'.val < n.val := hlt
          have hib : i'.val < price.length := by rw [← hn]; exact hlt'
          apply WP.spec_bind (Slice.index_usize_spec price i' hib)
          intro x hx
          have hlen : v'.val.length < Usize.max := by
            rw [hv']
            have h2 : (price.val.take i'.val).length ≤ price.length := by
              rw [List.length_take]; omega
            scalar_tac
          apply WP.spec_bind (alloc.vec.Vec.push_spec v' x hlen)
          intro v'' hv''
          apply WP.spec_bind (Usize.add_spec (x := i') (y := 1#usize) (by scalar_tac))
          intro i'' hi''
          have hiv : i''.val = i'.val + 1 := by rw [hi'']; simp
          simp only [WP.spec_ok, hiv, hv'', hx, hv']
          exact ⟨⟨by omega, List.take_append_getElem hib⟩, by omega⟩
        · rw [if_neg hlt]
          simp only [WP.spec_ok]
          have hlt'' : ¬ (i'.val < n.val) := hlt
          have h1 : i'.val = n.val := by omega
          rw [hv', h1, hn, List.take_length]
      · exact ⟨hi, hv⟩
    obtain ⟨r, hr, hp⟩ := spec_ok_exists (p := fun (w : alloc.vec.Vec Std.I64) =>
      w.val = price.val)
      (aux (Slice.len price) (alloc.vec.Vec.new Std.I64) 0#usize rfl (by simp) (by simp))
    exact ⟨r, hr, hp⟩

  open Aegis.MaximumTastiness in
  /-- The greedy loop of `can_make` computes the maximal number of positions that can
  be taken with consecutive distances at least `d`. -/
  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count : Std.I64) (last : Std.I64) (i : Std.Usize) (L : List ℤ)
      (hL : L = sorted.val.map (fun x => x.val))
      (hLs : L.Pairwise (· ≤ ·))
      (hval : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 1000000000)
      (hi : i.val ≤ L.length) (hn : n.val = L.length)
      (hlen : L.length ≤ 100000)
      (hinv : ∃ (cnt li : ℕ), count.val = (cnt : ℤ) ∧ GInv L d.val i.val cnt li ∧
        last.val = L.getD li 0) :
      ∃ b, can_make_loop sorted k d n count last i = ok b ∧
        (b = true ↔ Pgood L k.val.toNat d.val) := by
    have hLgetD : ∀ j, L.getD j 0 = (sorted.val.getD j 0#i64).val := by
      intro j
      rw [hL]
      cases h : sorted.val[j]? with
      | none => simp [h]
      | some v => simp [h]
    have aux_pgood : ∀ (i cnt li k : ℕ), i ≤ L.length → GInv L d.val i cnt li → k ≤ cnt →
        Pgood L k d.val := by
      intro i cnt li k hile hinv hk
      obtain ⟨-, -, ⟨S, hSsub, hSOK, hScard, -⟩, -⟩ := hinv
      have hsub : S ⊆ Finset.range L.length := fun x hx =>
        Finset.mem_range.2 (by have := Finset.mem_range.1 (hSsub hx); omega)
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := k) (by omega)
      exact ⟨T, hTsub.trans hsub, SelOK_subset hSOK hTsub, hTcard⟩
    have key : ∀ (count last : Std.I64) (i : Std.Usize), i.val ≤ L.length →
        (∃ (cnt li : ℕ), count.val = (cnt : ℤ) ∧ GInv L d.val i.val cnt li ∧
          last.val = L.getD li 0) →
        WP.spec (can_make_loop sorted k d n count last i)
          (fun b => b = true ↔ Pgood L k.val.toNat d.val) := by
      intro count last i hi0 hinv0
      unfold can_make_loop
      apply Aeneas.Std.loop.spec_decr_nat (α := Std.I64 × Std.I64 × Std.Usize) (β := Bool)
        (measure := fun p : Std.I64 × Std.I64 × Std.Usize => n.val - p.2.2.val)
        (inv := fun p : Std.I64 × Std.I64 × Std.Usize =>
          p.2.2.val ≤ n.val ∧ ∃ (cnt li : ℕ), p.1.val = (cnt : ℤ) ∧
            GInv L d.val p.2.2.val cnt li ∧ p.2.1.val = L.getD li 0)
        (post := fun b => b = true ↔ Pgood L k.val.toNat d.val) _ _
      · rintro ⟨count', last', i'⟩ ⟨hile, cnt, li, hcount, hginv, hlast⟩
        simp only [Prod.fst, Prod.snd] at hile hcount hginv hlast ⊢
        unfold can_make_loop.body
        have hcntle : cnt ≤ i'.val := by
          obtain ⟨-, -, ⟨S, hSsub, hSOK, hScard, -⟩, -⟩ := hginv
          have h1 : S.card ≤ (Finset.range i'.val).card := Finset.card_le_card hSsub
          rw [hScard, Finset.card_range] at h1
          exact h1
        by_cases hlt : i' < n
        · rw [if_pos hlt]
          have hlt' : i'.val < n.val := hlt
          have hib2 : i'.val < L.length := by omega
          have hib : i'.val < sorted.length := by
            have hlen : L.length = sorted.length := by rw [hL]; simp
            omega
          have hli : li < L.length := by
            have := hginv.2.1
            omega
          apply WP.spec_bind (Slice.index_usize_spec sorted i' hib)
          intro x hx
          have hxL : x.val = L.getD i'.val 0 := by
            rw [hx, hLgetD, List.getD_eq_getElem sorted.val 0#i64 hib]
          have hxb : 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
            rw [hxL, getD_of_lt hib2]; exact hval _ (List.getElem_mem hib2)
          have hlastb : 1 ≤ last'.val ∧ last'.val ≤ 1000000000 := by
            rw [hlast, getD_of_lt hli]; exact hval _ (List.getElem_mem hli)
          apply WP.spec_bind
            (Std.I64.sub_spec (x := x) (y := last') (by scalar_tac) (by scalar_tac))
          intro i2 hi2
          by_cases hge : i2 ≥ d
          · rw [if_pos hge]
            have hge' : d.val ≤ i2.val := hge
            have hstep : d.val ≤ L.getD i'.val 0 - L.getD li 0 := by
              rw [hi2, hxL, hlast] at hge'
              exact hge'
            apply WP.spec_bind
              (Std.I64.add_spec (x := count') (y := 1#i64) (by
                rw [hcount]
                have h100 : cnt + 1 ≤ 100001 := by omega
                scalar_tac) (by scalar_tac))
            intro count1 hc1
            by_cases hk : count1 ≥ k
            · rw [if_pos hk]
              simp only [WP.spec_ok]
              have hk1 : k.val ≤ count1.val := hk
              have hk' : k.val.toNat ≤ cnt + 1 := by
                have h2 : count1.val = (cnt : ℤ) + 1 := by rw [hc1, hcount]; simp
                have h3 : k.val ≤ (cnt : ℤ) + 1 := by omega
                have h4 := Int.toNat_le.mpr h3
                omega
              exact ⟨fun _ => aux_pgood (i'.val + 1) (cnt + 1) i' k.val.toNat (by omega)
                (GInv_step_pos hLs hginv hib2 hstep) hk', fun _ => trivial⟩
            · rw [if_neg hk]
              apply WP.spec_bind (Usize.add_spec (x := i') (y := 1#usize) (by scalar_tac))
              intro i3 hi3
              have hi3v : i3.val = i'.val + 1 := by rw [hi3]; simp
              simp only [WP.spec_ok]
              refine ⟨⟨by omega, cnt + 1, i', ?_, ?_, hxL⟩, by omega⟩
              · rw [hc1, hcount]
                simp
              · rw [hi3v]
                exact GInv_step_pos hLs hginv hib2 hstep
          · rw [if_neg hge]
            have hstep : ¬ (d.val ≤ L.getD i'.val 0 - L.getD li 0) := by
              intro h
              apply hge
              have h2 : d.val ≤ i2.val := by
                rw [hi2, hxL, hlast]
                exact h
              exact h2
            apply WP.spec_bind (Usize.add_spec (x := i') (y := 1#usize) (by scalar_tac))
            intro i3 hi3
            have hi3v : i3.val = i'.val + 1 := by rw [hi3]; simp
            simp only [WP.spec_ok]
            refine ⟨⟨by omega, cnt, li, hcount, ?_, hlast⟩, by omega⟩
            rw [hi3v]
            exact GInv_step_neg hLs hginv hib2 hstep
        · rw [if_neg hlt]
          simp only [WP.spec_ok, decide_eq_true_eq]
          have hieq : i'.val = L.length := by
            have h : ¬ (i'.val < n.val) := hlt
            omega
          have hG : GInv L d.val L.length cnt li := hieq ▸ hginv
          have hkey : (count' ≥ k) ↔ k.val.toNat ≤ cnt := by
            have h1 : (count' ≥ k) ↔ k.val ≤ count'.val := Iff.rfl
            rw [h1, hcount]
            exact Int.toNat_le.symm
          exact hkey.trans (GInv_final hG)
      · refine ⟨?_, ?_⟩
        · simp only [Prod.fst, Prod.snd]
          rw [hn]
          exact hi0
        · simpa only [Prod.fst, Prod.snd] using hinv0
    obtain ⟨b, hb, hbp⟩ := spec_ok_exists (key count last i hi hinv)
    exact ⟨b, hb, hbp⟩

  open Aegis.MaximumTastiness in
  /-- `can_make` decides the threshold predicate. -/
  theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64) (L : List ℤ)
      (hL : L = sorted.val.map (fun x => x.val))
      (hLs : L.Pairwise (· ≤ ·))
      (hval : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 1000000000)
      (hk : 2 ≤ k.val) (hkn : k.val.toNat ≤ L.length) (hlen : L.length ≤ 100000)
      (hd : 0 ≤ d.val) :
      ∃ b, can_make sorted k d = ok b ∧ (b = true ↔ Pgood L k.val.toNat d.val) := by
    have hspec : WP.spec (can_make sorted k d)
        (fun b => b = true ↔ Pgood L k.val.toNat d.val) := by
      unfold can_make
      have hk1 : ¬ (k ≤ 1#i64) := by
        intro h
        have h1 : (1#i64).val = 1 := by simp
        have h2 : k.val ≤ (1#i64).val := h
        omega
      rw [if_neg hk1]
      have hLlen : L.length = sorted.length := by rw [hL]; simp
      have h0 : 0 < sorted.length := by omega
      apply WP.spec_bind (Slice.index_usize_spec sorted 0#usize h0)
      intro last hlast
      have hLget0 : L.getD 0 0 = (sorted.val.getD 0 0#i64).val := by
        rw [hL]
        cases h : sorted.val[0]? with
        | none => simp [h]
        | some v => simp [h]
      have hlastD : last.val = L.getD 0 0 := by
        rw [hlast, hLget0, List.getD_eq_getElem sorted.val 0#i64 h0]
        simp
      have hone : (1#usize).val = 1 := by simp
      have hi1 : (1#usize).val ≤ L.length := by omega
      obtain ⟨b, hb, hbp⟩ := can_make_loop_spec sorted k d (Slice.len sorted) 1#i64 last 1#usize L
        hL hLs hval hi1 (by rw [Slice.len_val]; omega) hlen
        ⟨1, 0, by simp, GInv_init (by omega), hlastD⟩
      rw [hb]
      simpa using hbp
    obtain ⟨b, hb, hbp⟩ := spec_ok_exists hspec
    exact ⟨b, hb, hbp⟩

  open Aegis.MaximumTastiness in
  /-- The binary search returns the largest admissible threshold. -/
  theorem loop1_spec (k : Std.I64) (sorted : alloc.vec.Vec Std.I64) (lo hi : Std.I64)
      (L : List ℤ)
      (hL : L = sorted.val.map (fun x => x.val))
      (hLs : L.Pairwise (· ≤ ·))
      (hval : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 1000000000)
      (hk : 2 ≤ k.val) (hkn : k.val.toNat ≤ L.length)
      (hlen : L.length ≤ 100000)
      (hlo0 : 0 ≤ lo.val)
      (hhi : hi.val ≤ L.getD (L.length - 1) 0 - L.getD 0 0 + 1)
      (hlt : lo.val < hi.val)
      (hp : Pgood L k.val.toNat lo.val)
      (hnp : ¬ Pgood L k.val.toNat hi.val) :
      ∃ r, maximum_tastiness_loop1 k sorted lo hi = ok r ∧ Pgood L k.val.toNat r.val ∧
        ¬ Pgood L k.val.toNat (r.val + 1) := by
    have hget0 : 1 ≤ L.getD 0 0 := by
      have h0 : 0 < L.length := by
        have h1 : 2 ≤ k.val.toNat := by omega
        omega
      rw [getD_of_lt (L := L) h0]
      exact (hval _ (List.getElem_mem h0)).1
    have hgetlast : L.getD (L.length - 1) 0 ≤ 1000000000 := by
      have h1 : L.length - 1 < L.length := by
        have h2 : 2 ≤ k.val.toNat := by omega
        omega
      rw [getD_of_lt (L := L) h1]
      exact (hval _ (List.getElem_mem h1)).2
    have hspread : L.getD (L.length - 1) 0 - L.getD 0 0 + 1 ≤ 1000000000 := by omega
    have key : ∀ (lo hi : Std.I64), 0 ≤ lo.val →
        hi.val ≤ L.getD (L.length - 1) 0 - L.getD 0 0 + 1 → lo.val < hi.val →
        Pgood L k.val.toNat lo.val → ¬ Pgood L k.val.toNat hi.val →
        WP.spec (maximum_tastiness_loop1 k sorted lo hi)
          (fun r => Pgood L k.val.toNat r.val ∧ ¬ Pgood L k.val.toNat (r.val + 1)) := by
      intro lo hi hlo0 hhi hlt hp hnp
      unfold maximum_tastiness_loop1
      apply Aeneas.Std.loop.spec_decr_nat (α := Std.I64 × Std.I64) (β := Std.I64)
        (measure := fun p : Std.I64 × Std.I64 => (p.2.val - p.1.val).toNat)
        (inv := fun p : Std.I64 × Std.I64 =>
          0 ≤ p.1.val ∧ p.1.val < p.2.val ∧
            p.2.val ≤ L.getD (L.length - 1) 0 - L.getD 0 0 + 1 ∧
            Pgood L k.val.toNat p.1.val ∧ ¬ Pgood L k.val.toNat p.2.val)
        (post := fun r => Pgood L k.val.toNat r.val ∧ ¬ Pgood L k.val.toNat (r.val + 1)) _ _
      · rintro ⟨lo', hi'⟩ ⟨hlo0', hlt', hhi', hp', hnp'⟩
        simp only [Prod.fst, Prod.snd] at hlo0' hlt' hhi' hp' hnp' ⊢
        have hhi'' : hi'.val ≤ 1000000000 := le_trans hhi' hspread
        unfold maximum_tastiness_loop1.body
        apply WP.spec_bind
          (Std.I64.add_spec (x := lo') (y := 1#i64) (by scalar_tac) (by scalar_tac))
        intro i hi_def
        have hi_val : i.val = lo'.val + 1 := hi_def
        by_cases hlt2 : i < hi'
        · have hlt2' : i.val < hi'.val := hlt2
          rw [if_pos hlt2]
          apply WP.spec_bind
            (Std.I64.sub_spec (x := hi') (y := lo') (by scalar_tac) (by scalar_tac))
          intro i1 hi1_def
          have hi1_val : i1.val = hi'.val - lo'.val := hi1_def
          apply WP.spec_bind
            (Std.I64.div_spec (x := i1) (y := 2#i64) (by decide) (by scalar_tac))
          intro i2 hi2_def
          have hi2_val : i2.val = i1.val / 2 := by
            rw [hi2_def, Int.tdiv_eq_ediv]
            have h0 : (0:ℤ) ≤ i1.val := by omega
            simp [h0]
          have hmid_nn : 0 ≤ lo'.val + i2.val := by omega
          have hmid_ub : lo'.val + i2.val ≤ 1000000000 := by omega
          apply WP.spec_bind
            (Std.I64.add_spec (x := lo') (y := i2) (by scalar_tac) (by scalar_tac))
          intro mid hmid_def
          have hmid_val : mid.val = lo'.val + i2.val := hmid_def
          have hmid_nonneg : 0 ≤ mid.val := by omega
          have hmid_lt : mid.val < hi'.val := by omega
          have hmid_gt : lo'.val < mid.val := by omega
          have hcan : WP.spec (can_make (alloc.vec.Vec.deref sorted) k mid)
              (fun b => b = true ↔ Pgood L k.val.toNat mid.val) := by
            obtain ⟨b, hb, hbs⟩ := can_make_spec (sorted := alloc.vec.Vec.deref sorted)
              (k := k) (d := mid) (L := L) (by rw [hL]; simp [alloc.vec.Vec.deref])
              hLs hval hk hkn hlen hmid_nonneg
            rw [hb]
            simpa using hbs
          apply WP.spec_bind hcan
          intro b hb
          by_cases hbtrue : b = true
          · rw [if_pos hbtrue]
            simp only [WP.spec_ok]
            exact ⟨⟨hmid_nonneg, hmid_lt, hhi', hb.mp hbtrue, hnp'⟩, by omega⟩
          · rw [if_neg hbtrue]
            simp only [WP.spec_ok]
            exact ⟨⟨hlo0', hmid_gt, le_trans (le_of_lt hmid_lt) hhi', hp',
              fun h => hbtrue (hb.mpr h)⟩, by omega⟩
        · have hlt2' : ¬ (i.val < hi'.val) := hlt2
          rw [if_neg hlt2]
          have hhi_eq : hi'.val = lo'.val + 1 := by omega
          simp only [WP.spec_ok]
          exact ⟨hp', by rw [← hhi_eq]; exact hnp'⟩
      · exact ⟨hlo0, hlt, hhi, hp, hnp⟩
    obtain ⟨r, hr, hpost⟩ := spec_ok_exists (key lo hi hlo0 hhi hlt hp hnp)
    exact ⟨r, hr, hpost⟩

  open Aegis.MaximumTastiness in
  /-- Main correctness statement for the extracted function. -/
  theorem main_aux (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxTastiness (vals price) k.val.toNat := by
    have hzero : (0#usize).val = 0 := rfl
    have hnev : (Slice.len price).val ≠ 0 := by rw [Slice.len_val]; omega
    have hne : ¬ (Slice.len price = 0#usize) := by
      rw [UScalar.neq_to_neq_val, hzero]
      exact hnev
    have hloop0 : WP.spec (maximum_tastiness_loop0 price price.len
        (alloc.vec.Vec.new Std.I64) 0#usize) (fun v => v.val = price.val) := by
      obtain ⟨v, hv, hveq⟩ := loop0_spec price h_len
      rw [hv]
      simpa using hveq
    have hderef : ∀ (v : alloc.vec.Vec Std.I64),
        WP.spec (lift (alloc.vec.Vec.deref_mut v))
          (fun p : Slice Std.I64 × (Slice Std.I64 → alloc.vec.Vec Std.I64) =>
            (∀ s' : Slice Std.I64, (p.2 s').val = s'.val) ∧ p.1.val = v.val) := by
      intro v
      unfold lift alloc.vec.Vec.deref_mut
      simp only [WP.spec_ok]
      exact ⟨fun s' => rfl, rfl⟩
    have hsort : ∀ (s : Slice Std.I64), alloc.slice.Slice.sort core.cmp.OrdI64 s ⦃ s1 =>
        (s1.val.map (fun x => x.val)).Perm (s.val.map (fun x => x.val)) ∧
        (s1.val.map (fun x => x.val)).Pairwise (· ≤ ·) ⦄ := by
      intro s
      obtain ⟨l', hl', hperm', hsorted'⟩ := sortList_spec s.val
      have hlen : l'.length ≤ Usize.max := by
        have h := List.Perm.length_eq hperm'
        simp only [List.length_map] at h
        rw [h]
        exact Slice.property s
      unfold alloc.slice.Slice.sort
      rw [hl']
      simp only [Aeneas.Std.bind_ok, dif_pos hlen, WP.spec_ok]
      refine ⟨?_, ?_⟩
      · rw [Slice.from_val]
        exact hperm'
      · rw [Slice.from_val]
        exact hsorted'
    have hspec : WP.spec (maximum_tastiness price k)
        (fun r => r.val = maxTastiness (vals price) k.val.toNat) := by
      unfold maximum_tastiness
      dsimp only
      rw [if_neg hne]
      step with hloop0 as ⟨ v, hv ⟩
      step with hderef as ⟨ s, back, hback, hs ⟩
      step with hsort as ⟨ s1, hperm, hsorted ⟩
      have hLs_perm : (s1.val.map (fun x => x.val)).Perm
          (price.val.map (fun x => x.val)) := by
        simpa only [hs, hv] using hperm
      have hLlen : (s1.val.map (fun x => x.val)).length = price.length := by
        have hp := List.Perm.length_eq hLs_perm
        simpa only [List.length_map] using hp
      have hLs_val : ∀ x ∈ s1.val.map (fun x => x.val), 1 ≤ x ∧ x ≤ 1000000000 := by
        intro x hx
        have hx' : x ∈ price.val.map (fun y => y.val) := hLs_perm.subset hx
        rcases List.mem_map.1 hx' with ⟨y, hy, rfl⟩
        exact h_price y hy
      step as ⟨ i, hieq ⟩ by scalar_tac
      rw [Slice.len_val] at hieq
      have hidx : i.val < (s1.val.map (fun x => x.val)).length := by
        rw [hLlen]
        omega
      step as ⟨ i1, hi1eq ⟩ by scalar_tac
      have hi1' : i1.val = (s1.val.map (fun x => x.val))[i.val] := by
        simp only [hi1eq, hback s1, List.getElem_map]
      have hi1_b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [hi1']
        exact hLs_val _ (List.getElem_mem hidx)
      step as ⟨ i2, hi2eq ⟩ by scalar_tac
      have h0idx : 0 < (s1.val.map (fun x => x.val)).length := by
        rw [hLlen]
        omega
      have hi2' : i2.val = (s1.val.map (fun x => x.val))[0] := by
        simp only [hi2eq, hback s1, List.getElem_map]
      have hi2_b : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        rw [hi2']
        exact hLs_val _ (List.getElem_mem h0idx)
      step as ⟨ max_diff, hdiffeq ⟩ by scalar_tac
      step as ⟨ hi, hhieq ⟩ by scalar_tac
      have hLlast_idx : (s1.val.map (fun x => x.val)).length - 1 = i.val := by
        rw [hLlen]
        omega
      have hlast : (s1.val.map (fun x => x.val)).getD
          ((s1.val.map (fun x => x.val)).length - 1) 0 = i1.val := by
        rw [hLlast_idx, getD_of_lt hidx, hi1']
      have hfirst : (s1.val.map (fun x => x.val)).getD 0 0 = i2.val := by
        rw [getD_of_lt h0idx, hi2']
      have hhi_eq : hi.val = (s1.val.map (fun x => x.val)).getD
            ((s1.val.map (fun x => x.val)).length - 1) 0
          - (s1.val.map (fun x => x.val)).getD 0 0 + 1 := by
        rw [hhieq, hdiffeq, hlast, hfirst]
      have hzero64 : (0#i64).val = 0 := rfl
      have hmono : (s1.val.map (fun x => x.val)).getD 0 0 ≤
          (s1.val.map (fun x => x.val)).getD
            ((s1.val.map (fun x => x.val)).length - 1) 0 :=
        getD_mono hsorted (by omega) (by omega)
      have hlt : (0#i64).val < hi.val := by
        rw [hhi_eq, hzero64]
        omega
      have hktwo : 2 ≤ k.val.toNat := (Int.le_toNat (z := k.val) (by omega)).mpr h_k_lo
      have hkn : k.val.toNat ≤ (s1.val.map (fun x => x.val)).length := by
        rw [hLlen]
        exact Int.toNat_le.mpr h_k_hi
      have hkn' : k.val.toNat ≤ (vals price).length := by
        simpa only [vals, List.length_map, hLlen] using hkn
      have hp : Pgood (s1.val.map (fun x => x.val)) k.val.toNat (0#i64).val := by
        rw [hzero64]
        exact Pgood_zero hsorted hkn
      have hnp : ¬ Pgood (s1.val.map (fun x => x.val)) k.val.toNat hi.val := by
        rw [hhi_eq]
        exact not_Pgood_spread hsorted hktwo
      obtain ⟨r, hr, hgood, hnot⟩ :=
        loop1_spec k (back s1) 0#i64 hi (s1.val.map (fun x => x.val))
          (by rw [hback s1]) hsorted hLs_val h_k_lo hkn (by rw [hLlen]; exact h_len)
          (by rw [hzero64]) (le_of_eq hhi_eq) hlt hp hnp
      rw [hr]
      simp only [WP.spec_ok]
      refine eq_maxTastiness hsorted hLs_perm hktwo hkn' hgood ?_
      intro e he
      by_contra hcon
      push_neg at hcon
      exact hnot (Pgood_mono (by omega) he)
    obtain ⟨r, hr, hp⟩ := spec_ok_exists hspec
    exact ⟨r, hr, hp⟩

  /-! ## Specifications -/

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    trivial

  /-- **S1 (main, functional).**  Under the stated preconditions the function returns a
  result `r` equal to the largest tastiness of a `k`-element set of positions, where the
  tastiness of a selection is the minimum pairwise distance of its prices. -/
  theorem spec_1 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxTastiness (vals price) k.val.toNat := by
    exact main_aux price k h_n h_k_lo h_k_hi h_len h_price

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
