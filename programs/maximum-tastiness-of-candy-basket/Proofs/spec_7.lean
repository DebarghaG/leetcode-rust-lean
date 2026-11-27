import Aegis.MaximumTastiness.Code.Funs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation
import Mathlib.Data.Multiset.Bind

/-
Proof of `AegisSpec.MaximumTastiness.spec_7` (maximum-tastiness-of-candy-basket).
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

  /-! ## Notions used in the proof of `spec_S7` -/

  open List

  /-- `absDiff` expressed with `Int`'s absolute value. -/
  theorem absDiff_eq_abs (a b : ℤ) : absDiff a b = |a - b| := by
    unfold absDiff
    rw [Int.abs_eq_natAbs]

  @[simp]
  theorem absDiff_self (a : ℤ) : absDiff a a = 0 := by
    simp [absDiff]

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    rw [absDiff_eq_abs, absDiff_eq_abs, abs_sub_comm]

  theorem absDiff_nonneg (a b : ℤ) : 0 ≤ absDiff a b := by
    rw [absDiff_eq_abs]
    exact abs_nonneg _

  theorem absDiff_of_le {a b : ℤ} (h : a ≤ b) : absDiff a b = b - a := by
    rw [absDiff_eq_abs, abs_of_nonpos (by lia)]
    ring

  /-- The selection condition of `spec_S7`, phrased with sets of index positions. -/
  def selExists (l : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    ∃ S : Finset ℕ, S ⊆ Finset.range l.length ∧ S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d ≤ absDiff (l.getD i 0) (l.getD j 0)

  /-- The same condition, phrased with sublists of values. -/
  def subExists (l : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    ∃ l' : List ℤ, l'.length = k ∧ l' <+ l ∧ l'.Pairwise (fun x y => d ≤ absDiff x y)

  /-- `greedyCount s d last` is the number of further elements the greedy strategy of
  `can_make` selects from `s`, when the previously selected element is `last`. -/
  def greedyCount : List ℤ → ℤ → ℤ → ℕ
    | [], _, _ => 0
    | x :: xs, d, last =>
      if d ≤ x - last then 1 + greedyCount xs d x else greedyCount xs d last

  /-- The elements selected by the greedy strategy, in order. -/
  def greedyPicks : List ℤ → ℤ → ℤ → List ℤ
    | [], _, _ => []
    | x :: xs, d, last =>
      if d ≤ x - last then x :: greedyPicks xs d x else greedyPicks xs d last

  theorem greedyPicks_length (s : List ℤ) (d last : ℤ) :
      (greedyPicks s d last).length = greedyCount s d last := by
    induction s generalizing last with
    | nil => simp [greedyPicks, greedyCount]
    | cons x xs ih =>
      rw [greedyPicks, greedyCount]
      split
      · simp [*]
        omega
      · exact ih last

  theorem greedyPicks_sublist (s : List ℤ) (d last : ℤ) :
      greedyPicks s d last <+ s := by
    induction s generalizing last with
    | nil => simp [greedyPicks]
    | cons x xs ih =>
      rw [greedyPicks]
      split
      · exact List.Sublist.cons_cons _ (ih x)
      · exact (ih last).trans (List.Sublist.cons _ (List.Sublist.refl _))

  /-! ### Submultisets and sublists -/

  /-- Every submultiset of the entries of a list is the multiset of entries of a
  sublist. -/
  theorem prvB_sublist_of_le_multiset :
      ∀ (m : List ℤ) (t : Multiset ℤ), t ≤ (↑m : Multiset ℤ) →
        ∃ m' : List ℤ, m' <+ m ∧ (↑m' : Multiset ℤ) = t := by
    intro m
    induction m with
    | nil =>
      intro t h
      have h0 : t = 0 := Multiset.le_zero.mp h
      exact ⟨[], by simp, by simp [h0]⟩
    | cons x xs ih =>
      intro t h
      have h' : t ≤ x ::ₘ (xs : Multiset ℤ) := h
      by_cases hx : x ∈ t
      · have hcon : x ::ₘ t.erase x = t := Multiset.cons_erase hx
        have hle : t.erase x ≤ (xs : Multiset ℤ) := by
          rw [Multiset.le_iff_count]
          intro a
          have h1 : Multiset.count a t ≤ Multiset.count a (x ::ₘ (xs : Multiset ℤ)) :=
            (Multiset.le_iff_count.mp h') a
          by_cases ha : a = x
          · subst ha
            rw [Multiset.count_erase_self, Multiset.count_cons_self] at *
            omega
          · rw [Multiset.count_erase_of_ne ha, Multiset.count_cons_of_ne ha] at *
            exact h1
        obtain ⟨m', hsub, hcoe⟩ := ih (t.erase x) hle
        refine ⟨x :: m', List.Sublist.cons_cons x hsub, ?_⟩
        show x ::ₘ (↑m' : Multiset ℤ) = t
        rw [hcoe, hcon]
      · have hcnt : Multiset.count x t = 0 := by
          rw [Multiset.count_eq_zero]; exact hx
        have hle : t ≤ (xs : Multiset ℤ) := by
          rw [Multiset.le_iff_count]
          intro a
          have h1 : Multiset.count a t ≤ Multiset.count a (x ::ₘ (xs : Multiset ℤ)) :=
            (Multiset.le_iff_count.mp h') a
          by_cases ha : a = x
          · subst ha
            rw [hcnt] at *
            omega
          · rw [Multiset.count_cons_of_ne ha] at h1
            exact h1
        obtain ⟨m', hsub, hcoe⟩ := ih t hle
        exact ⟨m', List.Sublist.cons x hsub, hcoe⟩

  /-- The relation `fun x y => d ≤ absDiff x y` is symmetric. -/
  theorem prvB_absDiff_rel_symm (d : ℤ) :
      ∀ {x y : ℤ}, d ≤ absDiff x y → d ≤ absDiff y x := by
    intro x y h
    rw [absDiff_comm y x]
    exact h

  /-- `subExists` is invariant under permutations of the list (one direction). -/
  theorem prvB_subExists_perm_fwd {l m : List ℤ} (h : l.Perm m) (k : ℕ) (d : ℤ) :
      subExists l k d → subExists m k d := by
    rintro ⟨l', hlen, hsub, hpw⟩
    have hlm : (↑l : Multiset ℤ) = ↑m := Multiset.coe_eq_coe.mpr h
    have hle : (↑l' : Multiset ℤ) ≤ (↑m : Multiset ℤ) := by
      rw [← hlm]
      exact Multiset.coe_le.mpr hsub.subperm
    obtain ⟨m', hsub', hcoe⟩ := prvB_sublist_of_le_multiset m ↑l' hle
    have hperm : m'.Perm l' := Multiset.coe_eq_coe.mp hcoe
    refine ⟨m', ?_, hsub', ?_⟩
    · rw [hperm.length_eq, hlen]
    · exact (List.Perm.pairwise_iff (prvB_absDiff_rel_symm d) hperm.symm).mp hpw

  theorem subExists_mono_d {l : List ℤ} {k : ℕ} {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) :
      subExists l k d₂ → subExists l k d₁ := by
    rintro ⟨l', hlen, hsub, hpw⟩
    exact ⟨l', hlen, hsub, hpw.imp (fun hxy => le_trans h hxy)⟩

  theorem subExists_le_card {l : List ℤ} {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) {d : ℤ} :
      subExists l k₂ d → subExists l k₁ d := by
    rintro ⟨l', hlen, hsub, hpw⟩
    refine ⟨l'.take k₁, ?_, (List.take_sublist k₁ l').trans hsub, hpw.take⟩
    rw [List.length_take]
    omega

  theorem subExists_perm {l m : List ℤ} (h : l.Perm m) (k : ℕ) (d : ℤ) :
      subExists l k d ↔ subExists m k d :=
    ⟨prvB_subExists_perm_fwd h k d, prvB_subExists_perm_fwd h.symm k d⟩

  /-! ### Bridging index selections and sublists (`selExists` vs. `subExists`) -/

  /-- The values at the indices given by a strictly increasing map into the index range
  form a sublist of the original list. -/
  theorem prvA_ofFn_get_sublist (l : List ℤ) (m : ℕ) (f : Fin m ↪o Fin l.length) :
      (List.ofFn fun i => l.get (f i)) <+ l := by
    have hlen : (List.ofFn fun i => l.get (f i)).length = m := List.length_ofFn
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
    refine ⟨OrderEmbedding.ofStrictMono
      (fun ix : Fin (List.ofFn fun i => l.get (f i)).length => f ⟨ix.1, by omega⟩) ?_, ?_⟩
    · intro a b hab
      exact f.strictMono (by simpa using hab)
    · intro ix
      simp only [List.get_ofFn]
      congr 1

  /-- A selection of `k` index positions with all pairwise distances at least `d` yields a
  sublist of `k` values with the same pairwise property. -/
  theorem prvA_pairwise_ofFn {α : Type} (R : α → α → Prop) (k : ℕ) (g : Fin k → α)
      (h : ∀ i j : Fin k, i < j → R (g i) (g j)) : (List.ofFn g).Pairwise R := by
    have hlen : (List.ofFn g).length = k := List.length_ofFn
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simpa using hij)

  theorem prvA_selExists_imp_subExists (l : List ℤ) (k : ℕ) (d : ℤ) :
      selExists l k d → subExists l k d := by
    rintro ⟨S, hS, hcard, hcond⟩
    set e := S.orderEmbOfFin hcard with he
    have hmem : ∀ i : Fin k, e i < l.length :=
      fun i => Finset.mem_range.mp (hS (Finset.orderEmbOfFin_mem S hcard i))
    let g : Fin k → Fin l.length := fun i => ⟨e i, hmem i⟩
    have hg : StrictMono g := fun a b hab => e.strictMono hab
    let f : Fin k ↪o Fin l.length := OrderEmbedding.ofStrictMono g hg
    have hfe : ∀ i : Fin k, ((f i : ℕ)) = e i := fun i => rfl
    refine ⟨List.ofFn (fun i => l.get (f i)), List.length_ofFn, ?_, ?_⟩
    · exact prvA_ofFn_get_sublist l k f
    · refine prvA_pairwise_ofFn _ k _ ?_
      intro a b hab
      have hga : e a ∈ S := Finset.orderEmbOfFin_mem S hcard a
      have hgb : e b ∈ S := Finset.orderEmbOfFin_mem S hcard b
      have hne : e a ≠ e b := by
        intro h
        exact absurd (e.injective h) (ne_of_lt hab)
      have h1 : l.getD ((f a : ℕ)) (0 : ℤ) = l.get (f a) := List.getD_eq_get ..
      have h2 : l.getD ((f b : ℕ)) (0 : ℤ) = l.get (f b) := List.getD_eq_get ..
      rw [← h1, ← h2, hfe a, hfe b]
      exact hcond (e a) hga (e b) hgb hne

  /-- Conversely, a sublist of `k` values with all pairwise distances at least `d` gives a
  selection of `k` index positions with the same pairwise property. -/
  theorem prvA_subExists_imp_selExists (l : List ℤ) (k : ℕ) (d : ℤ) :
      subExists l k d → selExists l k d := by
    rintro ⟨l', hlen, hsub, hpw⟩
    subst hlen
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    refine ⟨Finset.univ.image (fun i => ((f i : Fin l.length) : ℕ)), ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact Finset.mem_range.mpr (f i).2
    · rw [Finset.card_image_of_injective _ (fun a b h => f.injective (Fin.ext h)),
        Finset.card_univ, Fintype.card_fin]
    · intro i hi j hj hij
      rw [Finset.mem_image] at hi hj
      obtain ⟨a, -, ha⟩ := hi
      obtain ⟨b, -, hb⟩ := hj
      rw [← ha, ← hb, List.getD_eq_get, List.getD_eq_get, ← hf a, ← hf b]
      have hne : a ≠ b := by
        intro h
        apply hij
        rw [← ha, ← hb, h]
      rcases lt_or_gt_of_ne hne with h | h
      · exact List.pairwise_iff_get.mp hpw a b h
      · rw [absDiff_comm]
        exact List.pairwise_iff_get.mp hpw b a h

  /-- The index-set formulation (`selExists`) and the sublist formulation (`subExists`) of the
  selection condition of `spec_S7` are equivalent. -/
  theorem selExists_iff_subExists (l : List ℤ) (k : ℕ) (d : ℤ) :
      selExists l k d ↔ subExists l k d :=
    ⟨prvA_selExists_imp_subExists l k d, prvA_subExists_imp_selExists l k d⟩

  theorem greedyCount_nonneg (s : List ℤ) (d last : ℤ) : 0 ≤ greedyCount s d last :=
    Nat.zero_le _

  theorem greedyCount_le_length (s : List ℤ) (d last : ℤ) :
      greedyCount s d last ≤ s.length := by
    induction s generalizing last with
    | nil => simp [greedyCount]
    | cons x xs ih =>
      rw [greedyCount]
      split
      · have := ih x; simp only [List.length_cons]; omega
      · have := ih last; simp only [List.length_cons]; omega

  /-! ### Relating `vals` to the array -/

  theorem vals_length (s : Slice Std.I64) : (vals s).length = s.val.length := by
    simp [vals]

  theorem vals_drop (s : Slice Std.I64) (i : ℕ) :
      (vals s).drop i = (s.val.drop i).map (fun x => x.val) := by
    simp [vals]

  theorem vals_getD (s : Slice Std.I64) (i : ℕ) (hi : i < (vals s).length) :
      (vals s).getD i 0 = (s.val[i]'(by simpa [vals_length] using hi)).val := by
    have h : i < s.val.length := by simpa [vals_length] using hi
    simp only [vals, List.getD, List.getElem?_map, List.getElem?_eq_getElem h,
      Option.map_some, Option.getD_some]

  /-! ### The loop invariant of `can_make` -/

  /-- Invariant of the loop of `can_make`, for the scanned suffix of `vals s`: the
  running count plus the number of elements the greedy strategy still selects equals the
  constant `C`, and the last selected value is a lower bound for the suffix. -/
  def canMakeInv (s : Slice Std.I64) (d : Std.I64) (C : ℤ)
      (st : Std.I64 × Std.I64 × Std.Usize) : Prop :=
    st.2.2.val ≤ s.val.length ∧
    (st.1.val : ℤ) + (greedyCount ((vals s).drop st.2.2.val) d.val st.2.1.val : ℤ) = C ∧
    1 ≤ st.2.1.val ∧ st.2.1.val ≤ 1000000000 ∧
    (∀ j, st.2.2.val ≤ j → j < (vals s).length → st.2.1.val ≤ (vals s).getD j 0)

  /-- In a nondecreasing list, `getD` is monotone in the index. -/
  theorem pairwise_getD_le {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) {i j : ℕ} (hij : i ≤ j)
      (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
    rcases Nat.lt_or_ge i j with h | h
    · rw [List.getD_eq_getElem _ _ (h.trans hj), List.getD_eq_getElem _ _ hj]
      exact (List.pairwise_iff_getElem.mp hs) i j (h.trans hj) hj h
    · have : i = j := by omega
      subst this
      exact le_rfl

  /-- `greedyCount` of a list, unfolded at its head. -/
  theorem greedyCount_cons (x : ℤ) (xs : List ℤ) (d last : ℤ) :
      greedyCount (x :: xs) d last =
        if d ≤ x - last then 1 + greedyCount xs d x else greedyCount xs d last := rfl

  /-- A total specification of a `Result` computation yields a value it returns. -/
  theorem spec_ok_exists {α : Type} {m : Result α} {p : WP.Post α}
      (h : WP.spec m p) : ∃ v, m = ok v ∧ p v := by
    cases m with
    | ret v => exact ⟨v, rfl, (WP.spec_ok v).1 h⟩
    | vis e k => exact absurd h (by simp [WP.spec_vis])
    | div => exact absurd h (by simp [WP.spec_div])

  /-! ### Optimality of the greedy strategy -/

  theorem prvD_le_absDiff (d a b : ℤ) (hd : 0 ≤ d) (h : d ≤ a - b) : d ≤ absDiff a b := by
    have h0 : 0 ≤ a - b := le_trans hd h
    rw [absDiff_eq_abs, abs_of_nonneg h0]
    exact h

  theorem prvD_greedyPicks_aux (s : List ℤ) (d last : ℤ) (hd : 0 ≤ d)
      (hs : s.Pairwise (· ≤ ·)) (hl : ∀ x ∈ s, last ≤ x) :
      (greedyPicks s d last).Pairwise (fun x y => d ≤ absDiff x y) ∧
        ∀ z ∈ greedyPicks s d last, d ≤ z - last := by
    induction s generalizing last with
    | nil => simp [greedyPicks]
    | cons x xs ih =>
      have hxs : xs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hxle : ∀ y ∈ xs, x ≤ y := (List.pairwise_cons.mp hs).1
      have ihx := ih x hxs hxle
      rw [greedyPicks]
      by_cases h : d ≤ x - last
      · rw [if_pos h]
        constructor
        · rw [List.pairwise_cons]
          constructor
          · intro y hy
            have hy' : d ≤ y - x := ihx.2 y hy
            have h0 : (0:ℤ) ≤ y - x := le_trans hd hy'
            rw [absDiff_comm, absDiff_eq_abs, abs_of_nonneg h0]
            exact hy'
          · exact ihx.1
        · intro z hz
          have hlx : last ≤ x := hl x (List.mem_cons_self ..)
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h
          · have h2 := ihx.2 z hz
            linarith
      · rw [if_neg h]
        exact ih last hxs (fun y hy => hl y (List.mem_cons_of_mem x hy))

  theorem prvD_greedyCount_PQ (s : List ℤ) (d : ℤ) (hs : s.Pairwise (· ≤ ·)) :
      (∀ a b : ℤ, a ≤ b → (∀ z ∈ s, b ≤ z) → greedyCount s d b ≤ greedyCount s d a) ∧
        (∀ a b : ℤ, a ≤ b → (∀ z ∈ s, b ≤ z) → greedyCount s d a ≤ 1 + greedyCount s d b) := by
    induction s with
    | nil => simp [greedyCount]
    | cons y ys ih =>
      have hys : ys.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hyle : ∀ z ∈ ys, y ≤ z := (List.pairwise_cons.mp hs).1
      have ih' := ih hys
      constructor
      · intro a b hab hb
        have hby : b ≤ y := hb y (List.mem_cons_self ..)
        have hbys : ∀ z ∈ ys, b ≤ z := fun z hz => hb z (List.mem_cons_of_mem y hz)
        have hay : a ≤ y := le_trans hab hby
        simp only [greedyCount]
        by_cases ea : d ≤ y - a
        · by_cases eb : d ≤ y - b
          · rw [if_pos ea, if_pos eb]
          · rw [if_pos ea, if_neg eb]
            have h1 := ih'.2 b y hby hyle
            have h2 := ih'.1 a y hay hyle
            omega
        · by_cases eb : d ≤ y - b
          · exact absurd (by linarith : d ≤ y - a) ea
          · rw [if_neg ea, if_neg eb]
            exact ih'.1 a b hab hbys
      · intro a b hab hb
        have hby : b ≤ y := hb y (List.mem_cons_self ..)
        have hbys : ∀ z ∈ ys, b ≤ z := fun z hz => hb z (List.mem_cons_of_mem y hz)
        have hay : a ≤ y := le_trans hab hby
        simp only [greedyCount]
        by_cases ea : d ≤ y - a
        · by_cases eb : d ≤ y - b
          · rw [if_pos ea, if_pos eb]
            omega
          · rw [if_pos ea, if_neg eb]
            have h1 := ih'.1 b y hby hyle
            omega
        · by_cases eb : d ≤ y - b
          · exact absurd (by linarith : d ≤ y - a) ea
          · rw [if_neg ea, if_neg eb]
            exact ih'.2 a b hab hbys

  theorem prvD_greedyCount_le_cons (y : ℤ) (ys : List ℤ) (d last : ℤ)
      (hys : ys.Pairwise (· ≤ ·)) (hly : last ≤ y) (hyle : ∀ z ∈ ys, y ≤ z) :
      greedyCount ys d last ≤ greedyCount (y :: ys) d last := by
    rw [greedyCount]
    by_cases h : d ≤ y - last
    · rw [if_pos h]
      exact (prvD_greedyCount_PQ ys d hys).2 last y hly hyle
    · simp only [if_neg h]
      exact le_rfl

  theorem greedyCount_optimal (s : List ℤ) (d : ℤ) (hd : 0 ≤ d) (hs : s.Pairwise (· ≤ ·))
      (last : ℤ) (hl : ∀ x ∈ s, last ≤ x) (u : List ℤ) (hus : u <+ s)
      (hu : u.Pairwise (fun x y => d ≤ absDiff x y))
      (hhead : ∀ x, u.head? = some x → d ≤ x - last) :
      u.length ≤ greedyCount s d last := by
    induction s generalizing last u with
    | nil =>
      have hu0 : u = [] := List.eq_nil_of_sublist_nil hus
      subst hu0
      simp [greedyCount]
    | cons y ys ih =>
      have hys : ys.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hyle : ∀ z ∈ ys, y ≤ z := (List.pairwise_cons.mp hs).1
      have hly : last ≤ y := hl y (List.mem_cons_self ..)
      have hlys : ∀ z ∈ ys, last ≤ z := fun z hz => hl z (List.mem_cons_of_mem y hz)
      rcases List.sublist_cons_iff.mp hus with hus' | ⟨r, rfl, hr⟩
      · have h1 := ih hys last hlys u hus' hu hhead
        exact le_trans h1 (prvD_greedyCount_le_cons y ys d last hys hly hyle)
      · have hsort : (y :: r).Pairwise (· ≤ ·) := List.Pairwise.sublist hus hs
        have hrp : r.Pairwise (fun x y => d ≤ absDiff x y) := (List.pairwise_cons.mp hu).2
        have hyr : ∀ z ∈ r, y ≤ z := (List.pairwise_cons.mp hsort).1
        have hheadr : ∀ x, r.head? = some x → d ≤ x - y := by
          intro x hx
          have hxr : x ∈ r := List.mem_of_mem_head? (by simp [hx])
          have h1 : d ≤ absDiff y x := (List.pairwise_cons.mp hu).1 x hxr
          have h2 : y ≤ x := hyr x hxr
          rw [absDiff_of_le h2] at h1
          exact h1
        have h1 : d ≤ y - last := hhead y List.head?_cons
        have h2 := ih hys y hyle r hr hrp hheadr
        rw [greedyCount, if_pos h1]
        simp only [List.length_cons]
        omega

  theorem greedyPicks_pairwise (s : List ℤ) (d : ℤ) (last : ℤ)
      (hs : s.Pairwise (· ≤ ·)) (hd : 0 ≤ d) (hl : ∀ x ∈ s, last ≤ x) :
      (greedyPicks s d last).Pairwise (fun x y => d ≤ absDiff x y) :=
    (prvD_greedyPicks_aux s d last hd hs hl).1

  theorem subExists_iff_greedyCount (s : List ℤ) (d : ℤ) (hd : 0 ≤ d) (hs : s.Pairwise (· ≤ ·))
      (hne : 1 ≤ s.length) (k : ℕ) :
      subExists s k d ↔ k ≤ 1 + greedyCount (s.drop 1) d (s.getD 0 0) := by
    cases s with
    | nil => simp at hne
    | cons y ys =>
      simp only [List.drop_one, List.tail_cons, List.getD_cons_zero]
      have hyle : ∀ z ∈ ys, y ≤ z := (List.pairwise_cons.mp hs).1
      have hl : ∀ x ∈ y :: ys, y - d ≤ x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · linarith
        · have h2 := hyle x hx
          linarith
      have hgcd : greedyCount (y :: ys) d (y - d) = 1 + greedyCount ys d y := by
        rw [greedyCount, if_pos (by linarith : d ≤ y - (y - d))]
      constructor
      · rintro ⟨l', hlen', hsub, hpair⟩
        have hhead : ∀ x, l'.head? = some x → d ≤ x - (y - d) := by
          intro x hx
          have hx1 : x ∈ l' := List.mem_of_mem_head? (by simp [hx])
          have hx2 : x ∈ y :: ys := List.Sublist.subset hsub hx1
          rcases List.mem_cons.mp hx2 with rfl | hx3
          · linarith
          · have h2 := hyle x hx3
            linarith
        have h1 := greedyCount_optimal (y :: ys) d hd hs (y - d) hl l' hsub hpair hhead
        rw [hgcd] at h1
        omega
      · intro hk
        have hpair := (prvD_greedyPicks_aux (y :: ys) d (y - d) hd hs hl).1
        have hlen : k ≤ (greedyPicks (y :: ys) d (y - d)).length := by
          rw [greedyPicks_length, hgcd]
          exact hk
        refine ⟨(greedyPicks (y :: ys) d (y - d)).take k, ?_, ?_, ?_⟩
        · rw [List.length_take]
          omega
        · exact (List.take_sublist k _).trans (greedyPicks_sublist _ _ _)
        · exact List.Pairwise.sublist (List.take_sublist k _) hpair

  /-- Splitting off the first element of a `vals` suffix. -/
  theorem vals_drop_eq_cons (s : Slice Std.I64) (i : ℕ) (hi : i < (vals s).length) :
      (vals s).drop i = (vals s).getD i 0 :: (vals s).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]

  /-- One iteration of the loop of `can_make` either finishes with the correct Boolean
  answer or preserves the invariant (and decreases the termination measure). -/
  theorem can_make_loop_body_spec0 (s : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize) (C : ℤ)
      (hn : n.val = s.val.length) (hs : (vals s).Pairwise (· ≤ ·))
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hmax : s.val.length ≤ 100000)
      (hC : C ≤ 1 + (s.val.length : ℤ))
      (hinv : canMakeInv s d C (count, last, i)) :
      Aegis.MaximumTastiness.can_make_loop.body s k d n count last i ⦃ r =>
        match r with
        | .done b => b = true ↔ (k.val : ℤ) ≤ C
        | .cont x => canMakeInv s d C x ∧ s.val.length - x.2.2.val < s.val.length - i.val ⦄ := by
    simp only [canMakeInv] at hinv
    obtain ⟨hile, hcnt, hlast1, hlast2, hlast⟩ := hinv
    have hlen : (vals s).length = s.val.length := vals_length s
    unfold Aegis.MaximumTastiness.can_make_loop.body
    split
    · rename_i hlt
      have hilen : i.val < (vals s).length := by
        have h1 := (UScalar.lt_equiv i n).1 hlt
        rw [hn] at h1
        rw [hlen]
        exact h1
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = (vals s).getD i.val 0 := by
        rw [hi1]
        exact (vals_getD s i.val hilen).symm
      have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
        rw [hi1]
        exact hval _ (List.getElem_mem _)
      have hlasti : last.val ≤ i1.val := by
        rw [hi1v]
        exact hlast i.val le_rfl hilen
      step as ⟨i2, hi2⟩
      have hd : (vals s).drop i.val = (vals s).getD i.val 0 :: (vals s).drop (i.val + 1) :=
        vals_drop_eq_cons s i.val hilen
      split
      · rename_i hge
        have hge' : d.val ≤ i1.val - last.val := by
          have h := (IScalar.le_equiv d i2).1 hge
          rw [hi2] at h
          exact h
        have hge'' : d.val ≤ (vals s).getD i.val 0 - last.val := by
          rw [← hi1v]; exact hge'
        have hstep : greedyCount ((vals s).drop i.val) d.val last.val =
            1 + greedyCount ((vals s).drop (i.val + 1)) d.val i1.val := by
          rw [hd, greedyCount_cons, if_pos hge'', ← hi1v]
        have hcntle : count.val + 1 ≤ C := by
          have hpos : 1 ≤ greedyCount ((vals s).drop i.val) d.val last.val := by
            rw [hstep]; omega
          omega
        step as ⟨count1, hcount1⟩
        split
        · rename_i hkge
          simp only [WP.spec_ok, true_iff]
          have h1 := (IScalar.le_equiv k count1).1 hkge
          omega
        · rename_i hklt
          simp only [canMakeInv]
          step as ⟨i3, hi3⟩
          refine ⟨?_, ?_, hi1b.1, hi1b.2, ?_, ?_⟩
          · omega
          · rw [hi3]
            omega
          · intro j hj hjlen
            rw [hi3] at hj
            rw [hi1v]
            exact pairwise_getD_le hs (by omega) hjlen
          · omega
      · rename_i hge
        have hge' : ¬ (d.val ≤ i1.val - last.val) := by
          intro h
          refine hge ((IScalar.le_equiv d i2).2 ?_)
          omega
        have hge'' : ¬ (d.val ≤ (vals s).getD i.val 0 - last.val) := by
          rw [← hi1v]; exact hge'
        have hstep : greedyCount ((vals s).drop i.val) d.val last.val =
            greedyCount ((vals s).drop (i.val + 1)) d.val last.val := by
          rw [hd, greedyCount_cons, if_neg hge'']
        simp only [canMakeInv]
        step as ⟨i3, hi3⟩
        refine ⟨?_, ?_, hlast1, hlast2, ?_, ?_⟩
        · omega
        · rw [hi3]
          omega
        · intro j hj hjlen
          rw [hi3] at hj
          exact hlast j (by omega) hjlen
        · omega
    · rename_i hge
      have hieq : i.val = s.val.length := by
        have h : ¬ (i.val < n.val) := by
          intro h
          exact hge ((UScalar.lt_equiv i n).2 h)
        rw [hn] at h
        omega
      have hdrop : (vals s).drop i.val = [] := List.drop_eq_nil_of_le (by rw [hlen]; omega)
      have hcnt' : (count.val : ℤ) = C := by
        rw [hdrop] at hcnt
        simpa [greedyCount] using hcnt
      simp only [WP.spec_ok]
      constructor
      · intro h
        simp only [decide_eq_true_eq] at h
        have h1 := (IScalar.le_equiv k count).1 h
        omega
      · intro h
        simp only [decide_eq_true_eq]
        exact (IScalar.le_equiv k count).2 (by omega)

  /-- Specification of the loop of `can_make`: it returns `true` exactly when the greedy
  count reaches `k`. -/
  theorem can_make_loop_spec (s : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize) (C : ℤ)
      (hn : n.val = s.val.length) (hs : (vals s).Pairwise (· ≤ ·))
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hmax : s.val.length ≤ 100000)
      (hC : C ≤ 1 + (s.val.length : ℤ))
      (hinv : canMakeInv s d C (count, last, i)) :
      Aegis.MaximumTastiness.can_make_loop s k d n count last i ⦃ b =>
        b = true ↔ (k.val : ℤ) ≤ C ⦄ := by
    unfold Aegis.MaximumTastiness.can_make_loop
    apply loop.spec_decr_nat
      (fun st : Std.I64 × Std.I64 × Std.Usize => s.val.length - st.2.2.val)
      (canMakeInv s d C) (fun b => b = true ↔ (k.val : ℤ) ≤ C)
    · intro x hx
      obtain ⟨a, b, c⟩ := x
      refine WP.spec_mono (can_make_loop_body_spec0 s k d n a b c C hn hs hval hmax hC hx) ?_
      intro r hr
      cases r with
      | done y => exact hr
      | cont x' => exact hr
    · exact hinv

  /-- Specification of `can_make`: it decides whether a selection of `k` positions with all
  pairwise distances at least `d` exists. -/
  theorem can_make_spec' (s : Slice Std.I64) (k d : Std.I64) (C : ℤ)
      (hCdef : C = 1 + (greedyCount ((vals s).drop 1) d.val ((vals s).getD 0 0) : ℤ))
      (hne : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hs : (vals s).Pairwise (· ≤ ·))
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk1 : 1 ≤ k.val)
      (hD : subExists (vals s) k.val.toNat d.val ↔ (k.val : ℤ) ≤ C) :
      Aegis.MaximumTastiness.can_make s k d ⦃ b =>
        b = true ↔ subExists (vals s) k.val.toNat d.val ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    simp only [Slice.len_val]
    split
    · rename_i hkle
      simp only [WP.spec_ok, true_iff]
      have hk : k.val = 1 := by
        have := (IScalar.le_equiv k (1#i64)).1 hkle
        simp at this ⊢
        omega
      rw [hk]
      norm_num only [Int.toNat_one]
      refine ⟨[(vals s).getD 0 0], rfl, ?_, ?_⟩
      · rw [List.singleton_sublist]
        rw [List.getD_eq_getElem _ _ (by rw [vals_length]; omega)]
        exact List.getElem_mem _
      · simp
    · rename_i hkle
      have hilen : 0 < s.val.length := by omega
      step as ⟨last, hlast⟩
      have hlastv : last.val = (vals s).getD 0 0 := by
        rw [hlast]
        exact (vals_getD s 0 (by rw [vals_length]; omega)).symm
      have hC : C ≤ 1 + (s.val.length : ℤ) := by
        rw [hCdef]
        have h := greedyCount_le_length ((vals s).drop 1) d.val ((vals s).getD 0 0)
        rw [List.length_drop, vals_length] at h
        have h1 : greedyCount ((vals s).drop 1) d.val ((vals s).getD 0 0) ≤ s.val.length := by
          omega
        have h2 : ((greedyCount ((vals s).drop 1) d.val ((vals s).getD 0 0) : ℕ) : ℤ) ≤
            (s.val.length : ℤ) := Nat.cast_le.mpr h1
        omega
      have hlastb : 1 ≤ last.val ∧ last.val ≤ 1000000000 := by
        rw [hlast]
        exact hval _ (List.getElem_mem _)
      have hlastlb : ∀ j, (1#usize).val ≤ j → j < (vals s).length →
          last.val ≤ (vals s).getD j 0 := by
        intro j hj hjlen
        rw [hlastv]
        exact pairwise_getD_le hs (by simpa using hj) hjlen
      have hinv : canMakeInv s d C (1#i64, last, 1#usize) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa using hne
        · show ((1#i64).val : ℤ) + (greedyCount ((vals s).drop (1#usize).val) d.val last.val : ℤ) = C
          simp only [hlastv]
          rw [hCdef]
          norm_num
        · simpa using hlastb.1
        · simpa using hlastb.2
        · simpa using hlastlb
      refine WP.spec_mono
        (can_make_loop_spec s k d (Slice.len s) 1#i64 last 1#usize C
          (by simp) hs hval hmax hC hinv) ?_
      intro b hb
      exact hb.trans hD.symm

  /-- Specification of `can_make`, in existential form. -/
  theorem can_make_spec (s : Slice Std.I64) (k d : Std.I64) (C : ℤ)
      (hCdef : C = 1 + (greedyCount ((vals s).drop 1) d.val ((vals s).getD 0 0) : ℤ))
      (hne : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hs : (vals s).Pairwise (· ≤ ·))
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk1 : 1 ≤ k.val)
      (hD : subExists (vals s) k.val.toNat d.val ↔ (k.val : ℤ) ≤ C) :
      ∃ b, Aegis.MaximumTastiness.can_make s k d = ok b ∧
        (b = true ↔ subExists (vals s) k.val.toNat d.val) :=
    spec_ok_exists (can_make_spec' s k d C hCdef hne hmax hs hval hk1 hD)

  /-! ### Copying the price array into a vector -/

  /-- One iteration of the first loop of `maximum_tastiness`. -/
  theorem mlt_loop0_body_spec (price : Slice Std.I64) (n : Std.Usize)
      (v : alloc.vec.Vec Std.I64) (j : Std.Usize)
      (hn : n.val = price.val.length)
      (hinv : v.val = price.val.take j.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0.body price n v j ⦃ r =>
        match r with
        | .done v' => v'.val = price.val
        | .cont x => x.1.val = price.val.take x.2.val ∧
            price.val.length - x.2.val < price.val.length - j.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0.body
    split
    · rename_i hlt
      have hjlen : j.val < price.val.length := by
        have h := (UScalar.lt_equiv j n).1 hlt
        rw [hn] at h
        exact h
      step as ⟨i1, hi1⟩
      have hvlen : v.val.length < Usize.max := by
        rw [hinv, List.length_take]
        have := Slice.property price
        omega
      step as ⟨v1, hv1⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_⟩
      · rw [hv1, hinv, hi2, hi1, List.take_add_one, List.getElem?_eq_getElem hjlen,
          Option.toList_some]
      · omega
    · rename_i hge
      have hjn : price.val.length ≤ j.val := by
        have h : ¬ (j.val < n.val) := by
          intro hh
          exact hge ((UScalar.lt_equiv j n).2 hh)
        rw [hn] at h
        omega
      simp only [WP.spec_ok]
      rw [hinv, List.take_of_length_le hjn]

  /-- Specification of the first loop of `maximum_tastiness`: it copies the whole price
  array into a vector. -/
  theorem mlt_loop0_spec (price : Slice Std.I64) (n : Std.Usize)
      (v : alloc.vec.Vec Std.I64) (j : Std.Usize)
      (hn : n.val = price.val.length)
      (hinv : v.val = price.val.take j.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n v j ⦃ v' =>
        v'.val = price.val ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
    apply loop.spec_decr_nat
      (fun st : alloc.vec.Vec Std.I64 × Std.Usize => price.val.length - st.2.val)
      (fun st => st.1.val = price.val.take st.2.val)
      (fun v' : alloc.vec.Vec Std.I64 => v'.val = price.val)
    · intro x hx
      obtain ⟨a, b⟩ := x
      refine WP.spec_mono (mlt_loop0_body_spec price n a b hn hx) ?_
      intro r hr
      cases r with
      | done v' =>
        simp only []
        exact hr
      | cont x' =>
        simp only []
        exact hr
    · show v.val = price.val.take j.val
      exact hinv

  /-! ### Correctness of the insertion sort on `I64` slices -/

  /-- The comparator of `alloc.slice.Slice.sort` at `I64`, spelled out. -/
  def prvC_cmp : Std.I64 → Std.I64 → Result Ordering := fun x y => ok (compare x.val y.val)

  @[simp]
  theorem prvC_cmp_eq (x y : Std.I64) :
      prvC_cmp x y = ok (compare x.val y.val) := rfl

  theorem prvC_cmp_OrdI64 : prvC_cmp = core.cmp.OrdI64.cmp := rfl

  /-- A list of scalars is sorted when its integer values are nondecreasing. -/
  def prvC_Sorted (l : List Std.I64) : Prop := (l.map (fun x => x.val)).Pairwise (· ≤ ·)

  theorem prvC_Sorted_cons_iff {x : Std.I64} {l : List Std.I64} :
      prvC_Sorted (x :: l) ↔
        (∀ a ∈ l.map (fun y => y.val), x.val ≤ a) ∧ prvC_Sorted l := by
    simp [prvC_Sorted]

  /-- A monadic bind whose result is `ok` comes from a successful first step. -/
  theorem prvC_bind_ok {α β : Type} {x : Result α} {f : α → Result β} {r : β}
      (h : Aeneas.Std.bind x f = ok r) : ∃ a, x = ok a ∧ f a = ok r := by
    revert h
    induction x using Result.cases with
    | ret a => intro h; exact ⟨a, rfl, by simpa using h⟩
    | vis i k => intro h; simp at h
    | div => intro h; simp at h

  /-- Insertion of `x` into a sorted list yields a sorted permutation of `x :: l`. -/
  theorem prvC_sortInsert_spec (x : Std.I64) (l : List Std.I64) :
      ∃ r, AegisShim.sortInsert prvC_cmp x l = ok r ∧ r.Perm (x :: l) ∧
        (prvC_Sorted l → prvC_Sorted r) ∧ r.length = l.length + 1 := by
    induction l generalizing x with
    | nil =>
      refine ⟨[x], ?_, List.Perm.refl _, ?_, by simp⟩
      · rw [AegisShim.sortInsert.eq_1]
      · intro _; simp [prvC_Sorted]
    | cons y ys ih =>
      obtain ⟨r1, h1, hperm1, hsorted1, hlen1⟩ := ih x
      simp only [AegisShim.sortInsert.eq_2, prvC_cmp_eq, h1, bind_ok]
      split_ifs with hb
      · have hgt : compare x.val y.val = Ordering.gt := beq_iff_eq.mp hb
        have hyx : y.val < x.val := compare_gt_iff_gt.mp hgt
        refine ⟨y :: r1, rfl, ?_, ?_, ?_⟩
        · exact List.Perm.trans (List.Perm.cons y hperm1) (List.Perm.swap x y ys)
        · intro hs
          obtain ⟨hyall, hys⟩ := prvC_Sorted_cons_iff.mp hs
          refine prvC_Sorted_cons_iff.mpr ⟨?_, hsorted1 hys⟩
          intro a ha
          have hmap : (r1.map (fun x => x.val)).Perm ((x :: ys).map (fun x => x.val)) :=
            hperm1.map (fun x => x.val)
          have hmem := (List.Perm.mem_iff hmap).mp ha
          rw [List.map_cons] at hmem
          rcases List.mem_cons.mp hmem with hax | hmem'
          · omega
          · obtain ⟨b, hb', hba⟩ := List.mem_map.mp hmem'
            have : y.val ≤ b.val := hyall b.val (List.mem_map.mpr ⟨b, hb', rfl⟩)
            omega
        · simp [hlen1]
      · have hne : ¬ compare x.val y.val = Ordering.gt := fun hh => hb (beq_iff_eq.mpr hh)
        have hle : x.val ≤ y.val := by
          have h2 : ¬ y.val < x.val := fun hlt => hne (compare_gt_iff_gt.mpr hlt)
          omega
        refine ⟨x :: y :: ys, rfl, List.Perm.refl _, ?_, by simp⟩
        intro hs
        obtain ⟨hyall, hys⟩ := prvC_Sorted_cons_iff.mp hs
        refine prvC_Sorted_cons_iff.mpr ⟨?_, hs⟩
        intro a ha
        rw [List.map_cons] at ha
        rcases List.mem_cons.mp ha with hay | hmem
        · omega
        · obtain ⟨b, hb', hba⟩ := List.mem_map.mp hmem
          have : y.val ≤ b.val := hyall b.val (List.mem_map.mpr ⟨b, hb', rfl⟩)
          omega

  /-- Insertion sort returns a sorted permutation. -/
  theorem prvC_sortList_spec (l : List Std.I64) :
      ∃ r, AegisShim.sortList prvC_cmp l = ok r ∧ r.Perm l ∧ prvC_Sorted r ∧
        r.length = l.length := by
    induction l with
    | nil =>
      refine ⟨[], ?_, List.Perm.refl _, ?_, by simp⟩
      · rw [AegisShim.sortList.eq_1]
      · simp [prvC_Sorted]
    | cons x xs ih =>
      obtain ⟨r1, h1, hperm1, hsorted1, hlen1⟩ := ih
      obtain ⟨r2, h2, hperm2, hsorted2, hlen2⟩ := prvC_sortInsert_spec x r1
      refine ⟨r2, ?_, List.Perm.trans hperm2 (List.Perm.cons x hperm1), hsorted2 hsorted1, ?_⟩
      · simp only [AegisShim.sortList.eq_2, h1, bind_ok, h2]
      · rw [hlen2, hlen1]; simp

  /-- `alloc.slice.Slice.sort` sorts a slice of `I64` by value. -/
  theorem slice_sort_spec (s : Slice Std.I64) :
      ∃ s' : Slice Std.I64, alloc.slice.Slice.sort core.cmp.OrdI64 s = ok s' ∧
        s'.val.length = s.val.length ∧ s'.val.Perm s.val ∧
        (s'.val.map (fun x => x.val)).Pairwise (· ≤ ·) := by
    obtain ⟨r, hr, hperm, hsorted, hlen⟩ := prvC_sortList_spec s.val
    have hbound : r.length ≤ Usize.max := by rw [hlen]; exact s.property
    have hs : AegisShim.sortList core.cmp.OrdI64.cmp (↑s : List Std.I64) = ok r := by
      rw [← prvC_cmp_OrdI64]; exact hr
    refine ⟨Slice.from r hbound, ?_, ?_, ?_, ?_⟩
    · rw [alloc.slice.Slice.sort.eq_1, hs]
      simp only [bind_ok, dif_pos hbound]
    · rw [Slice.from_val]; exact hlen
    · rw [Slice.from_val]; exact hperm
    · rw [Slice.from_val]; exact hsorted

  /-! ### The binary search loop -/

  /-- Invariant of the binary search loop of `maximum_tastiness`: `lo` is a feasible
  distance and `hi` is not. -/
  def loop1Inv (v : alloc.vec.Vec Std.I64) (k : Std.I64) (st : Std.I64 × Std.I64) : Prop :=
    0 ≤ st.1.val ∧ st.1.val < st.2.val ∧ st.2.val ≤ 1000000001 ∧
    Aegis.MaximumTastiness.can_make v.slice k st.1 = ok true ∧
    Aegis.MaximumTastiness.can_make v.slice k st.2 = ok false

  /-- The postcondition of the binary search loop. -/
  def loop1Post (v : alloc.vec.Vec Std.I64) (k : Std.I64) (r : Std.I64) : Prop :=
    ∀ d : ℤ, 0 ≤ d → (d ≤ r.val ↔ subExists (vals v.slice) k.val.toNat d)

  theorem loop1Inv_mk (v : alloc.vec.Vec Std.I64) (k a b : Std.I64)
      (h1 : 0 ≤ a.val) (h2 : a.val < b.val) (h3 : b.val ≤ 1000000001)
      (h4 : Aegis.MaximumTastiness.can_make v.slice k a = ok true)
      (h5 : Aegis.MaximumTastiness.can_make v.slice k b = ok false) :
      loop1Inv v k (a, b) := ⟨h1, h2, h3, h4, h5⟩

  theorem mlt_loop1_body_spec0 (v : alloc.vec.Vec Std.I64) (k lo hi : Std.I64)
      (hcm : ∀ (d : Std.I64), 0 ≤ d.val →
        ∃ b, Aegis.MaximumTastiness.can_make v.slice k d = ok b ∧
          (b = true ↔ subExists (vals v.slice) k.val.toNat d.val))
      (hinv : loop1Inv v k (lo, hi)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1.body k v lo hi ⦃ r =>
        match r with
        | .done x => loop1Post v k x
        | .cont y => loop1Inv v k y ∧
            (hi.val - lo.val).toNat > (y.2.val - y.1.val).toNat ⦄ := by
    obtain ⟨h0lo, hlt, hhi, hclo, hchi⟩ := hinv
    have h0lo' : 0 ≤ lo.val := h0lo
    have hlt' : lo.val < hi.val := hlt
    have hhi' : hi.val ≤ 1000000001 := hhi
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1.body
    step as ⟨i, hi1⟩
    split
    · rename_i hlti
      have hihi : i.val < hi.val := (IScalar.lt_equiv i hi).1 hlti
      step as ⟨i1, hi1v⟩
      step as ⟨i2, hi2v⟩
      step as ⟨mid, hmidv⟩
      have hgap : 2 ≤ i1.val := by rw [hi1v]; omega
      have hhalf : 1 ≤ i1.val.tdiv 2 := by
        have h2 := Int.le_tdiv_of_mul_le (by norm_num : (0:ℤ) < 2) (a := (1:ℤ))
          (b := i1.val) (by omega)
        simpa using h2
      have hhalf_lt : i1.val.tdiv 2 ≤ i1.val - 1 := by
        have ha : 0 ≤ i1.val := by omega
        rw [Int.tdiv_eq_ediv_of_nonneg ha]
        have h1 := Int.mul_ediv_add_emod i1.val 2
        have h2 := Int.emod_nonneg i1.val (by norm_num : (2:ℤ) ≠ 0)
        have h3 := Int.emod_lt_of_pos i1.val (by norm_num : (0:ℤ) < 2)
        omega
      have hmidgt : lo.val < mid.val := by
        rw [hmidv, hi2v]
        omega
      have hmidlt : mid.val < hi.val := by
        rw [hmidv, hi2v]
        omega
      have hderef : alloc.vec.Vec.deref v = v.slice := Slice.val_from v.slice v.slice.property
      rw [hderef]
      obtain ⟨b, hb, hbiff⟩ := hcm mid (by omega)
      rw [hb]
      simp only [bind_ok]
      split
      · rename_i hbtrue
        simp only [WP.spec_ok]
        have hbT : b = true := beq_iff_eq.mp hbtrue
        subst hbT
        refine ⟨loop1Inv_mk v k mid hi (by omega) hmidlt (by omega) hb hchi, ?_⟩
        exact (Int.toNat_lt_toNat (by omega : (0:ℤ) < hi.val - lo.val)).mpr (by omega)
      · rename_i hbfalse
        simp only [WP.spec_ok]
        have hbF : b = false := by
          cases b
          · rfl
          · exact absurd rfl hbfalse
        subst hbF
        refine ⟨loop1Inv_mk v k lo mid h0lo hmidgt (by omega) hclo hb, ?_⟩
        exact (Int.toNat_lt_toNat (by omega : (0:ℤ) < hi.val - lo.val)).mpr (by omega)
    · rename_i hge
      simp only [WP.spec_ok]
      have hle : hi.val ≤ lo.val + 1 := by
        have hni : ¬ (i.val < hi.val) := by
          intro hc
          exact hge ((IScalar.lt_equiv i hi).2 hc)
        omega
      intro d hd
      constructor
      · intro hdle
        have hsub_lo : subExists (vals v.slice) k.val.toNat lo.val := by
          obtain ⟨b, hb, hbiff⟩ := hcm lo h0lo
          rw [hclo] at hb
          have hbT : b = true := by
            cases b
            · exact absurd hb (by simp)
            · rfl
          subst hbT
          exact hbiff.mp rfl
        exact subExists_mono_d hdle hsub_lo
      · intro hsub_d
        by_contra hcon
        have hgt : lo.val < d := by omega
        have hhi_le : (hi.val : ℤ) ≤ d := by omega
        have hsub_hi : subExists (vals v.slice) k.val.toNat hi.val :=
          subExists_mono_d hhi_le hsub_d
        obtain ⟨b, hb, hbiff⟩ := hcm hi (by omega)
        rw [hchi] at hb
        have hbF : b = false := by
          cases b
          · rfl
          · exact absurd hb (by simp)
        subst hbF
        exact absurd (hbiff.mpr hsub_hi) (by simp)

  /-- The body of the binary search loop preserves its invariant. -/
  theorem mlt_loop1_body_spec (v : alloc.vec.Vec Std.I64) (k : Std.I64)
      (hcm : ∀ (d : Std.I64), 0 ≤ d.val →
        ∃ b, Aegis.MaximumTastiness.can_make v.slice k d = ok b ∧
          (b = true ↔ subExists (vals v.slice) k.val.toNat d.val)) :
      ∀ x : Std.I64 × Std.I64, loop1Inv v k x →
        (match x with
         | (lo, hi) => Aegis.MaximumTastiness.maximum_tastiness_loop1.body k v lo hi) ⦃ r =>
          match r with
          | .done y => loop1Post v k y
          | .cont y => loop1Inv v k y ∧
              (x.2.val - x.1.val).toNat > (y.2.val - y.1.val).toNat ⦄ := by
    intro x hx
    obtain ⟨a, b⟩ := x
    exact mlt_loop1_body_spec0 v k a b hcm hx

  /-- Specification of the binary search loop: it returns the largest feasible distance. -/
  theorem mlt_loop1_spec (v : alloc.vec.Vec Std.I64) (k lo hi : Std.I64)
      (hcm : ∀ (d : Std.I64), 0 ≤ d.val →
        ∃ b, Aegis.MaximumTastiness.can_make v.slice k d = ok b ∧
          (b = true ↔ subExists (vals v.slice) k.val.toNat d.val))
      (hinv : loop1Inv v k (lo, hi)) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k v lo hi ⦃ r =>
        loop1Post v k r ⦄ := by
    unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
    apply loop.spec_decr_nat
      (fun st : Std.I64 × Std.I64 => (st.2.val - st.1.val).toNat)
      (loop1Inv v k) (loop1Post v k)
    · intro x hx
      refine WP.spec_mono (mlt_loop1_body_spec v k hcm x hx) ?_
      intro r hr
      cases r with
      | done y =>
        simp only []
        exact hr
      | cont y =>
        simp only []
        exact hr
    · exact hinv

  /-! ### Auxiliary facts about `subExists` and extrema of a sorted list -/

  /-- Every list with at least `k` elements has a `k`-element sublist all of whose
  pairwise distances are at least `0`. -/
  theorem subExists_zero (l : List ℤ) (k : ℕ) (hk : k ≤ l.length) : subExists l k 0 := by
    refine ⟨l.take k, ?_, List.take_sublist k l, ?_⟩
    · rw [List.length_take]; omega
    · rw [List.pairwise_iff_getElem]
      intro i j _ _ _
      exact absDiff_nonneg _ _

  /-- In a nondecreasing nonempty list, the distance of two entries is at most the
  difference of the last and the first entry. -/
  theorem absDiff_le_of_sorted {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) (hne : 1 ≤ l.length)
      {x y : ℤ} (hx : x ∈ l) (hy : y ∈ l) :
      absDiff x y ≤ l.getD (l.length - 1) 0 - l.getD 0 0 := by
    have hlast : l.length - 1 < l.length := by omega
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hy
    have hxi : l.getD 0 0 ≤ l.getD i 0 := pairwise_getD_le hs (by omega) hi
    have hxj : l.getD i 0 ≤ l.getD (l.length - 1) 0 :=
      pairwise_getD_le hs (by omega) hlast
    have hyi : l.getD 0 0 ≤ l.getD j 0 := pairwise_getD_le hs (by omega) hj
    have hyj : l.getD j 0 ≤ l.getD (l.length - 1) 0 :=
      pairwise_getD_le hs (by omega) hlast
    have hxi' : l.getD 0 0 ≤ x := by
      rw [← hix, ← List.getD_eq_getElem l 0 hi]; exact hxi
    have hxj' : x ≤ l.getD (l.length - 1) 0 := by
      rw [← hix, ← List.getD_eq_getElem l 0 hi]; exact hxj
    have hyi' : l.getD 0 0 ≤ y := by
      rw [← hjx, ← List.getD_eq_getElem l 0 hj]; exact hyi
    have hyj' : y ≤ l.getD (l.length - 1) 0 := by
      rw [← hjx, ← List.getD_eq_getElem l 0 hj]; exact hyj
    rw [absDiff_eq_abs, abs_le]
    constructor <;> omega

  /-- If all pairwise distances in `l` are at most `W` and `W < d`, then there is no
  sublist of `k ≥ 2` elements with all pairwise distances at least `d`. -/
  theorem subExists_false_of_bound {l : List ℤ} {W d : ℤ} {k : ℕ}
      (hbound : ∀ x ∈ l, ∀ y ∈ l, absDiff x y ≤ W) (hW : W < d) (hk : 2 ≤ k) :
      ¬ subExists l k d := by
    rintro ⟨l', hlen, hsub, hpw⟩
    have h2 : 2 ≤ l'.length := by omega
    have h0 : 0 < l'.length := by omega
    have hp := List.pairwise_iff_getElem.mp hpw 0 1 h0 h2 (by norm_num)
    have hmem0 : l'[0] ∈ l := List.Sublist.subset hsub (List.getElem_mem ..)
    have hmem1 : l'[1] ∈ l := List.Sublist.subset hsub (List.getElem_mem ..)
    have hb := hbound _ hmem0 _ hmem1
    omega

  /-- Overflow-free subtraction of small nonnegative `I64`s. -/
  theorem i64_sub_spec {x y : Std.I64} (h1 : 0 ≤ x.val) (h2 : x.val ≤ 1000000000)
      (h3 : 0 ≤ y.val) (h4 : y.val ≤ 1000000000) :
      x - y ⦃ z => z.val = x.val - y.val ⦄ :=
    IScalar.sub_spec (by scalar_tac) (by scalar_tac)

  /-- Overflow-free addition of small nonnegative `I64`s. -/
  theorem i64_add_spec {x y : Std.I64} (h1 : 0 ≤ x.val) (h2 : x.val ≤ 1000000000)
      (h3 : 0 ≤ y.val) (h4 : y.val ≤ 1000000000) :
      x + y ⦃ z => z.val = x.val + y.val ⦄ :=
    IScalar.add_spec (by scalar_tac) (by scalar_tac)

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
  theorem spec_7 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ d : ℤ, 0 ≤ d → (d ≤ r.val ↔
          ∃ S : Finset ℕ, S ⊆ Finset.range (vals price).length ∧ S.card = k.val.toNat ∧
            ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
              d ≤ absDiff ((vals price).getD i 0) ((vals price).getD j 0)) := by
    set P : Std.I64 → Prop := fun r => ∀ d : ℤ, 0 ≤ d →
      (d ≤ r.val ↔ selExists (vals price) k.val.toNat d) with hP
    change ∃ r, maximum_tastiness price k = ok r ∧ P r
    unfold maximum_tastiness
    simp only [Slice.len_val]
    have hn2 : 2 ≤ price.val.length := h_n
    have hn100 : price.val.length ≤ 100000 := h_len
    have hne : ¬ (Slice.len price = 0#usize) := by
      intro h
      have h2 : (Slice.len price).val = 0 := by rw [h]; rfl
      rw [Slice.len_val] at h2
      omega
    rw [if_neg hne]
    refine spec_ok_exists ?_
    have hspec_of_exists : ∀ {α : Type} {m : Result α} {p : WP.Post α},
        (∃ v, m = ok v ∧ p v) → WP.spec m p := by
      intro α m p h
      obtain ⟨v, hv, hp⟩ := h
      rw [hv]
      simpa using hp
    refine WP.spec_bind (mlt_loop0_spec price (Slice.len price)
      (alloc.vec.Vec.new Std.I64) 0#usize ?_ ?_) ?_
    · exact Slice.len_val price
    · simp [alloc.vec.Vec.new]
    · intro v1 hv1
      have hdm : lift (alloc.vec.Vec.deref_mut v1) ⦃ p =>
          p.1.val = v1.val ∧ (∀ s : Slice Std.I64, (p.2 s).val = s.val) ⦄ := by
        simp only [lift, WP.spec_ok]
        exact ⟨rfl, fun s => rfl⟩
      refine WP.spec_bind hdm ?_
      intro p hp
      obtain ⟨s, back⟩ := p
      obtain ⟨hps, hpb⟩ := hp
      change (do
        let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 s
        let i ← Slice.len price - 1#usize
        let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) (back s1) i
        let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) (back s1) 0#usize
        let max_diff ← i1 - i2
        let hi ← max_diff + 1#i64
        Aegis.MaximumTastiness.maximum_tastiness_loop1 k (back s1) 0#i64 hi) ⦃ P ⦄
      refine WP.spec_bind (hspec_of_exists (slice_sort_spec s)) ?_
      intro s1 hs1
      obtain ⟨hs1len, hs1perm, hs1sorted⟩ := hs1
      have hsub : (1#usize).val ≤ (Slice.len price).val := by
        have h1 : 2 ≤ price.val.length := h_n
        have h2 : 1 ≤ price.val.length := by omega
        simpa [Slice.len_val] using h2
      refine WP.spec_bind (Usize.sub_spec (x := Slice.len price) (y := 1#usize) hsub) ?_
      intro i hi
      obtain ⟨hi1, hi2⟩ := hi
      simp only [alloc.vec.Vec.index_slice_index]
      -- basic facts about the sorted vector
      have hbl : (back s1).val = s1.val := hpb s1
      have hsliceval : (back s1).slice.val = s1.val := hbl
      have hsl : s.val = v1.val := hps
      have hsl_len : s.val.length = price.val.length := by rw [hsl, hv1]
      have hblen : (back s1).length = price.val.length := by
        show (back s1).val.length = price.val.length
        rw [hbl, hs1len, hsl_len]
      have hperm : s1.val.Perm price.val := by
        have h := hs1perm
        rw [hsl, hv1] at h
        exact h
      have hperm' : (back s1).slice.val.Perm price.val := by
        rw [hsliceval]; exact hperm
      have hvals : vals (back s1).slice = (back s1).slice.val.map (fun x => x.val) := rfl
      have hsvs : (vals (back s1).slice).Pairwise (· ≤ ·) := by
        rw [hvals, hsliceval]
        exact hs1sorted
      have hvslen : (vals (back s1).slice).length = price.val.length := by
        rw [hvals, List.length_map, hsliceval, hs1len, hsl_len]
      have hval' : ∀ x ∈ (back s1).slice.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
        intro x hx
        rw [hsliceval] at hx
        exact h_price x (hperm.mem_iff.mp hx)
      have hne1 : 1 ≤ (back s1).slice.val.length := by
        have h2 : 2 ≤ price.val.length := h_n
        rw [hsliceval, hs1len, hsl_len]; omega
      have hmax1 : (back s1).slice.val.length ≤ 100000 := by
        have h2 : price.val.length ≤ 100000 := h_len
        rw [hsliceval, hs1len, hsl_len]; omega
      have hiv : i.val = price.val.length - 1 := by
        rw [hi1, Slice.len_val]
        have h1v : (1#usize).val = 1 := rfl
        rw [h1v]
      have hib1 : i.val < (back s1).length := by
        have h2 : 2 ≤ price.val.length := h_n
        rw [hiv, hblen]; omega
      refine WP.spec_bind (alloc.vec.Vec.index_usize_spec (back s1) i hib1) ?_
      intro i1 hi1v
      have hib0 : (0#usize).val < (back s1).length := by
        have h0 : (0#usize).val = 0 := rfl
        have h2 : 2 ≤ price.val.length := h_n
        rw [hblen, h0]; omega
      refine WP.spec_bind (alloc.vec.Vec.index_usize_spec (back s1) 0#usize hib0) ?_
      intro i2 hi2v
      have hi1e : i1.val = ((back s1).slice.val)[i.val].val := by
        rw [hi1v]; rfl
      have hi2e : i2.val = ((back s1).slice.val)[(0#usize).val].val := by
        rw [hi2v]; rfl
      have hidx0 : (0#usize).val = 0 := rfl
      have hidx : i.val = (vals (back s1).slice).length - 1 := by
        rw [hiv, hvslen]
      have hivlen : i.val < (vals (back s1).slice).length := by
        have h2 : 2 ≤ price.val.length := h_n
        rw [hvslen, hiv]; omega
      have hi1g0 : (vals (back s1).slice).getD i.val 0 = i1.val := by
        rw [vals_getD ((back s1).slice) i.val (by simpa using hivlen)]
        exact hi1e.symm
      have hi1g : i1.val = (vals (back s1).slice).getD ((vals (back s1).slice).length - 1) 0 := by
        rw [← hidx]
        exact hi1g0.symm
      have hi2g : i2.val = (vals (back s1).slice).getD 0 0 := by
        have hlt : 0 < (vals (back s1).slice).length := by rw [hvslen]; omega
        have h0 : (vals (back s1).slice).getD 0 0 = i2.val := by
          rw [vals_getD ((back s1).slice) 0 (by simpa using hlt)]
          exact hi2e.symm
        exact h0.symm
      have hi21 : i2.val ≤ i1.val := by
        rw [hi1g, hi2g]
        exact pairwise_getD_le hsvs (by omega) (by omega)
      obtain ⟨hi1pos, hi1le⟩ := hval' i1 (by rw [hi1v]; exact List.getElem_mem ..)
      obtain ⟨hi2pos, hi2le⟩ := hval' i2 (by rw [hi2v]; exact List.getElem_mem ..)
      have hmd0 : 0 ≤ i1.val - i2.val := by omega
      have hmd1 : i1.val - i2.val ≤ 1000000000 := by omega
      refine WP.spec_bind (i64_sub_spec (x := i1) (y := i2) (by omega) hi1le
        (by omega) hi2le) ?_
      intro md hmd
      have hmdv : md.val = i1.val - i2.val := hmd
      have hmdXY : md.val = (vals (back s1).slice).getD ((vals (back s1).slice).length - 1) 0
          - (vals (back s1).slice).getD 0 0 := by rw [hmdv, hi1g, hi2g]
      have hmdn : 0 ≤ md.val := by rw [hmdv]; omega
      have hmdl : md.val ≤ 1000000000 := by rw [hmdv]; omega
      have hone : (1#i64).val = 1 := rfl
      refine WP.spec_bind (i64_add_spec (x := md) (y := 1#i64) hmdn hmdl ?_ ?_) ?_
      · rw [hone]; omega
      · rw [hone]; omega
      intro hfin hfinv
      have hfinv' : hfin.val = md.val + 1 := by simpa using hfinv
      have hfin_gt : 0 < hfin.val := by rw [hfinv']; omega
      have hfin_le : hfin.val ≤ 1000000001 := by rw [hfinv']; omega
      have hmd_lt : md.val < hfin.val := by rw [hfinv']; omega
      have hk1 : 1 ≤ k.val := by omega
      -- `can_make` decides `subExists` at every nonnegative `d`
      have hcm : ∀ d : Std.I64, 0 ≤ d.val → ∃ b,
          Aegis.MaximumTastiness.can_make (back s1).slice k d = ok b ∧
            (b = true ↔ subExists (vals (back s1).slice) k.val.toNat d.val) := by
        intro d hd
        have hk' : (k.val : ℤ) = (k.val.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        have hcast : (1 : ℤ)
            + (greedyCount ((vals (back s1).slice).drop 1) d.val
                ((vals (back s1).slice).getD 0 0) : ℤ)
            = ((1 + greedyCount ((vals (back s1).slice).drop 1) d.val
                ((vals (back s1).slice).getD 0 0) : ℕ) : ℤ) := by push_cast; ring
        have hD : subExists (vals (back s1).slice) k.val.toNat d.val ↔
            (k.val : ℤ) ≤ 1 + (greedyCount ((vals (back s1).slice).drop 1) d.val
                ((vals (back s1).slice).getD 0 0) : ℤ) := by
          rw [hk', hcast, Nat.cast_le]
          have hne' : 1 ≤ (vals (back s1).slice).length := by rw [hvslen]; omega
          exact subExists_iff_greedyCount (vals (back s1).slice) d.val hd hsvs hne' k.val.toNat
        exact can_make_spec (back s1).slice k d _ rfl hne1 hmax1 hsvs hval' hk1 hD
      have hklen : k.val.toNat ≤ (vals (back s1).slice).length := by
        rw [hvslen]
        have hk'' : (k.val : ℤ) = (k.val.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        have hle := h_k_hi
        rw [hk''] at hle
        exact Nat.cast_le.mp hle
      have hzero64 : (0#i64).val = 0 := rfl
      obtain ⟨b0, hb0, hb0iff⟩ := hcm 0#i64 (by rw [hzero64])
      have hsub0 : subExists (vals (back s1).slice) k.val.toNat (0#i64).val := by
        simpa [hzero64] using subExists_zero (vals (back s1).slice) k.val.toNat hklen
      have hb0t : b0 = true := hb0iff.mpr hsub0
      obtain ⟨bf, hbf, hbfiff⟩ := hcm hfin (by omega)
      have hsubf : ¬ subExists (vals (back s1).slice) k.val.toNat hfin.val := by
        refine subExists_false_of_bound (W := md.val) (d := hfin.val) ?_ hmd_lt (by omega)
        intro a ha b hb
        rw [hmdXY]
        have hne' : 1 ≤ (vals (back s1).slice).length := by rw [hvslen]; omega
        exact absDiff_le_of_sorted hsvs hne' ha hb
      have hbfF : bf = false := by
        cases bf
        · rfl
        · exact absurd (hbfiff.mp rfl) hsubf
      have hinv : loop1Inv (back s1) k (0#i64, hfin) := by
        refine loop1Inv_mk (back s1) k 0#i64 hfin ?_ hfin_gt hfin_le ?_ ?_
        · rw [hzero64]
        · rw [hb0, hb0t]
        · rw [hbf, hbfF]
      have hpermv : (vals (back s1).slice).Perm (vals price) := by
        rw [hvals]
        exact hperm'.map (fun x => x.val)
      refine WP.spec_mono (mlt_loop1_spec (back s1) k 0#i64 hfin hcm hinv) ?_
      intro r hr
      rw [hP]
      intro d hd
      rw [hr d hd, selExists_iff_subExists (vals price) k.val.toNat d]
      exact subExists_perm hpermv k.val.toNat d

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
