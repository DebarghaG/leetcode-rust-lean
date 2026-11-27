import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_13` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary lemmas about the extracted program -/

  namespace Aux

  open AegisShim

  /-- The `I64` comparator used by the extracted insertion sort. -/
  abbrev cmpI : Std.I64 → Std.I64 → Result Ordering := core.cmp.OrdI64.cmp

  theorem cmpI_eq (x y : Std.I64) : cmpI x y = ok (compare x.val y.val) := rfl

  theorem compare_gt_iff (x y : Std.I64) :
      (compare x.val y.val == Ordering.gt) ↔ y.val < x.val := by
    simp only [compare]
    unfold compareOfLessAndEq
    split <;> simp_all
    omega

  /-- `sortInsert` always succeeds. -/
  theorem sortInsert_ok (l : List Std.I64) : ∀ x, ∃ r, AegisShim.sortInsert cmpI x l = ok r := by
    induction l with
    | nil => intro x; exact ⟨[x], rfl⟩
    | cons y ys ih =>
      intro x
      simp only [AegisShim.sortInsert, cmpI_eq, bind_ok]
      by_cases h : (compare x.val y.val == Ordering.gt) = true
      · rw [if_pos h]
        obtain ⟨r, hr⟩ := ih x
        exact ⟨y :: r, by rw [hr]; simp⟩
      · rw [if_neg h]
        exact ⟨x :: y :: ys, rfl⟩

  /-- `sortList` always succeeds. -/
  theorem sortList_ok (l : List Std.I64) : ∃ r, AegisShim.sortList cmpI l = ok r := by
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x xs ih =>
      simp only [AegisShim.sortList, bind_ok]
      obtain ⟨r, hr⟩ := ih
      rw [hr]
      simp only [bind_ok]
      exact sortInsert_ok r x

  /-- `sortInsert` inserts an element, up to permutation. -/
  theorem sortInsert_perm (l : List Std.I64) :
      ∀ x r, AegisShim.sortInsert cmpI x l = ok r → r.Perm (x :: l) := by
    induction l with
    | nil =>
      intro x r h
      simp only [AegisShim.sortInsert, ok.injEq] at h
      subst h
      exact List.Perm.refl _
    | cons y ys ih =>
      intro x r h
      simp only [AegisShim.sortInsert, cmpI_eq, bind_ok] at h
      by_cases hc : (compare x.val y.val == Ordering.gt) = true
      · rw [if_pos hc] at h
        obtain ⟨r', hr'⟩ := sortInsert_ok ys x
        rw [hr'] at h
        simp only [bind_ok, ok.injEq] at h
        subst h
        exact (List.Perm.cons y (ih x r' hr')).trans (List.Perm.swap x y ys)
      · rw [if_neg hc] at h
        simp only [ok.injEq] at h
        subst h
        exact List.Perm.refl _

  /-- `sortList` rearranges the list. -/
  theorem sortList_perm (l : List Std.I64) :
      ∀ r, AegisShim.sortList cmpI l = ok r → r.Perm l := by
    induction l with
    | nil =>
      intro r h
      simp only [AegisShim.sortList, ok.injEq] at h
      subst h
      exact List.Perm.refl _
    | cons x xs ih =>
      intro r h
      simp only [AegisShim.sortList, bind_ok] at h
      obtain ⟨r', hr'⟩ := sortList_ok xs
      rw [hr'] at h
      simp only [bind_ok] at h
      exact (sortInsert_perm r' x r h).trans (List.Perm.cons x (ih r' hr'))

  /-- A list of `I64` whose values are nondecreasing. -/
  def SortedV (l : List Std.I64) : Prop := l.Pairwise (fun a b => a.val ≤ b.val)

  theorem SortedV.cons {a : Std.I64} {l : List Std.I64} (h : ∀ b ∈ l, a.val ≤ b.val)
      (hl : SortedV l) : SortedV (a :: l) :=
    List.Pairwise.cons h hl

  theorem SortedV.tail {a : Std.I64} {l : List Std.I64} (h : SortedV (a :: l)) : SortedV l :=
    (List.pairwise_cons.mp h).2

  /-- Inserting an element into a sorted list keeps it sorted. -/
  theorem sortInsert_sorted (l : List Std.I64) :
      SortedV l → ∀ x r, AegisShim.sortInsert cmpI x l = ok r → SortedV r := by
    induction l with
    | nil =>
      intro _ x r h
      simp only [AegisShim.sortInsert, ok.injEq] at h
      subst h
      exact SortedV.cons (fun b hb => by simp at hb) List.Pairwise.nil
    | cons y ys ih =>
      intro hs x r h
      simp only [AegisShim.sortInsert, cmpI_eq, bind_ok] at h
      obtain ⟨hall, hys⟩ := List.pairwise_cons.mp hs
      by_cases hc : (compare x.val y.val == Ordering.gt) = true
      · rw [if_pos hc] at h
        obtain ⟨r', hr'⟩ := sortInsert_ok ys x
        rw [hr'] at h
        simp only [bind_ok, ok.injEq] at h
        subst h
        have h1 : SortedV r' := ih hys x r' hr'
        have h2 : y.val ≤ x.val := by
          have := (compare_gt_iff x y).mp hc
          omega
        refine SortedV.cons ?_ h1
        intro b hb
        have hbm : b = x ∨ b ∈ ys := by
          simpa using (sortInsert_perm ys x r' hr').mem_iff.mp hb
        rcases hbm with hbx | hb'
        · rw [hbx]; exact h2
        · exact hall b hb'
      · rw [if_neg hc] at h
        simp only [ok.injEq] at h
        subst h
        have h2 : x.val ≤ y.val := by
          have := (compare_gt_iff x y).not.mp hc
          omega
        exact SortedV.cons (fun b hb => by
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact h2
          · exact le_trans h2 (hall b hb')) hs

  /-- `sortList` sorts. -/
  theorem sortList_sorted (l : List Std.I64) :
      ∀ r, AegisShim.sortList cmpI l = ok r → SortedV r := by
    induction l with
    | nil =>
      intro r h
      simp only [AegisShim.sortList, ok.injEq] at h
      subst h
      exact List.Pairwise.nil
    | cons x xs ih =>
      intro r h
      simp only [AegisShim.sortList, bind_ok] at h
      obtain ⟨r', hr'⟩ := sortList_ok xs
      rw [hr'] at h
      simp only [bind_ok] at h
      exact sortInsert_sorted r' (ih r' hr') x r h

  /-- Two sorted lists which are permutations of each other are equal. -/
  theorem SortedV.eq_of_perm {l₁ l₂ : List Std.I64} (h₁ : SortedV l₁) (h₂ : SortedV l₂)
      (hp : l₁.Perm l₂) : l₁ = l₂ := by
    have h₁' : l₁.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) := h₁
    have h₂' : l₂.Pairwise (fun a b : Std.I64 => a.val ≤ b.val) := h₂
    exact List.Perm.eq_of_pairwise (le := fun a b : Std.I64 => a.val ≤ b.val)
      (fun a b _ _ h1 h2 => IScalar.eq_of_val_eq (le_antisymm h1 h2)) h₁' h₂' hp

  /-- `sortList` only depends on the multiset of its argument. -/
  theorem sortList_eq_of_perm {l₁ l₂ : List Std.I64} (hp : l₁.Perm l₂) :
      AegisShim.sortList cmpI l₁ = AegisShim.sortList cmpI l₂ := by
    obtain ⟨r₁, hr₁⟩ := sortList_ok l₁
    obtain ⟨r₂, hr₂⟩ := sortList_ok l₂
    rw [hr₁, hr₂]
    have h := SortedV.eq_of_perm (sortList_sorted l₁ r₁ hr₁) (sortList_sorted l₂ r₂ hr₂)
      ((sortList_perm l₁ r₁ hr₁).trans (hp.trans (sortList_perm l₂ r₂ hr₂).symm))
    rw [h]

  /-- `Slice.sort` (insertion sort over `I64`) succeeds, and the result is a sorted
  rearrangement of the input. -/
  theorem slice_sort_spec (s : Slice Std.I64) :
      ∃ r, alloc.slice.Slice.sort core.cmp.OrdI64 s = ok r ∧ r.val.Perm s.val ∧
        SortedV r.val := by
    obtain ⟨l, hl⟩ := sortList_ok s.val
    have hlbound : l.length ≤ Std.Usize.max := by
      rw [(sortList_perm s.val l hl).length_eq]
      exact s.property
    refine ⟨Slice.from l hlbound, ?_, ?_, ?_⟩
    · simp only [alloc.slice.Slice.sort, hl, bind_ok, dif_pos hlbound]
    · rw [Slice.from_val]; exact sortList_perm s.val l hl
    · rw [Slice.from_val]; exact sortList_sorted s.val l hl

  /-- `Slice.sort` (insertion sort over `I64`) only depends on the multiset of its input. -/
  theorem slice_sort_eq_of_perm {s₁ s₂ : Slice Std.I64} (h : s₁.val.Perm s₂.val) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s₁ = alloc.slice.Slice.sort core.cmp.OrdI64 s₂ := by
    have h' := sortList_eq_of_perm h
    simp only [alloc.slice.Slice.sort]
    rw [h']

  /-- The continuation of `maximum_tastiness` after building the copy of the input array:
  sort it, then run the binary search for the largest feasible gap. -/
  def tail (n : Std.Usize) (k : Std.I64) (sorted : alloc.vec.Vec Std.I64) : Result Std.I64 := do
    let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 sorted.slice
    let sorted1 : alloc.vec.Vec Std.I64 := ⟨s1⟩
    let i ← n - 1#usize
    let i1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) sorted1 i
    let i2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) sorted1 0#usize
    let max_diff ← i1 - i2
    let hi ← max_diff + 1#i64
    Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted1 0#i64 hi

  /-- The tail only depends on the multiset of the array contents. -/
  theorem tail_congr {n : Std.Usize} {k : Std.I64} {v v' : alloc.vec.Vec Std.I64}
      (h : List.Perm (alloc.vec.Vec.val v) (alloc.vec.Vec.val v')) :
      tail n k v = tail n k v' := by
    have hs : alloc.slice.Slice.sort core.cmp.OrdI64 v.slice
        = alloc.slice.Slice.sort core.cmp.OrdI64 v'.slice := slice_sort_eq_of_perm h
    simp only [tail]
    rw [hs]

  /-- `Slice.len` vanishes exactly for empty slices. -/
  theorem slice_len_eq_zero_iff (s : Slice Std.I64) : Slice.len s = 0#usize ↔ s.length = 0 := by
    constructor
    · intro h
      have := congrArg UScalar.val h
      simpa using this
    · intro h
      apply UScalar.eq_of_val_eq
      simp [h]

  /-- Unfolding of `maximum_tastiness` on a nonempty array. -/
  theorem maximum_tastiness_unfold (s : Slice Std.I64) (k : Std.I64) (hne : s.length ≠ 0) :
      maximum_tastiness s k =
        (do
          let sorted ←
            Aegis.MaximumTastiness.maximum_tastiness_loop0 s (Slice.len s)
              (alloc.vec.Vec.new Std.I64) 0#usize
          tail (Slice.len s) k sorted) := by
    have h0 : ¬ (Slice.len s = 0#usize) := fun h => hne ((slice_len_eq_zero_iff s).mp h)
    simp only [maximum_tastiness, h0, if_false, lift, alloc.vec.Vec.deref_mut, bind_ok,
      tail, ↓reduceDIte]
    rfl

  /-- Specification of the copy loop: it collects the contents of the array. -/
  theorem loop0_spec (s : Slice Std.I64) (i : Std.Usize) (acc : alloc.vec.Vec Std.I64)
      (hb : s.val.length < Std.Usize.max)
      (hi : i.val ≤ s.val.length) (hacc : alloc.vec.Vec.val acc = s.val.take i.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 s (Slice.len s) acc i ⦃
        v => alloc.vec.Vec.val v = s.val ⦄ := by
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec Std.I64 × Std.Usize => s.val.length - p.2.val)
      (inv := fun p => p.2.val ≤ s.val.length ∧
        alloc.vec.Vec.val p.1 = s.val.take p.2.val)
      (post := fun v : alloc.vec.Vec Std.I64 => alloc.vec.Vec.val v = s.val)
    · rintro ⟨a, j⟩ ⟨hj, ha⟩
      dsimp only at hj ha ⊢
      simp only [Aegis.MaximumTastiness.maximum_tastiness_loop0.body]
      split_ifs with hlt
      · have hltv : j.val < s.val.length := by simpa using hlt
        apply WP.spec_bind (Slice.index_usize_spec s j hltv)
        intro x hx
        have hlen : a.val.length < Std.Usize.max := by
          rw [ha, List.length_take]; scalar_tac
        apply WP.spec_bind (alloc.vec.Vec.push_spec a x hlen)
        intro a' ha'
        have hside : j.val + (1#usize).val ≤ UScalar.max (ty := .Usize) := by scalar_tac
        apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := j) (y := 1#usize) hside)
        intro j' hj'
        simp only [WP.spec_ok]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · scalar_tac
        · rw [ha', ha, hj', hx]
          have h1 : (1#usize).val = 1 := by simp
          rw [h1]
          exact List.take_concat_get' (l := s.val) (i := j.val) hltv
        · scalar_tac
      · have hjn : j.val = s.val.length := by
          have h2 : ¬ (j.val < s.val.length) := by simpa using hlt
          omega
        simp only [WP.spec_ok]
        rw [ha, hjn, List.take_length]
    · exact ⟨hi, hacc⟩

  /-- The copy loop run from the start collects the whole array. -/
  theorem loop0_spec_start (s : Slice Std.I64) (hb : s.val.length < Std.Usize.max) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 s (Slice.len s)
        (alloc.vec.Vec.new Std.I64) 0#usize ⦃
        v => alloc.vec.Vec.val v = s.val ⦄ := by
    apply loop0_spec s 0#usize _ hb (by simp) (by simp)

  /-- `spec` implies that the computation returns an actual value. -/
  theorem spec_exists_ok {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
      ∃ x, m = ok x ∧ p x := by
    revert h
    refine Result.cases m ?_ ?_ ?_
    · intro x h
      exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
    · intro e k h
      exact absurd h (by simp)
    · intro h
      exact absurd h (by simp)

  /-- `maximum_tastiness` only depends on the multiset of the array contents. -/
  theorem maximum_tastiness_perm {s s' : Slice Std.I64} {k : Std.I64}
      (h : s.val.Perm s'.val) (hne : s.val.length ≠ 0)
      (hb : s.val.length < Std.Usize.max) :
      maximum_tastiness s k = maximum_tastiness s' k := by
    have hlen : s.val.length = s'.val.length := h.length_eq
    have hne' : s'.val.length ≠ 0 := by rw [← hlen]; exact hne
    have hb' : s'.val.length < Std.Usize.max := by rw [← hlen]; exact hb
    obtain ⟨v, hv, hvv⟩ := spec_exists_ok (loop0_spec_start s hb)
    obtain ⟨v', hv', hvv'⟩ := spec_exists_ok (loop0_spec_start s' hb')
    have hlenU : Slice.len s = Slice.len s' := by
      apply UScalar.eq_of_val_eq
      simp [hlen]
    rw [maximum_tastiness_unfold s k hne, maximum_tastiness_unfold s' k hne']
    rw [hv, hv']
    simp only [bind_ok]
    rw [hlenU]
    exact tail_congr (by rw [hvv, hvv']; exact h)

  /-- The gap test `can_make_loop` always terminates without failing. -/
  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (hn : n.val = sorted.val.length) (i : Std.Usize) (count last : Std.I64)
      (hi : i.val ≤ n.val) (hb : sorted.val.length < Std.Usize.max)
      (hlen : sorted.val.length ≤ 100000)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hc1 : 1 ≤ count.val) (hc2 : count.val ≤ i.val)
      (hl1 : 1 ≤ last.val) (hl2 : last.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i ⦃ _ => True ⦄ := by
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun p : Std.I64 × Std.I64 × Std.Usize => n.val - p.2.2.val)
      (inv := fun p => p.2.2.val ≤ n.val ∧
        (1 ≤ p.2.1.val ∧ p.2.1.val ≤ 1000000000) ∧
        (1 ≤ p.1.val ∧ p.1.val ≤ p.2.2.val))
      (post := fun (_ : Bool) => True)
    · rintro ⟨c, l, j⟩ ⟨hj, ⟨hl1', hl2'⟩, ⟨hc1', hc2'⟩⟩
      dsimp only at hj hl1' hl2' hc1' hc2' ⊢
      simp only [Aegis.MaximumTastiness.can_make_loop.body]
      split_ifs with hlt
      · have hltv : j.val < sorted.val.length := by
          have h2 : j.val < n.val := by simpa using hlt
          omega
        apply WP.spec_bind (Slice.index_usize_spec sorted j hltv)
        intro x hx
        have hxval : 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
          refine hval x ?_
          rw [hx]
          exact List.getElem_mem hltv
        have hsub1 : IScalar.min (.I64) ≤ x.val - l.val := by scalar_tac
        have hsub2 : x.val - l.val ≤ IScalar.max (.I64) := by scalar_tac
        apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := x) (y := l) hsub1 hsub2)
        intro i2 hi2
        split_ifs with hge
        · have hnb : (n.val : ℤ) ≤ 100000 := by
            have h2 : n.val = sorted.val.length := hn
            omega
          have hjlt : j.val < n.val := by simpa using hlt
          have hadd1 : IScalar.min (.I64) ≤ c.val + (1#i64).val := by scalar_tac
          have hadd2 : c.val + (1#i64).val ≤ IScalar.max (.I64) := by scalar_tac
          apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := c) (y := 1#i64) hadd1 hadd2)
          intro c1 hc1''
          split_ifs with hge2
          · simp only [WP.spec_ok]
          · have hside : j.val + (1#usize).val ≤ UScalar.max (ty := .Usize) := by scalar_tac
            apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := j) (y := 1#usize) hside)
            intro j' hj'
            have hj1 : j'.val = j.val + 1 := by
              have h1 : (1#usize).val = 1 := by simp
              omega
            have hjle : j'.val ≤ n.val := by omega
            have hc11 : 1 ≤ c1.val := by
              have h1 : (1#i64).val = 1 := by simp
              omega
            have hc12 : c1.val ≤ j'.val := by
              have h1 : (1#i64).val = 1 := by simp
              omega
            have hmeas : n.val - j'.val < n.val - j.val := by omega
            simp only [WP.spec_ok]
            exact ⟨⟨hjle, hxval, ⟨hc11, hc12⟩⟩, hmeas⟩
        · have hside : j.val + (1#usize).val ≤ UScalar.max (ty := .Usize) := by scalar_tac
          apply WP.spec_bind (UScalar.add_spec (ty := .Usize) (x := j) (y := 1#usize) hside)
          intro j' hj'
          have hj1 : j'.val = j.val + 1 := by
            have h1 : (1#usize).val = 1 := by simp
            omega
          have hjle : j'.val ≤ n.val := by omega
          have hc2' : c.val ≤ j'.val := by omega
          have hmeas : n.val - j'.val < n.val - j.val := by omega
          simp only [WP.spec_ok]
          exact ⟨⟨hjle, ⟨hl1', hl2'⟩, ⟨hc1', hc2'⟩⟩, hmeas⟩
      · simp only [WP.spec_ok]
    · exact ⟨hi, ⟨hl1, hl2⟩, ⟨hc1, hc2⟩⟩

  /-- The whole gap test never fails. -/
  theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hne : 1 ≤ sorted.val.length) (hb : sorted.val.length < Std.Usize.max)
      (hlen : sorted.val.length ≤ 100000)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make sorted k d ⦃ (_ : Bool) => True ⦄ := by
    simp only [Aegis.MaximumTastiness.can_make]
    split_ifs with hk
    · simp only [WP.spec_ok]
    · have h0 : (0#usize).val < sorted.val.length := by
        have h1 : (0#usize).val = 0 := by simp
        omega
      apply WP.spec_bind (Slice.index_usize_spec sorted 0#usize h0)
      intro last hlast
      have hlvd : 1 ≤ last.val ∧ last.val ≤ 1000000000 := by
        refine hval last ?_
        rw [hlast]
        exact List.getElem_mem h0
      have hile : (1#usize).val ≤ (Slice.len sorted).val := by
        have h1 : (1#usize).val = 1 := by simp
        have h2 : (Slice.len sorted).val = sorted.val.length := by simp
        omega
      exact can_make_loop_spec sorted k d (Slice.len sorted) rfl 1#usize 1#i64 last hile hb hlen hval
        (by simp) (by simp) hlvd.1 hlvd.2

  /-- Monotonicity of a value-sorted list (strictly increasing indices). -/
  theorem SortedV.getElem_le {l : List Std.I64} (h : SortedV l) {i j : ℕ}
      (hi : i < l.length) (hj : j < l.length) (hij : i < j) : l[i].val ≤ l[j].val :=
    (List.pairwise_iff_getElem.mp h i j hi hj hij)

  theorem tdiv2_pos {x : ℤ} (h : 2 ≤ x) : 1 ≤ x.tdiv 2 := by
    have h1 := Int.mul_tdiv_add_tmod x 2
    have h2 := Int.tmod_nonneg (a := x) (2 : ℤ) (by omega)
    have h3 := Int.tmod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
    omega

  theorem tdiv2_lt {x : ℤ} (h : 1 ≤ x) : x.tdiv 2 < x := by
    have h1 := Int.mul_tdiv_add_tmod x 2
    have h2 := Int.tmod_nonneg (a := x) (2 : ℤ) (by omega)
    have h3 := Int.tmod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
    omega

  /-- The binary search loop never fails. -/
  theorem loop1_spec (k : Std.I64) (sorted : alloc.vec.Vec Std.I64) (lo hi : Std.I64)
      (hlo : 0 ≤ lo.val) (hlh : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000000001)
      (hne : 1 ≤ sorted.val.length) (hb : sorted.val.length < Std.Usize.max)
      (hlen : sorted.val.length ≤ 100000)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi ⦃ (_ : Std.I64) => True ⦄ := by
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun p : Std.I64 × Std.I64 => (p.2.val - p.1.val).toNat)
      (inv := fun p => 0 ≤ p.1.val ∧ p.1.val ≤ p.2.val ∧ p.2.val ≤ 1000000001)
      (post := fun (_ : Std.I64) => True)
    · rintro ⟨a, b⟩ ⟨ha1, ha2, ha3⟩
      dsimp only at ha1 ha2 ha3 ⊢
      simp only [Aegis.MaximumTastiness.maximum_tastiness_loop1.body]
      have hadd1 : IScalar.min (.I64) ≤ a.val + (1#i64).val := by scalar_tac
      have hadd2 : a.val + (1#i64).val ≤ IScalar.max (.I64) := by scalar_tac
      apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := a) (y := 1#i64) hadd1 hadd2)
      intro i hieq
      split_ifs with hlt
      · have hltv : a.val + 1 < b.val := by
          have hlt' : i.val < b.val := by simpa using hlt
          have h : i.val = a.val + (1#i64).val := hieq
          have h1 : (1#i64).val = 1 := by simp
          omega
        have hsub1 : IScalar.min (.I64) ≤ b.val - a.val := by scalar_tac
        have hsub2 : b.val - a.val ≤ IScalar.max (.I64) := by scalar_tac
        apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := b) (y := a) hsub1 hsub2)
        intro i1 hi1
        obtain ⟨i2, hi2eq, hi2v⟩ := IScalar.div_spec (ty := .I64) (x := i1) (y := 2#i64)
          (by simp) (by simp [IScalar.min])
        rw [hi2eq]
        simp only [bind_ok]
        have hi1v : i1.val = b.val - a.val := hi1
        have hi2v' : i2.val = (b.val - a.val).tdiv 2 := by
          rw [hi2v, hi1v]
          simp
        have hx2 : 2 ≤ b.val - a.val := by omega
        have hi2pos : 1 ≤ i2.val := by
          rw [hi2v']; exact tdiv2_pos hx2
        have hi2lt : i2.val < b.val - a.val := by
          rw [hi2v']; exact tdiv2_lt (by omega)
        have hmid1 : IScalar.min (.I64) ≤ a.val + i2.val := by scalar_tac
        have hmid2 : a.val + i2.val ≤ IScalar.max (.I64) := by scalar_tac
        apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := a) (y := i2) hmid1 hmid2)
        intro mid hmeq
        have hmidv : mid.val = a.val + i2.val := hmeq
        have hsv : (alloc.vec.Vec.deref sorted).val = sorted.val := by
          simp [alloc.vec.Vec.deref]
        apply WP.spec_bind (can_make_spec (alloc.vec.Vec.deref sorted) k mid
          (by rw [hsv]; exact hne) (by rw [hsv]; exact hb) (by rw [hsv]; exact hlen)
          (by rw [hsv]; exact hval))
        intro bres hbres
        split_ifs with hbres2
        · have hinv : 0 ≤ mid.val ∧ mid.val ≤ b.val ∧ b.val ≤ 1000000001 := by
            refine ⟨by omega, by omega, ha3⟩
          have hmeas : (b.val - mid.val).toNat < (b.val - a.val).toNat := by
            rw [Int.toNat_lt_toNat (by omega : 0 < b.val - a.val)]
            omega
          simp only [WP.spec_ok]
          exact ⟨hinv, hmeas⟩
        · have hinv : 0 ≤ a.val ∧ a.val ≤ mid.val ∧ mid.val ≤ 1000000001 := by
            refine ⟨ha1, by omega, by omega⟩
          have hmeas : (mid.val - a.val).toNat < (b.val - a.val).toNat := by
            rw [Int.toNat_lt_toNat (by omega : 0 < b.val - a.val)]
            omega
          simp only [WP.spec_ok]
          exact ⟨hinv, hmeas⟩
      · simp only [WP.spec_ok]
    · exact ⟨hlo, hlh, hhi⟩

  /-- The tail of `maximum_tastiness` never fails. -/
  theorem tail_spec (n : Std.Usize) (k : Std.I64) (v : alloc.vec.Vec Std.I64)
      (hn : 2 ≤ n.val) (hnv : n.val = v.val.length) (hb : v.val.length < Std.Usize.max)
      (hlen : v.val.length ≤ 100000)
      (hval : ∀ x ∈ v.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      tail n k v ⦃ (_ : Std.I64) => True ⦄ := by
    obtain ⟨sl, hsl, hslperm, hslsorted⟩ := slice_sort_spec v.slice
    have hslval : sl.val.Perm v.val := hslperm
    have hlenv : sl.val.length = n.val := by
      rw [hslval.length_eq, hnv]
    have hb' : sl.val.length < Std.Usize.max := by rw [hlenv, hnv]; exact hb
    have hlen' : sl.val.length ≤ 100000 := by rw [hlenv, hnv]; exact hlen
    have hval' : ∀ x ∈ sl.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 :=
      fun x hx => hval x (hslval.mem_iff.mp hx)
    have hne' : 1 ≤ sl.val.length := by rw [hlenv]; omega
    simp only [tail]
    rw [hsl]
    simp only [bind_ok]
    have hsub : (1#usize).val ≤ n.val := by
      have h1 : (1#usize).val = 1 := by simp
      omega
    apply WP.spec_bind (UScalar.sub_spec (ty := .Usize) (x := n) (y := 1#usize) hsub)
    intro i hi
    have hiv : i.val = n.val - 1 := by
      have h1 : (1#usize).val = 1 := by simp
      have h2 := hi.1
      omega
    have hib : i.val < sl.val.length := by rw [hlenv]; omega
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind
      (alloc.vec.Vec.index_usize_spec (⟨sl⟩ : alloc.vec.Vec Std.I64) i hib)
    intro i1 hi1
    have hi1' : i1 = sl.val[i.val] := hi1
    have h0b : (0#usize).val < sl.val.length := by
      have h1 : (0#usize).val = 0 := by simp
      omega
    apply WP.spec_bind
      (alloc.vec.Vec.index_usize_spec (⟨sl⟩ : alloc.vec.Vec Std.I64) 0#usize h0b)
    intro j hj
    have hj' : j = sl.val[(0#usize).val] := hj
    have hv1 : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
      refine hval' _ ?_
      rw [hi1']
      exact List.getElem_mem hib
    have hv2 : 1 ≤ j.val ∧ j.val ≤ 1000000000 := by
      refine hval' _ ?_
      rw [hj']
      exact List.getElem_mem h0b
    have hsub1 : IScalar.min (.I64) ≤ i1.val - j.val := by scalar_tac
    have hsub2 : i1.val - j.val ≤ IScalar.max (.I64) := by scalar_tac
    apply WP.spec_bind (IScalar.sub_spec (ty := .I64) (x := i1) (y := j) hsub1 hsub2)
    intro m hm
    have hadd1 : IScalar.min (.I64) ≤ m.val + (1#i64).val := by scalar_tac
    have hadd2 : m.val + (1#i64).val ≤ IScalar.max (.I64) := by scalar_tac
    apply WP.spec_bind (IScalar.add_spec (ty := .I64) (x := m) (y := 1#i64) hadd1 hadd2)
    intro hi' hhi'
    have hmv : m.val = i1.val - j.val := hm
    have hhiv : hi'.val = m.val + (1#i64).val := hhi'
    have hival : i.val = sl.val.length - 1 := by rw [← hlenv] at hiv; omega
    have h0v : (0#usize).val = 0 := by simp
    have hisorted : sl.val[(0#usize).val].val ≤ sl.val[i.val].val :=
      SortedV.getElem_le hslsorted h0b hib (by omega)
    have hji : j.val ≤ i1.val := by
      rw [hj', hi1']
      exact hisorted
    have hpos : 0 ≤ m.val := by rw [hmv]; omega
    have hle : hi'.val ≤ 1000000001 := by
      have h1 : (1#i64).val = 1 := by simp
      omega
    refine loop1_spec k ⟨sl⟩ 0#i64 hi' ?_ ?_ hle hne' hb' hlen' hval'
    · show (0 : ℤ) ≤ (0#i64).val
      simp
    · rw [hhiv]
      have h1 : (1#i64).val = 1 := by simp
      have h0 : (0#i64).val = 0 := by simp
      omega

  /-- The value map on lists of integers. -/
  abbrev valL (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  theorem valL_def (l : List Std.I64) : valL l = l.map (fun x => x.val) := rfl

  /-- The value map is injective on lists. -/
  theorem map_val_inj : Function.Injective valL :=
    List.map_injective_iff.mpr (fun a b h => IScalar.eq_of_val_eq h)

  /-- `sortList` only depends on the multiset of the *values* of its argument. -/
  theorem sortList_eq_of_map_perm {l₁ l₂ : List Std.I64}
      (hp : (valL l₁).Perm (valL l₂)) :
      AegisShim.sortList cmpI l₁ = AegisShim.sortList cmpI l₂ := by
    obtain ⟨r₁, hr₁⟩ := sortList_ok l₁
    obtain ⟨r₂, hr₂⟩ := sortList_ok l₂
    rw [hr₁, hr₂]
    have hs₁ : (valL r₁).Pairwise (· ≤ ·) :=
      List.pairwise_map.mpr (sortList_sorted l₁ r₁ hr₁)
    have hs₂ : (valL r₂).Pairwise (· ≤ ·) :=
      List.pairwise_map.mpr (sortList_sorted l₂ r₂ hr₂)
    have hp' : (valL r₁).Perm (valL r₂) :=
      ((sortList_perm l₁ r₁ hr₁).map (fun x => x.val)).trans
        (hp.trans ((sortList_perm l₂ r₂ hr₂).map (fun x => x.val)).symm)
    have heq : valL r₁ = valL r₂ := List.Perm.eq_of_pairwise' hs₁ hs₂ hp'
    rw [map_val_inj heq]

  /-- `Slice.sort` only depends on the multiset of the values of its input. -/
  theorem slice_sort_eq_of_map_perm {s₁ s₂ : Slice Std.I64} (h : (valL s₁.val).Perm (valL s₂.val)) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s₁ = alloc.slice.Slice.sort core.cmp.OrdI64 s₂ := by
    have h' := sortList_eq_of_map_perm h
    simp only [alloc.slice.Slice.sort]
    rw [h']

  /-- The tail only depends on the multiset of the values of the array contents. -/
  theorem tail_congr_map {n : Std.Usize} {k : Std.I64} {v v' : alloc.vec.Vec Std.I64}
      (h : (valL v.val).Perm (valL v'.val)) : tail n k v = tail n k v' := by
    have hs : alloc.slice.Slice.sort core.cmp.OrdI64 v.slice
        = alloc.slice.Slice.sort core.cmp.OrdI64 v'.slice := slice_sort_eq_of_map_perm h
    simp only [tail]
    rw [hs]

  /-- `maximum_tastiness` only depends on the multiset of the array contents. -/
  theorem maximum_tastiness_perm_map {s s' : Slice Std.I64} {k : Std.I64}
      (h : (valL s.val).Perm (valL s'.val)) (hne : s.val.length ≠ 0)
      (hb : s.val.length < Std.Usize.max) :
      maximum_tastiness s k = maximum_tastiness s' k := by
    have hlen : s.val.length = s'.val.length := by
      simpa using h.length_eq
    have hne' : s'.val.length ≠ 0 := by rw [← hlen]; exact hne
    have hb' : s'.val.length < Std.Usize.max := by rw [← hlen]; exact hb
    obtain ⟨v, hv, hvv⟩ := spec_exists_ok (loop0_spec_start s hb)
    obtain ⟨v', hv', hvv'⟩ := spec_exists_ok (loop0_spec_start s' hb')
    have hlenU : Slice.len s = Slice.len s' := by
      apply UScalar.eq_of_val_eq
      simp [hlen]
    rw [maximum_tastiness_unfold s k hne, maximum_tastiness_unfold s' k hne']
    rw [hv, hv']
    simp only [bind_ok]
    rw [hlenU]
    exact tail_congr_map (by rw [hvv, hvv']; exact h)

  /-- `maximum_tastiness` never fails under the preconditions of the specification. -/
  theorem maximum_tastiness_exists (s : Slice Std.I64) (k : Std.I64)
      (hn : 2 ≤ s.val.length) (hb : s.val.length < Std.Usize.max)
      (hlen : s.val.length ≤ 100000)
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness s k = ok r := by
    have hne : s.val.length ≠ 0 := by omega
    obtain ⟨v, hv, hvv⟩ := spec_exists_ok (loop0_spec_start s hb)
    have htail : tail (Slice.len s) k v ⦃ (_ : Std.I64) => True ⦄ := by
      refine tail_spec (Slice.len s) k v ?_ ?_ ?_ ?_ ?_
      · rw [Slice.len_val]; omega
      · rw [Slice.len_val, hvv]
      · rw [hvv]; exact hb
      · rw [hvv]; exact hlen
      · intro x hx
        exact hval x (by rw [hvv] at hx; exact hx)
    obtain ⟨r, hr, -⟩ := spec_exists_ok htail
    refine ⟨r, ?_⟩
    rw [maximum_tastiness_unfold s k hne, hv]
    simp only [bind_ok]
    exact hr

  end Aux

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
  theorem spec_13 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, (vals q).Perm (vals price) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    have h2P : price.val.length ≤ Std.Usize.max := price.property
    have h3P : price.val.length ≤ 100000 := h_len
    have h4P : 2 ≤ price.val.length := h_n
    have hmaxP : 100000 < Std.Usize.max := by scalar_tac
    have hbP : price.val.length < Std.Usize.max := by omega
    have hneP : price.val.length ≠ 0 := by omega
    obtain ⟨r, hr⟩ := Aux.maximum_tastiness_exists price k h_n hbP h_len h_price
    refine ⟨r, hr, ?_⟩
    intro q hq
    have hqlen : q.val.length = price.val.length := by
      have h1 := hq.length_eq
      simpa [vals, Aux.valL] using h1
    have hbQ : q.val.length < Std.Usize.max := by rw [hqlen]; exact hbP
    have hlenQ : q.val.length ≤ 100000 := by rw [hqlen]; exact h_len
    have hvalQ : ∀ x ∈ q.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      have hx1 : x.val ∈ vals q := List.mem_map_of_mem hx
      have hx2 : x.val ∈ vals price := hq.mem_iff.mp hx1
      obtain ⟨y, hy, hyv⟩ := List.mem_map.mp hx2
      have hxy : x = y := IScalar.eq_of_val_eq hyv.symm
      rw [hxy]
      exact h_price y hy
    obtain ⟨r', hr'⟩ := Aux.maximum_tastiness_exists q k (by rw [hqlen]; exact h_n) hbQ hlenQ hvalQ
    refine ⟨r', hr', ?_⟩
    have heq : maximum_tastiness price k = maximum_tastiness q k :=
      Aux.maximum_tastiness_perm_map hq.symm hneP hbP
    rw [hr, hr'] at heq
    have hrr : r = r' := by simpa using heq
    rw [hrr]

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
