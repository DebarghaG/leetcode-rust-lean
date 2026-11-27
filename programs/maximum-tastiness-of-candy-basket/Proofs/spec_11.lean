import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_11` (maximum-tastiness-of-candy-basket).
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

  /-! ### The greedy scan, abstractly

  The extracted `can_make` walks over the sorted array and counts how many elements it can
  pick so that consecutive picks are at least `d` apart.  We model this scan on `List ℤ`. -/

  /-- `IsChain d last l`: the elements of `l` are a valid chain starting from `last`, i.e. each
  element is at least `d` above its predecessor. -/
  def IsChain (d last : ℤ) : List ℤ → Prop
    | [] => True
    | y :: ys => d ≤ y - last ∧ IsChain d y ys

  /-- The elements accepted by the greedy scan of `l` when the previously accepted value is
  `last`, in acceptance order. -/
  def gacc (d : ℤ) : List ℤ → ℤ → List ℤ
    | [], _ => []
    | x :: xs, last => if d ≤ x - last then x :: gacc d xs x else gacc d xs last

  /-- The number of elements accepted by the greedy scan. -/
  def gcount (d : ℤ) (l : List ℤ) (last : ℤ) : ℕ := (gacc d l last).length

  theorem gacc_sublist (d : ℤ) (l : List ℤ) (last : ℤ) : (gacc d l last).Sublist l := by
    induction l generalizing last with
    | nil => simp [gacc]
    | cons x xs ih =>
      by_cases h : d ≤ x - last
      · rw [gacc, if_pos h]; exact List.Sublist.cons_cons _ (ih x)
      · rw [gacc, if_neg h]; exact List.Sublist.cons _ (ih last)

  theorem gacc_isChain (d : ℤ) (l : List ℤ) (last : ℤ) : IsChain d last (gacc d l last) := by
    induction l generalizing last with
    | nil => simp [gacc, IsChain]
    | cons x xs ih =>
      by_cases h : d ≤ x - last
      · rw [gacc, if_pos h]; exact ⟨h, ih x⟩
      · rw [gacc, if_neg h]; exact ih last

  theorem isChain_gt {d last : ℤ} {l : List ℤ} (hd : 1 ≤ d) (h : IsChain d last l) :
      ∀ z ∈ l, last < z := by
    induction l generalizing last with
    | nil => simp
    | cons y ys ih =>
      intro z hz
      rw [IsChain] at h
      obtain ⟨h1, h2⟩ := h
      rcases List.mem_cons.1 hz with rfl | hz
      · omega
      · have := ih h2 z hz; omega

  theorem gacc_nodup {d : ℤ} (hd : 1 ≤ d) (l : List ℤ) (last : ℤ) :
      (gacc d l last).Nodup := by
    induction l generalizing last with
    | nil => simp [gacc]
    | cons x xs ih =>
      by_cases h : d ≤ x - last
      · rw [gacc, if_pos h, List.nodup_cons]
        refine ⟨?_, ih x⟩
        intro hmem
        have := isChain_gt hd (gacc_isChain d xs x) x hmem
        omega
      · rw [gacc, if_neg h]; exact ih last

  theorem gcount_le_length (d : ℤ) (l : List ℤ) (last : ℤ) : gcount d l last ≤ l.length :=
    (gacc_sublist d l last).length_le

  /-- With threshold `1`, the greedy scan only accepts pairwise distinct values, hence accepts at
  most one element per distinct value of the list. -/
  theorem gcount_le_dedup {d : ℤ} (hd : 1 ≤ d) (l : List ℤ) (last : ℤ) :
      gcount d l last ≤ l.dedup.length := by
    have hnd := gacc_nodup hd l last
    have hsub : (gacc d l last).toFinset ⊆ l.toFinset := by
      intro a ha
      rw [List.mem_toFinset] at *
      exact (gacc_sublist d l last).subset ha
    have h1 : (gacc d l last).toFinset.card ≤ l.toFinset.card := Finset.card_le_card hsub
    rw [List.card_toFinset, List.card_toFinset, hnd.dedup] at h1
    simpa [gcount] using h1

  theorem gcount_pos {d : ℤ} {l : List ℤ} {last : ℤ} (h : 1 ≤ gcount d l last) :
      ∃ y ∈ l, d ≤ y - last := by
    induction l generalizing last with
    | nil => simp [gcount, gacc] at h
    | cons x xs ih =>
      by_cases hc : d ≤ x - last
      · exact ⟨x, by simp, hc⟩
      · have h' : 1 ≤ gcount d xs last := by
          simpa [gcount, gacc, hc] using h
        obtain ⟨y, hy, hd⟩ := ih h'
        exact ⟨y, by simp [hy], hd⟩

  /-- Starting the scan lower gives at least as many accepted elements.  Both this bound and the
  upper bound `gcount d l L ≤ gcount d l a + 1` are proved simultaneously on sorted lists. -/
  theorem gcount_aux (d : ℤ) : ∀ (l : List ℤ) (L a : ℤ), l.Pairwise (· ≤ ·) →
      (∀ x ∈ l, a ≤ x) → L ≤ a →
      gcount d l L ≤ gcount d l a + 1 ∧ gcount d l a ≤ gcount d l L := by
    intro l
    induction l with
    | nil => intro L a _ _ _; simp [gcount, gacc]
    | cons x xs ih =>
      intro L a hs ha hLa
      rw [List.pairwise_cons] at hs
      obtain ⟨hhead, htail⟩ := hs
      have hax : a ≤ x := ha x (by simp)
      have ha' : ∀ y ∈ xs, x ≤ y := hhead
      by_cases hac : d ≤ x - a
      · have hLc : d ≤ x - L := by omega
        have e1 : gcount d (x :: xs) L = gcount d xs x + 1 := by
          simp [gcount, gacc, hLc]
        have e2 : gcount d (x :: xs) a = gcount d xs x + 1 := by
          simp [gcount, gacc, hac]
        rw [e1, e2]
        exact ⟨Nat.le_add_right _ _, le_rfl⟩
      · by_cases hLc : d ≤ x - L
        · -- `L` accepts the head while `a` does not
          have e1 : gcount d (x :: xs) L = gcount d xs x + 1 := by
            simp [gcount, gacc, hLc]
          have e2 : gcount d (x :: xs) a = gcount d xs a := by simp [gcount, gacc, hac]
          rw [e1, e2]
          exact ⟨by have := (ih a x htail ha' hax).2; omega, (ih a x htail ha' hax).1⟩
        · have e1 : gcount d (x :: xs) L = gcount d xs L := by simp [gcount, gacc, hLc]
          have e2 : gcount d (x :: xs) a = gcount d xs a := by simp [gcount, gacc, hac]
          rw [e1, e2]
          exact ih L a htail (fun y hy => le_trans hax (ha' y hy)) hLa

  /-- The greedy scan accepts fewer elements when the required gap grows. -/
  theorem gcount_mono_d (d d' : ℤ) (hdd : d' ≤ d) (l : List ℤ) (last : ℤ)
      (hs : l.Pairwise (· ≤ ·)) (hl : ∀ x ∈ l, last ≤ x) :
      gcount d l last ≤ gcount d' l last := by
    induction l generalizing last with
    | nil => simp [gcount, gacc]
    | cons x xs ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hhead, htail⟩ := hs
      have hlx : last ≤ x := hl x (by simp)
      have hl' : ∀ y ∈ xs, last ≤ y := fun y hy => hl y (by simp [hy])
      by_cases h1 : d ≤ x - last
      · have h2 : d' ≤ x - last := le_trans hdd h1
        have e1 : gcount d (x :: xs) last = gcount d xs x + 1 := by simp [gcount, gacc, h1]
        have e2 : gcount d' (x :: xs) last = gcount d' xs x + 1 := by simp [gcount, gacc, h2]
        rw [e1, e2]
        exact Nat.add_le_add_right (ih x htail hhead) 1
      · by_cases h2 : d' ≤ x - last
        · have e1 : gcount d (x :: xs) last = gcount d xs last := by simp [gcount, gacc, h1]
          have e2 : gcount d' (x :: xs) last = gcount d' xs x + 1 := by simp [gcount, gacc, h2]
          rw [e1, e2]
          have ih1 : gcount d xs last ≤ gcount d' xs last := ih last htail hl'
          have aux := (gcount_aux d' xs last x htail hhead hlx).1
          omega
        · have e1 : gcount d (x :: xs) last = gcount d xs last := by simp [gcount, gacc, h1]
          have e2 : gcount d' (x :: xs) last = gcount d' xs last := by simp [gcount, gacc, h2]
          rw [e1, e2]
          exact ih last htail hl'

  /-- With threshold `0` every element is accepted. -/
  theorem gcount_zero (l : List ℤ) (last : ℤ) (hs : l.Pairwise (· ≤ ·))
      (hl : ∀ x ∈ l, last ≤ x) : gcount 0 l last = l.length := by
    induction l generalizing last with
    | nil => simp [gcount, gacc]
    | cons x xs ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hhead, htail⟩ := hs
      have hl' : ∀ y ∈ xs, last ≤ y := fun y hy => hl y (by simp [hy])
      have hc : 0 ≤ x - last := by have := hl x (by simp); omega
      have e : gcount 0 (x :: xs) last = gcount 0 xs x + 1 := by
        show (gacc 0 (x :: xs) last).length = (gacc 0 xs x).length + 1
        rw [gacc, if_pos hc, List.length_cons]
      rw [e]
      simp [ih x htail hhead]

  /-- With threshold `1` on a sorted list, the greedy scan starting at the head collects exactly
  one element per distinct value. -/
  theorem gcount_one_head (x : ℤ) (xs : List ℤ) (hs : (x :: xs).Pairwise (· ≤ ·)) :
      gcount 1 xs x + 1 = (x :: xs).dedup.length := by
    induction xs generalizing x with
    | nil => simp [gcount, gacc]
    | cons y ys ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hhead, htail⟩ := hs
      have hxy : x ≤ y := hhead y (by simp)
      have hhead' : ∀ z ∈ ys, y ≤ z := (List.pairwise_cons.1 htail).1
      by_cases h : 1 ≤ y - x
      · have e : gcount 1 (y :: ys) x = gcount 1 ys y + 1 := by simp [gcount, gacc, h]
        have hnot : x ∉ (y :: ys).dedup := by
          rw [List.mem_dedup]
          intro hmem
          rcases List.mem_cons.1 hmem with h' | h'
          · omega
          · have := hhead' x h'; omega
        rw [e, List.dedup_cons_of_notMem' hnot, List.length_cons, ih y htail]
      · have hyx : y ≤ x := by omega
        have hyx' : y = x := le_antisymm hyx hxy
        subst hyx'
        have hc : ¬ (1 ≤ y - y) := by omega
        have e : gcount 1 (y :: ys) y = gcount 1 ys y := by
          simp only [gcount, gacc, if_neg hc]
        rw [e, List.dedup_cons_of_mem (List.mem_cons_self ..), ih y htail]

  /-! ### Relating the extracted code to the abstract scan -/

  open Aegis.MaximumTastiness

  /-! ### Insertion sort (`sortInsert` / `sortList`) -/

  theorem OrdI64.cmp_eq (x y : Std.I64) :
      core.cmp.OrdI64.cmp x y = ok (compare x.val y.val) :=
    rfl

  /-- `sortInsert` inserts into a sorted list, producing a sorted permutation. -/
  theorem sortInsert_spec (cmp : Std.I64 → Std.I64 → Result Ordering)
      (hcmp : ∀ x y, cmp x y = ok (compare x.val y.val))
      (x : Std.I64) (l : List Std.I64) (hs : l.Pairwise (fun a b => a.val ≤ b.val)) :
      ∃ r, AegisShim.sortInsert cmp x l = ok r ∧
        r.Perm (x :: l) ∧ r.Pairwise (fun a b => a.val ≤ b.val) := by
    induction l with
    | nil =>
      exact ⟨[x], by simp [AegisShim.sortInsert], by simp, by simp⟩
    | cons y ys ih =>
      obtain ⟨hyys, htail⟩ := List.pairwise_cons.1 hs
      obtain ⟨r, hr, hperm, hsorted⟩ := ih htail
      by_cases hc : compare x.val y.val = Ordering.gt
      · have hlt : y.val < x.val := compare_gt_iff_gt.1 hc
        refine ⟨y :: r, ?_, ?_, ?_⟩
        · simp [AegisShim.sortInsert, hcmp, hc, hr]
        · exact (List.Perm.cons y hperm).trans (List.Perm.swap x y ys)
        · refine List.pairwise_cons.2 ⟨?_, hsorted⟩
          intro z hz
          have hz' : z ∈ x :: ys := hperm.subset hz
          rcases List.mem_cons.1 hz' with rfl | hz''
          · omega
          · have := hyys z hz''; omega
      · have hle : x.val ≤ y.val := by
          have := compare_le_iff_le.1 hc
          simpa using this
        refine ⟨x :: y :: ys, ?_, ?_, ?_⟩
        · simp [AegisShim.sortInsert, hcmp, hc]
        · exact List.Perm.refl _
        · have hx : ∀ a ∈ y :: ys, x.val ≤ a.val := by
            intro a ha
            rcases List.mem_cons.1 ha with rfl | ha
            · exact hle
            · have := hyys a ha; omega
          exact List.pairwise_cons.2 ⟨hx, List.pairwise_cons.2 ⟨hyys, htail⟩⟩

  /-- `sortList` sorts a list, up to permutation. -/
  theorem sortList_spec (cmp : Std.I64 → Std.I64 → Result Ordering)
      (hcmp : ∀ x y, cmp x y = ok (compare x.val y.val)) (l : List Std.I64) :
      ∃ r, AegisShim.sortList cmp l = ok r ∧
        r.Perm l ∧ r.Pairwise (fun a b => a.val ≤ b.val) := by
    induction l with
    | nil => exact ⟨[], by simp [AegisShim.sortList], by simp, by simp⟩
    | cons x xs ih =>
      obtain ⟨r, hr, hperm, hsorted⟩ := ih
      obtain ⟨r', hr', hperm', hsorted'⟩ := sortInsert_spec cmp hcmp x r hsorted
      refine ⟨r', ?_, hperm'.trans (List.Perm.cons x hperm), hsorted'⟩
      simp [AegisShim.sortList, hr, hr']

  /-- The sort used by the program: it succeeds and yields a sorted permutation of the values. -/
  theorem Slice.sort_spec (s : Slice Std.I64) :
      ∃ s', alloc.slice.Slice.sort core.cmp.OrdI64 s = ok s' ∧
        (s'.val.map (fun x => x.val)).Perm (s.val.map (fun x => x.val)) ∧
        (s'.val.map (fun x => x.val)).Pairwise (· ≤ ·) := by
    obtain ⟨r, hr, hperm, hsorted⟩ :=
      sortList_spec core.cmp.OrdI64.cmp (fun x y => OrdI64.cmp_eq x y) s.val
    have hlen : r.length ≤ Usize.max := by
      rw [hperm.length_eq]; exact s.property
    refine ⟨Slice.from r hlen, ?_, ?_, ?_⟩
    · simp [alloc.slice.Slice.sort, hr, hlen]
    · simpa using hperm.map (fun x : Std.I64 => x.val)
    · simpa [List.pairwise_map] using hsorted

  /-- A program which satisfies a specification returns a value satisfying it. -/
  theorem spec_eq_ok {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
      ∃ r, m = ok r ∧ p r := by
    revert h
    refine Result.cases m ?_ ?_ ?_
    · intro r hr; exact ⟨r, rfl, by simpa using hr⟩
    · intro i k hr; rw [WP.spec_vis] at hr; exact hr.elim
    · intro hr; rw [WP.spec_div] at hr; exact hr.elim

  /-- The copy loop: starting from a vector holding the first `i` prices, it ends with a vector
  holding all prices. -/
  theorem loop0_spec (price : Slice Std.I64) (n : Usize) (vec : alloc.vec.Vec Std.I64)
      (i : Usize) (hn : n.val = price.length) (hi : i.val ≤ n.val)
      (hv : vec.val = price.val.take i.val) :
      ∃ v, maximum_tastiness_loop0 price n vec i = ok v ∧
        v.val = price.val.take n.val := by
    have hbound : n.val ≤ Usize.max := by rw [hn]; exact price.property
    have hmain : maximum_tastiness_loop0 price n vec i ⦃ v =>
        v.val = price.val.take n.val ⦄ := by
      unfold maximum_tastiness_loop0
      apply loop.spec_decr_nat
        (fun s : alloc.vec.Vec Std.I64 × Usize => n.val - s.2.val)
        (fun s : alloc.vec.Vec Std.I64 × Usize =>
          s.2.val ≤ n.val ∧ s.1.val = price.val.take s.2.val)
        (fun v : alloc.vec.Vec Std.I64 => v.val = price.val.take n.val)
      · rintro ⟨vec, i⟩ ⟨hi, hv⟩
        dsimp only at hi hv ⊢
        unfold maximum_tastiness_loop0.body
        by_cases hcase : i < n
        · rw [if_pos hcase]
          have hival : i.val < n.val := by simpa using hcase
          have hn' : n.val = price.val.length := hn
          have hib : i.val < price.val.length := by omega
          apply WP.spec_bind (Slice.index_usize_spec price i hib)
          intro i1 hi1
          have hlen : vec.val.length < Usize.max := by
            rw [hv, List.length_take]
            have h1 : min i.val price.val.length ≤ i.val := Nat.min_le_left _ _
            omega
          apply WP.spec_bind (alloc.vec.Vec.push_spec vec i1 hlen)
          intro sorted1 hs1
          have hiadd : i.val + 1 ≤ Usize.max := by omega
          apply WP.spec_bind (Usize.add_spec hiadd)
          intro i2 hi2
          simp only [WP.spec_ok]
          have hi2v : i2.val = i.val + 1 := by simpa using hi2
          have htake : price.val.take (i.val + 1) = price.val.take i.val ++ [price.val[i.val]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hib]
            rfl
          have hs : sorted1.val = price.val.take i2.val := by
            rw [hs1, hi1, hv, hi2v, htake]
          refine ⟨⟨?_, hs⟩, ?_⟩
          · omega
          · omega
        · rw [if_neg hcase]
          simp only [WP.spec_ok]
          have hival : ¬ (i.val < n.val) := by simpa using hcase
          have hieq : i.val = n.val := by omega
          rw [hv, UScalar.eq_of_val_eq hieq]
      · exact ⟨hi, hv⟩
    obtain ⟨v, hv, hpost⟩ := spec_eq_ok hmain
    exact ⟨v, hv, hpost⟩

  /-- Cons step of the greedy count. -/
  theorem gcount_cons (d : ℤ) (x : ℤ) (t : List ℤ) (last : ℤ) :
      gcount d (x :: t) last
        = if d ≤ x - last then gcount d t x + 1 else gcount d t last := by
    by_cases h : d ≤ x - last <;> simp [gcount, gacc, h]

  theorem gcount_nil (d : ℤ) (last : ℤ) : gcount d [] last = 0 := rfl

  /-- One step of the greedy count at position `j` of `S`. -/
  theorem gcount_drop_cons (d : ℤ) (S : List ℤ) (j : ℕ) (last x : ℤ)
      (hj : j < S.length) (hx : S[j] = x) :
      ((gcount d (S.drop j) last : ℕ) : ℤ)
        = if d ≤ x - last then ((gcount d (S.drop (j + 1)) x : ℕ) : ℤ) + 1
          else ((gcount d (S.drop (j + 1)) last : ℕ) : ℤ) := by
    rw [List.drop_eq_getElem_cons hj, hx, gcount_cons]
    split <;> simp

  /-- Semantics of the `can_make` loop: it decides whether the greedy scan can pick `k`
  elements with gaps at least `d`. -/
  theorem I64.sub_bnd {a b : Std.I64} (h1 : 1 ≤ a.val) (h2 : a.val ≤ 1000000000)
      (h3 : 1 ≤ b.val) (h4 : b.val ≤ 1000000000) :
      Std.I64.min ≤ a.val - b.val ∧ a.val - b.val ≤ Std.I64.max :=
    ⟨by scalar_tac, by scalar_tac⟩

  theorem I64.add_one_bnd {a : Std.I64} (h1 : 1 ≤ a.val) (h2 : a.val ≤ 100000) :
      Std.I64.min ≤ a.val + 1 ∧ a.val + 1 ≤ Std.I64.max :=
    ⟨by scalar_tac, by scalar_tac⟩

  theorem can_make_loop_spec (sorted : Slice Std.I64) (S : List ℤ) (k d : Std.I64)
      (n : Usize) (count last : Std.I64) (i : Usize)
      (hS : S = sorted.val.map (fun x => x.val)) (hn : n.val = S.length)
      (hi : i.val ≤ n.val) (hN : n.val ≤ 100000)
      (hc1 : 1 ≤ count.val) (hc2 : count.val ≤ i.val)
      (hl1 : 1 ≤ last.val) (hl2 : last.val ≤ 1000000000)
      (hb : ∀ y ∈ S, 1 ≤ y ∧ y ≤ 1000000000) :
      ∃ b, can_make_loop sorted k d n count last i = ok b ∧
        (b = true ↔ k.val ≤ count.val + ((gcount d.val (S.drop i.val) last.val : ℕ) : ℤ)) := by
    have hSlen : sorted.val.length = S.length := by rw [hS, List.length_map]
    have hUmax : S.length ≤ Usize.max := by
      rw [← hSlen]; exact sorted.property
    set A : Prop := k.val ≤ count.val + ((gcount d.val (S.drop i.val) last.val : ℕ) : ℤ)
      with hAdef
    have hmain : can_make_loop sorted k d n count last i ⦃ b => (b = true ↔ A) ⦄ := by
      unfold can_make_loop
      apply loop.spec_decr_nat
        (fun s : Std.I64 × Std.I64 × Usize => n.val - s.2.2.val)
        (fun s : Std.I64 × Std.I64 × Usize =>
          s.2.2.val ≤ n.val ∧ 1 ≤ s.1.val ∧ s.1.val ≤ s.2.2.val ∧
          1 ≤ s.2.1.val ∧ s.2.1.val ≤ 1000000000 ∧
          (k.val ≤ s.1.val + ((gcount d.val (S.drop s.2.2.val) s.2.1.val : ℕ) : ℤ) ↔ A))
        (fun b : Bool => (b = true ↔ A))
      · rintro ⟨count, last, i⟩ ⟨hi, hc1, hc2, hl1, hl2, hA⟩
        dsimp only at hi hc1 hc2 hl1 hl2 hA ⊢
        unfold can_make_loop.body
        by_cases hcase : i < n
        · rw [if_pos hcase]
          have hival : i.val < n.val := by simpa using hcase
          have hSlen' : i.val < S.length := by omega
          have hib : i.val < sorted.val.length := by omega
          apply WP.spec_bind (Slice.index_usize_spec sorted i hib)
          intro i1 hi1
          have hxi : S[i.val] = i1.val := by
            simp only [hS, List.getElem_map, hi1]
          have hmem : i1.val ∈ S := by
            rw [← hxi]; exact List.getElem_mem hSlen'
          obtain ⟨hb1, hb2⟩ := hb _ hmem
          obtain ⟨hsub1, hsub2⟩ := I64.sub_bnd hb1 hb2 hl1 hl2
          apply WP.spec_bind (I64.sub_spec hsub1 hsub2)
          intro i2 hi2
          have hi2v : i2.val = i1.val - last.val := hi2
          have hii : i.val + 1 ≤ Usize.max := by omega
          by_cases hcmp : i2 >= d
          · rw [if_pos hcmp]
            have hcmp' : d.val ≤ i1.val - last.val := by rw [← hi2v]; exact hcmp
            obtain ⟨hadd1, hadd2⟩ := I64.add_one_bnd hc1 (by omega)
            apply WP.spec_bind (I64.add_spec hadd1 hadd2)
            intro count1 hcount1
            have hcount1v : count1.val = count.val + 1 := hcount1
            have hkey := gcount_drop_cons d.val S i.val last.val i1.val hSlen' hxi
            rw [if_pos hcmp'] at hkey
            by_cases hck : count1 >= k
            · rw [if_pos hck]
              simp only [WP.spec_ok]
              have hck' : k.val ≤ count1.val := hck
              simp only [true_iff]
              refine hA.mp ?_
              rw [hkey]
              omega
            · rw [if_neg hck]
              apply WP.spec_bind (Usize.add_spec hii)
              intro i3 hi3
              simp only [WP.spec_ok]
              have hi3v : i3.val = i.val + 1 := hi3
              have hlast :
                  (k.val ≤ count1.val + ((gcount d.val (S.drop i3.val) i1.val : ℕ) : ℤ)) ↔ A := by
                rw [← hA, hcount1v, hi3v, hkey]
                constructor <;> intro h <;> omega
              exact ⟨⟨by omega, by omega, by omega, hb1, hb2, hlast⟩, by omega⟩
          · rw [if_neg hcmp]
            have hcmp' : ¬ (d.val ≤ i1.val - last.val) := by rw [← hi2v]; exact hcmp
            have hkey := gcount_drop_cons d.val S i.val last.val i1.val hSlen' hxi
            rw [if_neg hcmp'] at hkey
            apply WP.spec_bind (Usize.add_spec hii)
            intro i3 hi3
            simp only [WP.spec_ok]
            have hi3v : i3.val = i.val + 1 := hi3
            have hlast :
                (k.val ≤ count.val + ((gcount d.val (S.drop i3.val) last.val : ℕ) : ℤ)) ↔ A := by
              rw [← hA, hi3v, hkey]
            have h1 : i3.val ≤ n.val := by omega
            have h3 : count.val ≤ i3.val := by omega
            have h4 : n.val - i3.val < n.val - i.val := by omega
            exact ⟨⟨h1, hc1, h3, hl1, hl2, hlast⟩, h4⟩
        · rw [if_neg hcase]
          simp only [WP.spec_ok]
          have hival : ¬ (i.val < n.val) := by simpa using hcase
          have hieq : i.val = n.val := by omega
          have hdrop0 : S.drop i.val = [] := by
            rw [hieq, hn]
            exact List.drop_length
          rw [decide_eq_true_eq]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · refine hA.mp ?_
            rw [hdrop0, gcount_nil]
            simpa using h
          · rw [← hA] at h
            rw [hdrop0, gcount_nil] at h
            simpa using h
      · exact ⟨hi, hc1, hc2, hl1, hl2, by simp only [hAdef]⟩
    obtain ⟨b, hb_eq, hpost⟩ := spec_eq_ok hmain
    exact ⟨b, hb_eq, hpost⟩

  /-- The `Triple` form of `can_make_loop_spec`. -/
  theorem can_make_loop_triple (sorted : Slice Std.I64) (S : List ℤ) (k d : Std.I64)
      (n : Usize) (count last : Std.I64) (i : Usize)
      (hS : S = sorted.val.map (fun x => x.val)) (hn : n.val = S.length)
      (hi : i.val ≤ n.val) (hN : n.val ≤ 100000)
      (hc1 : 1 ≤ count.val) (hc2 : count.val ≤ i.val)
      (hl1 : 1 ≤ last.val) (hl2 : last.val ≤ 1000000000)
      (hb : ∀ y ∈ S, 1 ≤ y ∧ y ≤ 1000000000) :
      can_make_loop sorted k d n count last i ⦃ b =>
        (b = true ↔ k.val ≤ count.val + ((gcount d.val (S.drop i.val) last.val : ℕ) : ℤ)) ⦄ := by
    obtain ⟨b, hb', hp⟩ :=
      can_make_loop_spec sorted S k d n count last i hS hn hi hN hc1 hc2 hl1 hl2 hb
    rw [hb']
    exact (WP.spec_ok b).2 hp

  /-- Semantics of `can_make`. -/
  theorem getElem_zero_val {l : List Std.I64} {x : ℤ} {xs : List ℤ}
      (h : l.map (fun y => y.val) = x :: xs) (h0 : 0 < l.length) :
      (l[0]'h0).val = x := by
    cases l with
    | nil => simp at h0
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hyx, -⟩ := h
      rw [List.getElem_cons_zero, hyx]

  theorem can_make_spec (sorted : Slice Std.I64) (x : ℤ) (xs : List ℤ) (k d : Std.I64)
      (hS : sorted.val.map (fun y => y.val) = x :: xs)
      (hN : (x :: xs).length ≤ 100000)
      (hb : ∀ y ∈ x :: xs, 1 ≤ y ∧ y ≤ 1000000000) :
      ∃ b, can_make sorted k d = ok b ∧
        (b = true ↔ k.val ≤ 1 + ((gcount d.val xs x : ℕ) : ℤ)) := by
    have hSlen : sorted.val.length = (x :: xs).length := by
      rw [← List.length_map]; exact congrArg List.length hS
    have hne : sorted.val ≠ [] := by
      rintro h
      rw [h] at hS
      simp at hS
    have hgoal : can_make sorted k d ⦃ b =>
        (b = true ↔ k.val ≤ 1 + ((gcount d.val xs x : ℕ) : ℤ)) ⦄ := by
      unfold can_make
      dsimp only
      by_cases hk : k <= 1#i64
      · rw [if_pos hk]
        simp only [WP.spec_ok]
        have hk' : k.val ≤ 1 := hk
        constructor
        · intro _
          have hnn : (0:ℤ) ≤ ((gcount d.val xs x : ℕ) : ℤ) := Nat.cast_nonneg _
          omega
        · intro _; trivial
      · rw [if_neg hk]
        obtain ⟨y, ys, hlm⟩ : ∃ y ys, sorted.val = y :: ys := by
          cases hl : sorted.val with
          | nil => exact absurd hl hne
          | cons y ys => exact ⟨y, ys, rfl⟩
        have hinj : (y :: ys).map (fun z => z.val) = x :: xs := by rw [← hlm]; exact hS
        simp only [List.map_cons, List.cons.injEq] at hinj
        obtain ⟨hyx, hys⟩ := hinj
        have hy : 1 ≤ y.val ∧ y.val ≤ 1000000000 := by
          have := hb x (by rw [← hyx]; exact List.mem_cons_self ..)
          exact ⟨by omega, by omega⟩
        have hpos : 0 < sorted.val.length := List.length_pos_of_ne_nil hne
        have hi0 : (0#usize).val < sorted.val.length := by simpa using hpos
        obtain ⟨hx1, hx2⟩ := hb x (List.mem_cons_self ..)
        apply WP.spec_bind (Slice.index_usize_spec sorted 0#usize hi0)
        intro last hlast
        have hlastv : last.val = x := by
          rw [hlast]
          exact getElem_zero_val hS hpos
        have hn : (Slice.len sorted).val = (x :: xs).length := by
          rw [Slice.len_val]; exact hSlen
        have hlen1 : 1 ≤ (Slice.len sorted).val := by
          rw [hn]; simp
        have hS' : (x :: xs) = sorted.val.map (fun z => z.val) := hS.symm
        apply WP.spec_mono (can_make_loop_triple sorted (x :: xs) k d (Slice.len sorted)
          1#i64 last 1#usize hS' hn hlen1 (by rw [hn]; exact hN) (by simp) (by simpa using hlen1)
          (by rw [hlastv]; exact hx1) (by rw [hlastv]; exact hx2) hb)
        intro b hbpost
        rw [hlastv] at hbpost
        simpa [List.drop_one] using hbpost
    obtain ⟨b, hb', hp⟩ := spec_eq_ok hgoal
    exact ⟨b, hb', hp⟩

  /-! ### The binary search -/

  /-- The feasibility predicate of the binary search: `can_make` succeeds for the gap `d`. -/
  def feas (k : Std.I64) (x : ℤ) (xs : List ℤ) : ℤ → Prop :=
    fun d => k.val ≤ 1 + ((gcount d xs x : ℕ) : ℤ)

  theorem exists_drop (P : ℤ → Prop) (B : ℤ) (h0 : P 0) (hB : 0 ≤ B) :
      ∃ k : ℕ, P (B - (k : ℤ)) :=
    ⟨B.toNat, by rw [Int.toNat_of_nonneg hB]; simpa using h0⟩

  /-- The greatest feasible value in `[0, B]`, computed as the largest drop `B - k` which is
  feasible. -/
  noncomputable def rmax (P : ℤ → Prop) (B : ℤ) (hex : ∃ k : ℕ, P (B - (k : ℤ))) : ℤ := by
    classical
    exact B - ((Nat.find hex : ℕ) : ℤ)

  theorem rmax_spec (P : ℤ → Prop) (B : ℤ) (hex : ∃ k : ℕ, P (B - (k : ℤ))) :
      P (rmax P B hex) ∧ rmax P B hex ≤ B ∧
      ∀ d : ℤ, 0 ≤ d → d ≤ B → P d → d ≤ rmax P B hex := by
    classical
    have hunf : rmax P B hex = B - ((Nat.find hex : ℕ) : ℤ) := by
      simp only [rmax]
    have hP : P (B - ((Nat.find hex : ℕ) : ℤ)) := Nat.find_spec hex
    refine ⟨?_, ?_, ?_⟩
    · rw [hunf]; exact hP
    · rw [hunf]
      have : (0:ℤ) ≤ ((Nat.find hex : ℕ) : ℤ) := Nat.cast_nonneg _
      omega
    · intro d hd0 hdB hPd
      rw [hunf]
      have hk : Nat.find hex ≤ (B - d).toNat := by
        apply Nat.find_min' _ (p := fun k => P (B - (k : ℤ)))
        have h1 : B - ((((B - d).toNat) : ℕ) : ℤ) = d := by
          rw [Int.toNat_of_nonneg (show (0:ℤ) ≤ B - d by omega)]
          omega
        rw [h1]; exact hPd
      have hcast : (((Nat.find hex : ℕ)) : ℤ) ≤ ((((B - d).toNat) : ℕ) : ℤ) := by
        exact_mod_cast hk
      have h2 : ((((B - d).toNat) : ℕ) : ℤ) = B - d :=
        Int.toNat_of_nonneg (show (0:ℤ) ≤ B - d by omega)
      omega

  /-- The `Triple` form of `can_make_spec`. -/
  theorem can_make_triple (sorted : Slice Std.I64) (x : ℤ) (xs : List ℤ) (k d : Std.I64)
      (hS : sorted.val.map (fun y => y.val) = x :: xs)
      (hN : (x :: xs).length ≤ 100000)
      (hb : ∀ y ∈ x :: xs, 1 ≤ y ∧ y ≤ 1000000000) :
      can_make sorted k d ⦃ b => (b = true ↔ feas k x xs d.val) ⦄ := by
    obtain ⟨b, hb', hp⟩ := can_make_spec sorted x xs k d hS hN hb
    rw [hb']
    exact (WP.spec_ok b).2 hp

  theorem tdiv2_eq (a : ℤ) (ha : 0 ≤ a) : Int.tdiv a 2 = ((a.toNat / 2 : ℕ) : ℤ) := by
    have h : a = ((a.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [h]
    exact (Int.ofNat_tdiv a.toNat 2).symm

  /-! ### `Triple` forms of the piecewise specifications -/

  theorem loop0_triple (price : Slice Std.I64) (n : Usize) (vec : alloc.vec.Vec Std.I64)
      (i : Usize) (hn : n.val = price.length) (hi : i.val ≤ n.val)
      (hv : vec.val = price.val.take i.val) :
      maximum_tastiness_loop0 price n vec i ⦃ v => v.val = price.val.take n.val ⦄ := by
    obtain ⟨v, hv', hp⟩ := loop0_spec price n vec i hn hi hv
    rw [hv']
    exact (WP.spec_ok v).2 hp

  theorem Slice.sort_triple (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s ⦃ s' =>
        (s'.val.map (fun x => x.val)).Perm (s.val.map (fun x => x.val)) ∧
        (s'.val.map (fun x => x.val)).Pairwise (· ≤ ·) ⦄ := by
    obtain ⟨s', hs', hp1, hp2⟩ := Slice.sort_spec s
    rw [hs']
    exact (WP.spec_ok s').2 ⟨hp1, hp2⟩

  theorem Vec.getElem_spec {T : Type} (v : alloc.vec.Vec T) (i : Usize)
      (h : i.val < v.val.length) :
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) v i ⦃ x =>
        x = v.val[i.val] ⦄ := by
    rw [alloc.vec.Vec.index_slice_index]
    exact alloc.vec.Vec.index_usize_spec v i h

  theorem lift_deref_mut_spec (v : alloc.vec.Vec Std.I64) :
      WP.spec (lift (alloc.vec.Vec.deref_mut v))
        (fun p : Slice Std.I64 × (Slice Std.I64 → alloc.vec.Vec Std.I64) =>
          p.1.val = v.val ∧ ∀ t, (p.2 t).val = t.val) := by
    simp only [lift, WP.spec_ok]
    exact ⟨rfl, fun t => rfl⟩

  /-! ### Last elements and distinct values -/

  theorem pairwise_getElem_le {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) {i j : ℕ}
      (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) : l[i] ≤ l[j] := by
    rcases Nat.lt_or_ge i j with h | h
    · have hh := List.pairwise_iff_get.1 hs ⟨i, hi⟩ ⟨j, hj⟩ h
      rwa [List.get_eq_getElem, List.get_eq_getElem] at hh
    · have : i = j := le_antisymm hij h
      subst this
      exact le_rfl

  theorem getLast_eq_lastElem (l : List ℤ) (h : l ≠ []) :
      l.getLast h = l[l.length - 1]'(by have := List.length_pos_of_ne_nil h; omega) := by
    exact List.getLast_eq_getElem h

  theorem mem_le_getLast {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) {y : ℤ} (hy : y ∈ l)
      (h : l ≠ []) : y ≤ l.getLast h := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
    rw [getLast_eq_lastElem l h]
    exact pairwise_getElem_le hs hi (by have := List.length_pos_of_ne_nil h; omega) (by omega)

  theorem getLast_map_I64 (l : List Std.I64) (h : l ≠ []) :
      (l.map (fun x => x.val)).getLast (by simpa using h) = (l.getLast h).val := by
    exact List.getLast_map (by simpa using h)

  /-- With gap at least `1` the greedy scan from the head collects at most one value per
  distinct value of the whole list. -/
  theorem gcount_succ_le_dedup {d : ℤ} (hd : 1 ≤ d) (x : ℤ) (xs : List ℤ) :
      gcount d xs x + 1 ≤ (x :: xs).dedup.length := by
    set s := gacc d xs x with hs_def
    have hnd : s.Nodup := gacc_nodup hd xs x
    have hgt : ∀ z ∈ s, x < z := isChain_gt hd (gacc_isChain d xs x)
    have hnotmem : x ∉ s.toFinset := by
      intro hmem
      rw [List.mem_toFinset] at hmem
      have := hgt x hmem
      omega
    have hsub : insert x s.toFinset ⊆ (x :: xs).toFinset := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rw [List.mem_toFinset]
      rcases hz with rfl | hz
      · exact List.mem_cons_self ..
      · rw [List.mem_toFinset] at hz
        exact List.mem_cons_of_mem _ ((gacc_sublist d xs x).subset hz)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotmem, List.card_toFinset, List.card_toFinset,
      hnd.dedup] at hcard
    rw [gcount, ← hs_def]
    simpa using hcard

  /-- The binary search returns the greatest feasible gap. -/
  theorem loop1_spec (sorted : alloc.vec.Vec Std.I64) (k : Std.I64) (x : ℤ) (xs : List ℤ)
      (B : ℤ) (hB0 : 0 ≤ B) (hBmax : B ≤ 1000000000)
      (hS : sorted.val.map (fun y => y.val) = x :: xs)
      (hN : (x :: xs).length ≤ 100000)
      (hb : ∀ y ∈ x :: xs, 1 ≤ y ∧ y ≤ 1000000000)
      (hmono : ∀ d d', 0 ≤ d' → d' ≤ d → feas k x xs d → feas k x xs d')
      (hBnd : ∀ d, feas k x xs d → d ≤ B)
      (hP0 : feas k x xs 0)
      (lo hi : Std.I64) (hlo0 : 0 ≤ lo.val)
      (hloR : lo.val ≤ rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0))
      (hhiR : rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0) < hi.val)
      (hhiB : hi.val ≤ B + 1) :
      ∃ r, maximum_tastiness_loop1 k sorted lo hi = ok r ∧
        r.val = rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0) := by
    set R := rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0) with hRdef
    obtain ⟨hPR, hRB, hleR⟩ := rmax_spec (feas k x xs) B
      (exists_drop (feas k x xs) B hP0 hB0)
    have hR0 : 0 ≤ R := hleR 0 (le_refl 0) hB0 hP0
    have hTriple : maximum_tastiness_loop1 k sorted lo hi ⦃ r => r.val = R ⦄ := by
      unfold maximum_tastiness_loop1
      apply loop.spec_decr_nat
        (fun s : Std.I64 × Std.I64 => (s.2.val - s.1.val).toNat)
        (fun s : Std.I64 × Std.I64 =>
          0 ≤ s.1.val ∧ s.1.val ≤ R ∧ R < s.2.val ∧ s.2.val ≤ B + 1)
        (fun r : Std.I64 => r.val = R)
      · rintro ⟨lo, hi⟩ ⟨hlo0, hloR, hhiR, hhiB⟩
        dsimp only at hlo0 hloR hhiR hhiB ⊢
        unfold maximum_tastiness_loop1.body
        have hadd1 : Std.I64.min ≤ lo.val + 1 := by scalar_tac
        have hadd2 : lo.val + 1 ≤ Std.I64.max := by scalar_tac
        apply WP.spec_bind (I64.add_spec hadd1 hadd2)
        intro i hic
        have hiv : i.val = lo.val + 1 := hic
        by_cases hcase : i < hi
        · rw [if_pos hcase]
          have hcase' : lo.val + 1 < hi.val := by rw [← hiv]; exact hcase
          have hsub1 : Std.I64.min ≤ hi.val - lo.val := by scalar_tac
          have hsub2 : hi.val - lo.val ≤ Std.I64.max := by scalar_tac
          apply WP.spec_bind (I64.sub_spec hsub1 hsub2)
          intro i1 hi1
          have hi1v : i1.val = hi.val - lo.val := hi1
          have h2v : (2#i64).val = 2 := by simp
          apply WP.spec_bind (I64.div_spec (x := i1) (y := 2#i64) (by rw [h2v]; omega) (by
            intro ⟨h1, h2⟩
            omega))
          intro i2 hi2
          have hi2v : i2.val = ((hi.val - lo.val).toNat / 2 : ℕ) := by
            rw [hi2, hi1v, h2v, tdiv2_eq (hi.val - lo.val) (by omega)]
          have hD0 : 0 ≤ hi.val - lo.val := by omega
          have hhalf_ub : (((hi.val - lo.val).toNat / 2 : ℕ) : ℤ) ≤ hi.val - lo.val := by
            have hh : ((hi.val - lo.val).toNat : ℤ) = hi.val - lo.val :=
              Int.toNat_of_nonneg hD0
            have hle : ((hi.val - lo.val).toNat / 2 : ℕ) ≤ (hi.val - lo.val).toNat :=
              Nat.div_le_self _ _
            rw [← hh] at *
            exact_mod_cast hle
          have hi2nn : 0 ≤ i2.val := by rw [hi2v]; exact Nat.cast_nonneg _
          have hi2ub : i2.val ≤ 1000000001 := by rw [hi2v]; omega
          have hadd3 : Std.I64.min ≤ lo.val + i2.val := by scalar_tac
          have hadd4 : lo.val + i2.val ≤ Std.I64.max := by scalar_tac
          apply WP.spec_bind (I64.add_spec hadd3 hadd4)
          intro mid hmid
          have hmidv : mid.val = lo.val + i2.val := hmid
          have hmidv' : mid.val = lo.val + ((hi.val - lo.val).toNat / 2 : ℕ) := by
            rw [hmidv, hi2v]
          have hmid_lo : lo.val ≤ mid.val := by
            rw [hmidv']
            have hnn : (0:ℤ) ≤ (((hi.val - lo.val).toNat / 2 : ℕ) : ℤ) := Nat.cast_nonneg _
            omega
          have hmid_lt : mid.val < hi.val := by
            rw [hmidv']
            have hlt : ((hi.val - lo.val).toNat / 2 : ℕ) < (hi.val - lo.val).toNat := by omega
            have hh : ((hi.val - lo.val).toNat : ℤ) = hi.val - lo.val :=
              Int.toNat_of_nonneg hD0
            have hcast : (((hi.val - lo.val).toNat / 2 : ℕ) : ℤ) < ((hi.val - lo.val).toNat : ℤ) :=
              by exact_mod_cast hlt
            omega
          have hmid0 : 0 ≤ mid.val := le_trans hlo0 hmid_lo
          have hmidB : mid.val ≤ B := by omega
          have hSd : (alloc.vec.Vec.deref sorted).val.map (fun y => y.val) = x :: xs := by
            rw [alloc.vec.Vec.deref, Slice.from_val]
            exact hS
          apply WP.spec_bind (can_make_triple (alloc.vec.Vec.deref sorted) x xs k mid hSd hN hb)
          intro b hbpost
          by_cases hbt : b
          · rw [if_pos hbt]
            simp only [WP.spec_ok]
            have hfeas : feas k x xs mid.val := hbpost.mp hbt
            have hle : mid.val ≤ R := hleR mid.val hmid0 hmidB hfeas
            have hmeas : (hi.val - mid.val).toNat < (hi.val - lo.val).toNat := by
              rw [Int.toNat_lt_toNat (by omega)]
              omega
            exact ⟨⟨hmid0, hle, hhiR, hhiB⟩, hmeas⟩
          · rw [if_neg hbt]
            simp only [WP.spec_ok]
            have hnfeas : ¬ feas k x xs mid.val := fun h => hbt (hbpost.mpr h)
            have hRmid : R < mid.val := by
              by_contra hcon
              push_neg at hcon
              exact hnfeas (hmono R mid.val hmid0 hcon hPR)
            have hmeas : (mid.val - lo.val).toNat < (hi.val - lo.val).toNat := by
              rw [Int.toNat_lt_toNat (by omega)]
              omega
            exact ⟨⟨hlo0, hloR, hRmid, by omega⟩, hmeas⟩
        · rw [if_neg hcase]
          simp only [WP.spec_ok]
          have hexit : hi.val ≤ lo.val + 1 := by
            have : ¬ (lo.val + 1 < hi.val) := by rw [← hiv]; exact hcase
            omega
          omega
      · exact ⟨hlo0, hloR, hhiR, hhiB⟩
    obtain ⟨r, hr, hpost⟩ := spec_eq_ok hTriple
    exact ⟨r, hr, hpost⟩

  theorem loop1_triple (sorted : alloc.vec.Vec Std.I64) (k : Std.I64) (x : ℤ) (xs : List ℤ)
      (B : ℤ) (hB0 : 0 ≤ B) (hBmax : B ≤ 1000000000)
      (hS : sorted.val.map (fun y => y.val) = x :: xs)
      (hN : (x :: xs).length ≤ 100000)
      (hb : ∀ y ∈ x :: xs, 1 ≤ y ∧ y ≤ 1000000000)
      (hmono : ∀ d d', 0 ≤ d' → d' ≤ d → feas k x xs d → feas k x xs d')
      (hBnd : ∀ d, feas k x xs d → d ≤ B)
      (hP0 : feas k x xs 0)
      (lo hi : Std.I64) (hlo0 : 0 ≤ lo.val)
      (hloR : lo.val ≤ rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0))
      (hhiR : rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0) < hi.val)
      (hhiB : hi.val ≤ B + 1) :
      maximum_tastiness_loop1 k sorted lo hi ⦃ r =>
        r.val = rmax (feas k x xs) B (exists_drop (feas k x xs) B hP0 hB0) ⦄ := by
    obtain ⟨r, hr, hp⟩ := loop1_spec sorted k x xs B hB0 hBmax hS hN hb hmono hBnd hP0 lo hi
      hlo0 hloR hhiR hhiB
    rw [hr]
    exact (WP.spec_ok r).2 hp


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
  theorem spec_11 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        (r.val = 0 ↔ (vals price).dedup.length < k.val.toNat) := by
    have hpk : 0 ≤ k.val := by omega
    have hbound : ∀ y ∈ vals price, 1 ≤ y ∧ y ≤ 1000000000 := by
      intro y hy
      rw [vals, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact h_price z hz
    have hlenv : (Slice.len price).val = price.val.length := Slice.len_val price
    have hPL : price.length = price.val.length := rfl
    have h0v : (0#usize).val = 0 := rfl
    have hnz : ¬ (Slice.len price = 0#usize) := by
      intro h
      have h0 : (Slice.len price).val = 0 := by rw [h]; rfl
      have h0' : price.length = 0 := by
        have h0'' : (Slice.val price).length = 0 := by rw [← hlenv]; exact h0
        simpa using h0''
      omega
    have hmain : maximum_tastiness price k ⦃ r =>
        (r.val = 0 ↔ (vals price).dedup.length < k.val.toNat) ⦄ := by
      unfold maximum_tastiness
      dsimp only
      rw [if_neg hnz]
      apply WP.spec_bind (loop0_triple price (Slice.len price) (alloc.vec.Vec.new Std.I64) 0#usize
        hlenv (by simp) (by simp))
      intro vec hvec
      have hvec' : vec.val = price.val := by
        rw [hvec, hlenv, List.take_length]
      apply WP.spec_bind (lift_deref_mut_spec vec)
      rintro ⟨s, back⟩ ⟨hsv, hbk⟩
      apply WP.spec_bind (Slice.sort_triple s)
      intro s1 hs1
      obtain ⟨hperm1, hsort1⟩ := hs1
      have hV : (back s1).val = s1.val := hbk s1
      have hsortS : ((back s1).val.map (fun y => y.val)).Pairwise (· ≤ ·) := by
        rw [hV]; exact hsort1
      have hpermv : (s.val.map (fun y => y.val)).Perm (price.val.map (fun y => y.val)) := by
        rw [show s.val.map (fun y => y.val) = price.val.map (fun y => y.val) by rw [hsv, hvec']]
      have hpermS : ((back s1).val.map (fun y => y.val)).Perm
          (price.val.map (fun y => y.val)) := by
        have h1 : ((back s1).val.map (fun y => y.val)).Perm (s.val.map (fun y => y.val)) := by
          rw [hV]; exact hperm1
        exact h1.trans hpermv
      have hlenS : ((back s1).val.map (fun y => y.val)).length =
          (price.val.map (fun y => y.val)).length := hpermS.length_eq
      have hbS : ∀ y ∈ (back s1).val.map (fun z => z.val), 1 ≤ y ∧ y ≤ 1000000000 := by
        intro y hy
        exact hbound y (hpermS.subset hy)
      have hSne : (back s1).val.map (fun y => y.val) ≠ [] := by
        intro h
        have h2 : (price.val.map (fun y => y.val)).length = 0 := by
          rw [← hlenS, h]
          simp
        rw [List.length_map] at h2
        omega
      obtain ⟨x, xs, hSx⟩ : ∃ x xs, (back s1).val.map (fun y => y.val) = x :: xs := by
        cases hl : (back s1).val.map (fun y => y.val) with
        | nil => exact absurd hl hSne
        | cons a t => exact ⟨a, t, rfl⟩
      have hxle : ∀ y ∈ xs, x ≤ y := by
        have h := hsortS
        rw [hSx, List.pairwise_cons] at h
        exact h.1
      have hxsorted : xs.Pairwise (· ≤ ·) := by
        have h := hsortS
        rw [hSx, List.pairwise_cons] at h
        exact h.2
      have hlenS' : (x :: xs).length = price.val.length := by
        rw [← hSx]
        simpa using hlenS
      have hp2 : 2 ≤ ((back s1).val.map (fun y => y.val)).length := by
        rw [hSx, hlenS']
        exact h_n
      have hn2 : 2 ≤ (Slice.len price).val := by rw [hlenv]; exact h_n
      have hsubh : (1#usize).val ≤ (Slice.len price).val := by
        have h1 : (1#usize).val = 1 := rfl
        rw [h1, hlenv]; omega
      apply WP.spec_bind (Usize.sub_spec hsubh)
      intro i hisub
      obtain ⟨hisub1, -⟩ := hisub
      have hiv : i.val = (Slice.len price).val - 1 := hisub1
      have hs1len : (back s1).val.length = price.val.length := by
        have h := hlenS
        simpa using h
      have hm1 : ((back s1).val.map (fun y : Std.I64 => y.val)).length = (back s1).val.length :=
        List.length_map ..
      have hislen : i.val < (back s1).val.length := by omega
      apply WP.spec_bind (Vec.getElem_spec (back s1) i hislen)
      intro i1 hi1
      have hi1v : i1 = (back s1).val[i.val] := hi1
      have h0len : (0#usize).val < (back s1).val.length := by omega
      apply WP.spec_bind (Vec.getElem_spec (back s1) 0#usize h0len)
      intro i2 hi2
      have hi2v : i2 = (back s1).val[(0#usize).val] := hi2
      have hi1S : i1.val = ((back s1).val.map (fun z : Std.I64 => z.val))[i.val]'
          (by rw [hm1]; exact hislen) := by
        rw [hi1v]
        exact (List.getElem_map (f := fun z : Std.I64 => z.val) (l := (back s1).val)
          (i := i.val)).symm
      have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 :=
        hbS _ (by rw [hi1S]; exact List.getElem_mem (by rw [hm1]; exact hislen))
      have hi2val : i2.val = x := by
        rw [hi2v]
        exact getElem_zero_val hSx (by omega)
      have hi2b : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
        have hmem : x ∈ (back s1).val.map (fun z : Std.I64 => z.val) := by
          rw [hSx]; exact List.mem_cons_self ..
        have := hbS x hmem
        omega
      have hsubb1 : Std.I64.min ≤ i1.val - i2.val := by scalar_tac
      have hsubb2 : i1.val - i2.val ≤ Std.I64.max := by scalar_tac
      apply WP.spec_bind (I64.sub_spec hsubb1 hsubb2)
      intro md hmd
      have hmdv : md.val = i1.val - i2.val := hmd
      have haddb1 : Std.I64.min ≤ md.val + 1 := by scalar_tac
      have haddb2 : md.val + 1 ≤ Std.I64.max := by scalar_tac
      apply WP.spec_bind (I64.add_spec haddb1 haddb2)
      intro hi_ hhi_
      have hhiv : hi_.val = md.val + 1 := hhi_
      -- the endpoints of the sorted values
      have hSlast : i1.val = ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne := by
        rw [hi1S, getLast_eq_lastElem]
        congr 1
        omega
      have hmax : md.val = ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne - x := by
        rw [hmdv, hSlast, hi2val]
      -- the hypotheses of the binary search
      have hN : (x :: xs).length ≤ 100000 := by
        rw [hlenS']; exact h_len
      have hbx : ∀ y ∈ x :: xs, 1 ≤ y ∧ y ≤ 1000000000 := by
        intro y hy
        exact hbS y (by rw [hSx]; exact hy)
      have hmono : ∀ d d', 0 ≤ d' → d' ≤ d → feas k x xs d → feas k x xs d' := by
        intro d d' hd' hdd hfeas
        show k.val ≤ 1 + (((gcount d' xs x : ℕ)) : ℤ)
        have h1 : gcount d xs x ≤ gcount d' xs x :=
          gcount_mono_d d d' hdd xs x hxsorted hxle
        have h2 : ((gcount d xs x : ℕ) : ℤ) ≤ ((gcount d' xs x : ℕ) : ℤ) := by
          exact_mod_cast h1
        have h3 : k.val ≤ 1 + ((gcount d xs x : ℕ) : ℤ) := hfeas
        linarith
      have hBnd : ∀ d, feas k x xs d → d ≤ md.val := by
        intro d hd
        have hd' : k.val ≤ 1 + ((gcount d xs x : ℕ) : ℤ) := hd
        have h1 : 1 ≤ gcount d xs x := by omega
        obtain ⟨y, hy, hdy⟩ := gcount_pos h1
        have hymem : y ∈ (back s1).val.map (fun z : Std.I64 => z.val) := by
          rw [hSx]; exact List.mem_cons_of_mem _ hy
        have hyub : y ≤ ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne :=
          mem_le_getLast hsortS hymem hSne
        have hx0 : x ≤ y := by
          rw [hSx] at hymem
          exact hxle y hy
        omega
      have hP0 : feas k x xs 0 := by
        show k.val ≤ 1 + ((gcount 0 xs x : ℕ) : ℤ)
        rw [gcount_zero xs x hxsorted hxle]
        have h1 : ((xs.length + 1 : ℕ) : ℤ) = ((x :: xs).length : ℤ) := by simp
        have h2 : ((x :: xs).length : ℤ) = (price.val.length : ℤ) := by rw [hlenS']
        omega
      have hxmem : x ∈ (back s1).val.map (fun z : Std.I64 => z.val) := by
        rw [hSx]; exact List.mem_cons_self ..
      have hxub : x ≤ ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne :=
        mem_le_getLast hsortS hxmem hSne
      obtain ⟨hx1, hx2⟩ := hbS x hxmem
      have hglb : 1 ≤ ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne :=
        (hbS _ (List.getLast_mem hSne)).1
      have hgub : ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne ≤ 1000000000 :=
        (hbS _ (List.getLast_mem hSne)).2
      have hB0 : 0 ≤ md.val := by rw [hmax]; omega
      have hBmax : md.val ≤ 1000000000 := by rw [hmax]; omega
      obtain ⟨hPR, hRB, hleR⟩ := rmax_spec (feas k x xs) md.val
        (exists_drop (feas k x xs) md.val hP0 hB0)
      have hlo0 : (0:ℤ) ≤ (0#i64).val := by simp
      have hloR : (0#i64).val ≤ rmax (feas k x xs) md.val
          (exists_drop (feas k x xs) md.val hP0 hB0) :=
        hleR 0 (le_refl 0) hB0 hP0
      have hhiR : rmax (feas k x xs) md.val (exists_drop (feas k x xs) md.val hP0 hB0) < hi_.val := by
        rw [hhiv]
        have := hRB
        omega
      have hhiB : hi_.val ≤ md.val + 1 := by rw [hhiv]
      apply WP.spec_mono (loop1_triple (back s1) k x xs md.val hB0 hBmax hSx hN hbx hmono hBnd
        hP0 (0#i64) hi_ hlo0 hloR hhiR hhiB)
      intro r hr
      -- final analysis
      have hdedup : (x :: xs).dedup.length = (vals price).dedup.length := by
        have hp : (x :: xs).Perm (vals price) := by
          rw [← hSx]
          exact hpermS
        exact hp.dedup.length_eq
      rw [hr]
      have hkpos : (0:ℤ) < k.val := by omega
      have hkcast : ((k.val.toNat : ℕ) : ℤ) = k.val := Int.toNat_of_nonneg hpk
      constructor
      · -- `R = 0` implies the number of distinct values is smaller than `k`
        intro hzero
        by_contra hcon
        push_neg at hcon
        have hfeas1 : feas k x xs 1 := by
          show k.val ≤ 1 + ((gcount 1 xs x : ℕ) : ℤ)
          have h1 := gcount_one_head x xs (by rw [← hSx]; exact hsortS)
          have h3 : ((gcount 1 xs x : ℕ) : ℤ) + 1 = ((x :: xs).dedup.length : ℤ) := by
            exact_mod_cast h1
          have h2 : ((k.val.toNat : ℕ) : ℤ) ≤ ((x :: xs).dedup.length : ℤ) := by
            rw [hdedup]
            exact_mod_cast hcon
          omega
        have h1g : 1 ≤ gcount 1 xs x := by
          have hd' : k.val ≤ 1 + ((gcount 1 xs x : ℕ) : ℤ) := hfeas1
          omega
        obtain ⟨y, hy, hdy⟩ := gcount_pos h1g
        have hymem : y ∈ (back s1).val.map (fun z : Std.I64 => z.val) := by
          rw [hSx]; exact List.mem_cons_of_mem _ hy
        have hyub : y ≤ ((back s1).val.map (fun z : Std.I64 => z.val)).getLast hSne :=
          mem_le_getLast hsortS hymem hSne
        have hx0 : x ≤ y := hxle y hy
        have h1md : 1 ≤ md.val := by rw [hmax]; omega
        have := hleR 1 (by norm_num) h1md hfeas1
        omega
      · -- fewer than `k` distinct values forces `R = 0`
        intro hlt
        by_contra hne
        have h1R : 1 ≤ rmax (feas k x xs) md.val
            (exists_drop (feas k x xs) md.val hP0 hB0) := by omega
        have hg := gcount_succ_le_dedup (d := rmax (feas k x xs) md.val
          (exists_drop (feas k x xs) md.val hP0 hB0)) h1R x xs
        have hcast : ((gcount (rmax (feas k x xs) md.val (exists_drop (feas k x xs) md.val hP0 hB0))
            xs x : ℕ) : ℤ) + 1 ≤ ((x :: xs).dedup.length : ℤ) := by
          exact_mod_cast hg
        have hPR' : k.val ≤ 1 + ((gcount (rmax (feas k x xs) md.val
            (exists_drop (feas k x xs) md.val hP0 hB0)) xs x : ℕ) : ℤ) := hPR
        have hd2 : ((x :: xs).dedup.length : ℤ) < k.val := by
          have h4 : ((x :: xs).dedup.length : ℤ) < ((k.val.toNat : ℕ) : ℤ) := by
            rw [hdedup]
            exact_mod_cast hlt
          omega
        omega
    obtain ⟨r, hr, hpost⟩ := spec_eq_ok hmain
    exact ⟨r, hr, hpost⟩

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
