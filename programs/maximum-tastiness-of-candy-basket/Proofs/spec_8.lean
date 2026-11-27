import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_8` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary lemmas for `spec_S8`

  The proofs below analyse the concrete Rust program: the two element-copying
  loops, the binary search on the gap, and the greedy feasibility test
  `can_make`. -/

  open Aegis.MaximumTastiness

  /-- A total-correctness specification yields the actual result of the
  computation. -/
  theorem spec_exists_ok {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
      ∃ v, m = ok v ∧ p v := by
    revert h
    refine Result.cases m ?_ ?_ ?_
    · intro v h
      exact ⟨v, rfl, (WP.spec_ok v).mp h⟩
    · intro e k h
      exact absurd h (by simp [WP.spec_vis])
    · intro h
      exact absurd h (by simp [WP.spec_div])

  /-- Well-founded induction principle for `Aeneas.Std.loop`, for partial
  correctness with a decreasing natural measure. -/
  theorem loop_spec_wf {α β : Type} (body : α → Result (ControlFlow α β)) (post : β → Prop)
      (P : α → Prop) (measure : α → ℕ)
      (hstep : ∀ x, P x → WP.spec (body x) (fun r => match r with
          | .cont y => P y ∧ measure y < measure x
          | .done b => post b)) :
      ∀ (m : ℕ) (x : α), P x → measure x = m → WP.spec (loop body x) post := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx hm
      rw [Aeneas.Std.loop.eq_def]
      refine WP.spec_bind (Pₘ := fun r => match r with
        | .cont y => WP.spec (loop body y) post
        | .done b => post b) ?_ ?_
      · refine WP.spec_mono (P₀ := fun r => match r with
            | .cont y => P y ∧ measure y < measure x
            | .done b => post b) (hstep x hx) ?_
        intro r hr
        cases r with
        | cont y =>
          obtain ⟨hy, hlt⟩ := hr
          exact ih (measure y) (by omega) y hy rfl
        | done b => simpa using hr
      · intro r hr
        cases r with
        | cont y => exact hr
        | done b => simpa using hr

  /-- `loop_spec_wf` with the measure instantiated. -/
  theorem loop_spec_wf' {α β : Type} (body : α → Result (ControlFlow α β)) (post : β → Prop)
      (P : α → Prop) (measure : α → ℕ)
      (hstep : ∀ x, P x → WP.spec (body x) (fun r => match r with
          | .cont y => P y ∧ measure y < measure x
          | .done b => post b))
      (x : α) (hx : P x) : WP.spec (loop body x) post :=
    loop_spec_wf body post P measure hstep _ x hx rfl

  /-- The prices stored in a (sorted) vector, as a list of integers. -/
  def sv (v : alloc.vec.Vec Std.I64) : List ℤ := vals (alloc.vec.Vec.deref v)

  theorem sv_eq (v : alloc.vec.Vec Std.I64) : sv v = v.val.map (fun x => x.val) := by
    simp [sv, vals, alloc.vec.Vec.deref]

  /-! ### The copy loop `maximum_tastiness_loop0` -/

  /-- Greedy scan: starting from the value `last`, walk the list left to right
  and pick an element whenever it is at distance at least `d` from the last
  picked value. -/
  def gscan (d last : ℤ) : List ℤ → List ℤ
    | [] => []
    | y :: ys => if d ≤ y - last then y :: gscan d y ys else gscan d last ys

  /-- Greedy selection from a whole list: the first element is always picked. -/
  def gsel (s : List ℤ) (d : ℤ) : List ℤ :=
    match s with
    | [] => []
    | x :: xs => x :: gscan d x xs

  theorem gscan_cons_pos (d last y : ℤ) (ys : List ℤ) (h : d ≤ y - last) :
      gscan d last (y :: ys) = y :: gscan d y ys := by
    simp only [gscan, if_pos h]

  theorem gscan_cons_neg (d last y : ℤ) (ys : List ℤ) (h : ¬ d ≤ y - last) :
      gscan d last (y :: ys) = gscan d last ys := by
    simp only [gscan, if_neg h]

  theorem gsel_cons (d x : ℤ) (xs : List ℤ) : gsel (x :: xs) d = x :: gscan d x xs := rfl

  theorem gscan_nil (d last : ℤ) : gscan d last [] = [] := rfl

  /-- `GapsFrom d last l`: consecutive elements of `l` (starting from the
  previous picked value `last`) differ by at least `d`. -/
  def GapsFrom (d last : ℤ) : List ℤ → Prop
    | [] => True
    | y :: ys => d ≤ y - last ∧ GapsFrom d y ys

  /-- `Gaps d l`: consecutive elements of `l` differ by at least `d`. -/
  def Gaps (d : ℤ) (l : List ℤ) : Prop :=
    match l with
    | [] => True
    | a :: t => GapsFrom d a t

  theorem gapsFrom_mono {d last last' : ℤ} {l : List ℤ} (h : GapsFrom d last l)
      (h' : last' ≤ last) : GapsFrom d last' l := by
    induction l generalizing last last' with
    | nil => trivial
    | cons y ys ih =>
      obtain ⟨h1, h2⟩ := h
      exact ⟨by omega, ih h2 le_rfl⟩

  theorem gapsFrom_ge (d : ℤ) (hd : 0 ≤ d) (last : ℤ) (l : List ℤ) (h : GapsFrom d last l) :
      ∀ x ∈ l, last + d ≤ x := by
    induction l generalizing last with
    | nil => intro x hx; exact absurd hx (by simp)
    | cons y ys ih =>
      obtain ⟨h1, h2⟩ := h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := ih y h2 x hx'
        omega

  theorem gapsFrom_gscan (d last : ℤ) (l : List ℤ) : GapsFrom d last (gscan d last l) := by
    induction l generalizing last with
    | nil => trivial
    | cons y ys ih =>
      by_cases h : d ≤ y - last
      · rw [gscan_cons_pos d last y ys h]
        exact ⟨h, ih y⟩
      · rw [gscan_cons_neg d last y ys h]
        exact ih last

  theorem gaps_gsel (s : List ℤ) (d : ℤ) : Gaps d (gsel s d) := by
    cases s with
    | nil => trivial
    | cons x xs => exact gapsFrom_gscan d x xs

  theorem gscan_eq_of_gapsFrom (d last : ℤ) (l : List ℤ) (h : GapsFrom d last l) :
      gscan d last l = l := by
    induction l generalizing last with
    | nil => rfl
    | cons y ys ih =>
      obtain ⟨h1, h2⟩ := h
      rw [gscan_cons_pos d last y ys h1, ih y h2]

  theorem gscan_sublist (d last : ℤ) (l : List ℤ) : (gscan d last l).Sublist l := by
    induction l generalizing last with
    | nil => exact List.Sublist.slnil
    | cons y ys ih =>
      by_cases h : d ≤ y - last
      · rw [gscan_cons_pos d last y ys h]
        exact List.Sublist.cons₂ y (ih y)
      · rw [gscan_cons_neg d last y ys h]
        exact List.Sublist.cons y (ih last)

  theorem gsel_sublist (s : List ℤ) (d : ℤ) : (gsel s d).Sublist s := by
    cases s with
    | nil => exact List.Sublist.slnil
    | cons x xs => exact List.Sublist.cons₂ x (gscan_sublist d x xs)

  theorem gsel_ne_nil (s : List ℤ) (d : ℤ) (h : s ≠ []) : gsel s d ≠ [] := by
    cases s with
    | nil => exact absurd rfl h
    | cons x xs => simp [gsel_cons]

  theorem gscan_length_le (d last : ℤ) (l : List ℤ) : (gscan d last l).length ≤ l.length :=
    (gscan_sublist d last l).length_le

  theorem gsel_length_le (s : List ℤ) (d : ℤ) : (gsel s d).length ≤ s.length :=
    (gsel_sublist s d).length_le

  theorem gscan_length_ge (d last : ℤ) (hd : 0 ≤ d) :
      ∀ (s t : List ℤ), s.Pairwise (· ≤ ·) → t.Sublist s → GapsFrom d last t →
        t.length ≤ (gscan d last s).length := by
    intro s
    induction s generalizing last with
    | nil =>
      intro t hs hsub hg
      have ht : t = [] := List.eq_nil_of_sublist_nil hsub
      subst ht
      simp [gscan_nil]
    | cons y ys ih =>
      intro t hs hsub hg
      obtain ⟨hyall, hys⟩ := List.pairwise_cons.mp hs
      by_cases hlt : d ≤ y - last
      · rw [gscan_cons_pos d last y ys hlt]
        cases t with
        | nil => simp
        | cons t0 ts =>
          obtain ⟨h1, h2⟩ := hg
          have ht0 : t0 ∈ y :: ys := hsub.subset (List.mem_cons_self ..)
          have hyt0 : y ≤ t0 := by
            rcases List.mem_cons.mp ht0 with h | h
            · rw [h]
            · exact hyall t0 h
          have hsub' : ts.Sublist ys := List.Sublist.of_cons_cons hsub
          have hg' : GapsFrom d y ts := gapsFrom_mono h2 hyt0
          have := ih y ts hys hsub' hg'
          simp only [List.length_cons]
          omega
      · rw [gscan_cons_neg d last y ys hlt]
        have hall : ∀ x ∈ t, last + d ≤ x := gapsFrom_ge d hd last t hg
        have hy : y ∉ t := by
          intro hmem
          have := hall y hmem
          omega
        have hsub' : t.Sublist ys := by
          rcases List.sublist_cons_iff.mp hsub with hh | ⟨r, hr, hh⟩
          · exact hh
          · rw [hr] at hy
            exact absurd List.mem_cons_self hy
        exact ih last t hys hsub' hg

  theorem gsel_length_ge (d : ℤ) (hd : 0 ≤ d) (s t : List ℤ)
      (hs : s.Pairwise (· ≤ ·)) (hsub : t.Sublist s) (hgaps : Gaps d t) :
      t.length ≤ (gsel s d).length := by
    cases s with
    | nil =>
      have ht : t = [] := List.eq_nil_of_sublist_nil hsub
      subst ht
      simp [gsel]
    | cons y ys =>
      cases t with
      | nil => simp
      | cons t0 ts =>
        obtain ⟨hyall, hys⟩ := List.pairwise_cons.mp hs
        have hsub' : ts.Sublist ys := List.Sublist.of_cons_cons hsub
        have ht0 : t0 ∈ y :: ys := hsub.subset (List.mem_cons_self ..)
        have hyt0 : y ≤ t0 := by
          rcases List.mem_cons.mp ht0 with h | h
          · rw [h]
          · exact hyall t0 h
        have hg' : GapsFrom d y ts := gapsFrom_mono hgaps hyt0
        have := gscan_length_ge d y hd ys ts hys hsub' hg'
        simp only [gsel_cons, List.length_cons]
        omega

  /-! ### Slice/list bridge lemmas -/

  theorem vals_eq_map (s : Slice Std.I64) : vals s = s.val.map (fun x => x.val) := rfl

  theorem vals_length (s : Slice Std.I64) : (vals s).length = s.length := by
    simp [vals]

  theorem vals_getElem (s : Slice Std.I64) (i : ℕ) (h : i < (vals s).length) :
      (vals s)[i] = (s.val[i]'(by simpa [vals] using h)).val := by
    simp [vals, List.getElem_map]

  theorem getElem_mem_drop {l : List ℤ} {i : ℕ} (h : i < l.length) : l[i] ∈ l.drop i := by
    rw [List.drop_eq_getElem_cons h]
    exact List.mem_cons_self ..

  theorem pairwise_drop_succ {l : List ℤ} (hs : l.Pairwise (· ≤ ·)) {i : ℕ} (h : i < l.length) :
      ∀ x ∈ l.drop (i + 1), l[i] ≤ x := by
    have h1 : (l.drop i).Pairwise (· ≤ ·) := hs.drop (i := i)
    rw [List.drop_eq_getElem_cons h] at h1
    exact (List.pairwise_cons.mp h1).1

  theorem gscan_drop_pos {l : List ℤ} {i : ℕ} (h : i < l.length) (last : ℤ) (d : ℤ)
      (hc : d ≤ l[i] - last) :
      gscan d last (l.drop i) = l[i] :: gscan d l[i] (l.drop (i + 1)) := by
    rw [List.drop_eq_getElem_cons h, gscan_cons_pos d last _ _ hc]

  theorem gscan_drop_neg {l : List ℤ} {i : ℕ} (h : i < l.length) (last : ℤ) (d : ℤ)
      (hc : ¬ (d ≤ l[i] - last)) :
      gscan d last (l.drop i) = gscan d last (l.drop (i + 1)) := by
    rw [List.drop_eq_getElem_cons h, gscan_cons_neg d last _ _ hc]

  /-! ### The greedy feasibility test `can_make` -/

  theorem can_make_loop_body_spec (s : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize)
      (hsort : (vals s).Pairwise (· ≤ ·)) (hd : 0 ≤ d.val) (hk : 2 ≤ k.val)
      (hn : n.val = (vals s).length)
      (hval : ∀ x ∈ vals s, 1 ≤ x ∧ x ≤ 1000000000)
      (hL : (vals s).length ≤ 100000)
      (hi : i.val ≤ n.val)
      (hlast_lo : 1 ≤ last.val) (hlast_hi : last.val ≤ 1000000000)
      (hall : ∀ x ∈ (vals s).drop i.val, last.val ≤ x)
      (hinv : count.val + (gscan d.val last.val ((vals s).drop i.val)).length
                = (gsel (vals s) d.val).length) :
      WP.spec (can_make_loop.body s k d n count last i)
        (fun r => match r with
          | .cont y => y.2.2.val ≤ n.val ∧
              (∀ x ∈ (vals s).drop y.2.2.val, y.2.1.val ≤ x) ∧
              y.1.val + (gscan d.val y.2.1.val ((vals s).drop y.2.2.val)).length
                = (gsel (vals s) d.val).length ∧
              1 ≤ y.2.1.val ∧ y.2.1.val ≤ 1000000000 ∧
              n.val - y.2.2.val < n.val - i.val
          | .done b => (b = true ↔ k.val ≤ (gsel (vals s) d.val).length)) := by
    simp only [can_make_loop.body]
    split
    case isTrue hilt =>
      have hiltv : i.val < n.val := by simpa using hilt
      have hilt' : i.val < (vals s).length := by omega
      have hsval : i.val < s.val.length := by simpa [vals] using hilt'
      have hmem : (vals s)[i.val] ∈ (vals s).drop i.val := getElem_mem_drop hilt'
      have hlast_le : last.val ≤ (vals s)[i.val] := hall _ hmem
      have hvi : 1 ≤ (vals s)[i.val] ∧ (vals s)[i.val] ≤ 1000000000 :=
        hval _ (List.getElem_mem hilt')
      have hUsize : (vals s).length ≤ Std.Usize.max := by
        rw [vals_length]; exact s.property
      step
      have hi1v : i1.val = (vals s)[i.val] := by
        rw [i1_post, vals_getElem s i.val hilt']
      have hb1 : Aeneas.Std.I64.min ≤ i1.val - last.val := by
        rw [Aeneas.Std.I64.min_eq]; omega
      have hb2 : i1.val - last.val ≤ Aeneas.Std.I64.max := by
        rw [Aeneas.Std.I64.max_eq]; omega
      step
      have hi2v : i2.val = i1.val - last.val := i2_post
      have hgsel_le : ((gsel (vals s) d.val).length : ℤ) ≤ 100000 := by
        have h := gsel_length_le (vals s) d.val
        omega
      have hcount_le : count.val ≤ ((gsel (vals s) d.val).length : ℤ) := by
        have h1 : (0 : ℤ) ≤ ((gscan d.val last.val ((vals s).drop i.val)).length : ℤ) :=
          Int.natCast_nonneg _
        omega
      split
      case isTrue hge =>
        have hgev : d.val ≤ i2.val := by simpa using hge
        have hge' : d.val ≤ (vals s)[i.val] - last.val := by omega
        have hlen1 : 1 ≤ (gscan d.val last.val ((vals s).drop i.val)).length := by
          rw [gscan_drop_pos hilt' last.val d.val hge', List.length_cons]
          omega
        have hmax : count.val + 1 ≤ Aeneas.Std.I64.max := by
          rw [Aeneas.Std.I64.max_eq]; omega
        step
        have hc1v : count1.val = count.val + 1 := count1_post
        split
        case isTrue hck =>
          have hckv : k.val ≤ count1.val := by simpa using hck
          simp only [WP.spec_ok, true_iff]
          omega
        case isFalse hck =>
          have hckv : count1.val < k.val := by
            have h : ¬ (k.val ≤ count1.val) := by simpa using hck
            omega
          have hi3max : i.val + 1 ≤ Std.Usize.max := by omega
          refine WP.spec_bind (Pₘ := fun (i3 : Std.Usize) => (i3 : Std.Usize).val = i.val + 1) ?_ ?_
          · simpa using (Std.Usize.add_spec (x := i) (y := 1#usize) hi3max)
          · intro i3 hi3v
            simp only [WP.spec_ok]
            refine ⟨?_, ?_, ?_, by rw [hi1v]; exact hvi.1, by rw [hi1v]; exact hvi.2, ?_⟩
            · omega
            · intro x hx
              rw [hi3v] at hx
              rw [hi1v]
              exact pairwise_drop_succ hsort hilt' x hx
            · have hlen : (gscan d.val i1.val ((vals s).drop (i.val + 1))).length
                  = (gscan d.val last.val ((vals s).drop i.val)).length - 1 := by
                rw [gscan_drop_pos hilt' last.val d.val hge', List.length_cons, hi1v]
                omega
              rw [hi3v, hlen]
              omega
            · omega
      case isFalse hge =>
        have hgev : ¬ (d.val ≤ i2.val) := by simpa using hge
        have hge' : ¬ (d.val ≤ (vals s)[i.val] - last.val) := by omega
        have hi3max : i.val + 1 ≤ Std.Usize.max := by omega
        have hmax : count.val + 1 ≤ Aeneas.Std.I64.max := by
          rw [Aeneas.Std.I64.max_eq]; omega
        refine WP.spec_bind (Pₘ := fun (i3 : Std.Usize) => (i3 : Std.Usize).val = i.val + 1) ?_ ?_
        · simpa using (Std.Usize.add_spec (x := i) (y := 1#usize) hi3max)
        · intro i3 hi3v
          simp only [WP.spec_ok]
          refine ⟨?_, ?_, ?_, hlast_lo, hlast_hi, ?_⟩
          · omega
          · intro x hx
            rw [hi3v] at hx
            refine hall x ?_
            rw [List.drop_eq_getElem_cons hilt']
            exact List.mem_cons_of_mem _ hx
          · rw [hi3v, ← gscan_drop_neg hilt' last.val d.val hge']
            exact hinv
          · omega
    case isFalse hilt =>
      have hge : n.val ≤ i.val := by
        have h : ¬ (i.val < n.val) := by simpa using hilt
        omega
      have hdrop : (vals s).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        omega
      have hgnil : gscan d.val last.val ((vals s).drop i.val) = [] := by rw [hdrop, gscan_nil]
      simp only [WP.spec_ok]
      have hcount_eq : count.val = ((gsel (vals s) d.val).length : ℤ) := by
        have h := hinv
        rw [hgnil] at h
        simpa using h
      constructor
      · intro h
        have : k.val ≤ count.val := by simpa using h
        omega
      · intro h
        have : k.val ≤ count.val := by omega
        simpa using this

  theorem can_make_spec (s : Slice Std.I64) (k d : Std.I64)
      (hsort : (vals s).Pairwise (· ≤ ·)) (hd : 0 ≤ d.val) (hk : 2 ≤ k.val)
      (hnpos : 0 < (vals s).length)
      (hval : ∀ x ∈ vals s, 1 ≤ x ∧ x ≤ 1000000000)
      (hL : (vals s).length ≤ 100000) :
      WP.spec (can_make s k d) (fun b => b = true ↔ k.val ≤ (gsel (vals s) d.val).length) := by
    have hnv : (Slice.len s).val = (vals s).length := by
      simp [vals, Aeneas.Std.Slice.len]
    have haux : ∀ (m : ℕ) (count last : Std.I64) (i : Std.Usize),
        i.val ≤ (vals s).length →
        1 ≤ last.val → last.val ≤ 1000000000 →
        (∀ x ∈ (vals s).drop i.val, last.val ≤ x) →
        count.val + (gscan d.val last.val ((vals s).drop i.val)).length
          = (gsel (vals s) d.val).length →
        (vals s).length - i.val = m →
        WP.spec (can_make_loop s k d (Slice.len s) count last i)
          (fun b => b = true ↔ k.val ≤ (gsel (vals s) d.val).length) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro count last i hi hlo hhi hall hinv hm
        simp only [can_make_loop]
        rw [Aeneas.Std.loop.eq_def]
        refine WP.spec_bind (Pₘ := fun r => match r with
          | .cont y => y.2.2.val ≤ (Slice.len s).val ∧
              (∀ x ∈ (vals s).drop y.2.2.val, y.2.1.val ≤ x) ∧
              y.1.val + (gscan d.val y.2.1.val ((vals s).drop y.2.2.val)).length
                = (gsel (vals s) d.val).length ∧
              1 ≤ y.2.1.val ∧ y.2.1.val ≤ 1000000000 ∧
              (Slice.len s).val - y.2.2.val < (Slice.len s).val - i.val
          | .done b => (b = true ↔ k.val ≤ (gsel (vals s) d.val).length)) ?_ ?_
        · refine WP.spec_mono (P₀ := fun r => match r with
            | .cont y => y.2.2.val ≤ (Slice.len s).val ∧
                (∀ x ∈ (vals s).drop y.2.2.val, y.2.1.val ≤ x) ∧
                y.1.val + (gscan d.val y.2.1.val ((vals s).drop y.2.2.val)).length
                  = (gsel (vals s) d.val).length ∧
                1 ≤ y.2.1.val ∧ y.2.1.val ≤ 1000000000 ∧
                (Slice.len s).val - y.2.2.val < (Slice.len s).val - i.val
            | .done b => (b = true ↔ k.val ≤ (gsel (vals s) d.val).length))
            (can_make_loop_body_spec s k d (Slice.len s) count last i hsort hd hk hnv hval hL
              (by rw [hnv]; exact hi) hlo hhi hall hinv) ?_
          intro r hr
          cases r with
          | cont y => exact hr
          | done b => exact hr
        · intro r hr
          cases r with
          | cont y =>
            obtain ⟨c', l', i'⟩ : Std.I64 × Std.I64 × Std.Usize := y
            obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
            simp only [Prod.fst, Prod.snd] at *
            exact ih ((vals s).length - i') (by omega) c' l' i' (by omega) h4 h5 h2 h3 rfl
          | done b => simpa using hr
    simp only [can_make]
    split
    case isTrue hk1 =>
      exfalso
      have h : k.val ≤ 1 := by simpa using hk1
      omega
    case isFalse hk1 =>
      have h0 : (0#usize).val < s.val.length := by simpa [vals] using hnpos
      step
      have hlastv : last.val = (vals s)[0] := by
        rw [last_post, vals_getElem s 0 hnpos]
      have hmem0 : (vals s)[0] ∈ vals s := List.getElem_mem hnpos
      have hb := hval _ hmem0
      have hdecomp : (vals s) = (vals s)[0] :: (vals s).drop (0 + 1) := by
        rw [← List.drop_eq_getElem_cons (l := vals s) (i := 0) hnpos, List.drop_zero]
      refine haux ((vals s).length - 1) 1#i64 last 1#usize ?_ ?_ ?_ ?_ ?_ rfl
      · rw [show (1#usize : Std.Usize).val = 1 from rfl]
        omega
      · rw [hlastv]; exact hb.1
      · rw [hlastv]; exact hb.2
      · intro x hx
        rw [hlastv]
        exact pairwise_drop_succ hsort hnpos x (by simpa using hx)
      · rw [hdecomp, gsel_cons, List.length_cons, hlastv]
        have h1 : (↑(1#usize) : ℕ) = 1 := rfl
        rw [h1]
        simp only [List.drop_succ_cons, List.drop_zero]
        have h2 : (1#i64 : Std.I64).val = 1 := by simp
        rw [h2]
        omega

  theorem loop0_body_cont (price : Slice Std.I64) (n : Std.Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hi : i.val < n.val) (hn : n.val = price.val.length)
      (hvl : sorted.val = price.val.take i.val) :
      WP.spec (maximum_tastiness_loop0.body price n sorted i)
        (fun r => match r with
          | .cont (s', i') => i'.val = i.val + 1 ∧ s'.val = price.val.take i'.val
          | .done _ => False) := by
    simp only [maximum_tastiness_loop0.body]
    split
    case isTrue h =>
      step
      step
      step
      simp_all
    case isFalse h => simp_all

  theorem loop0_body_done (price : Slice Std.I64) (n : Std.Usize)
      (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hi : ¬ i.val < n.val) (hin : i.val ≤ n.val) (hn : n.val = price.val.length)
      (hvl : sorted.val = price.val.take i.val) :
      WP.spec (maximum_tastiness_loop0.body price n sorted i)
        (fun r => match r with
          | .cont _ => False
          | .done v => v.val = price.val) := by
    simp only [maximum_tastiness_loop0.body]
    split
    case isTrue h => exact absurd h hi
    case isFalse h =>
      have hge : n.val ≤ i.val := by omega
      have hie : i.val = n.val := by omega
      simp only [WP.spec_ok, ControlFlow.done.injEq]
      rw [hvl, hie, hn, List.take_length]

  theorem maximum_tastiness_loop0_aux (price : Slice Std.I64) (n : Std.Usize) :
      ∀ (m : ℕ) (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize),
        n.val = price.val.length → i.val ≤ n.val →
        sorted.val = price.val.take i.val → n.val - i.val = m →
        WP.spec (maximum_tastiness_loop0 price n sorted i) (fun v => v.val = price.val) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro sorted i hn hi hvl hm
      simp only [maximum_tastiness_loop0]
      rw [Aeneas.Std.loop.eq_def]
      refine WP.spec_bind (Pₘ := fun r => match r with
        | .cont y => y.2.val ≤ n.val ∧ y.1.val = price.val.take y.2.val ∧
            n.val - y.2.val < n.val - i.val
        | .done b => b.val = price.val) ?_ ?_
      · by_cases h : i.val < n.val
        · refine WP.spec_mono (P₀ := fun r => match r with
              | .cont (s', i') => i'.val = i.val + 1 ∧ s'.val = price.val.take i'.val
              | .done _ => False) (loop0_body_cont price n sorted i h hn hvl) ?_
          intro r hr
          cases r with
          | cont y =>
            obtain ⟨s', i'⟩ := y
            obtain ⟨h1, h2⟩ := hr
            simp only [Prod.fst, Prod.snd] at *
            exact ⟨by omega, h2, by omega⟩
          | done b => exact hr.elim
        · refine WP.spec_mono (P₀ := fun r => match r with
              | .cont _ => False
              | .done v => v.val = price.val) (loop0_body_done price n sorted i h hi hn hvl) ?_
          intro r hr
          cases r with
          | cont y => exact hr.elim
          | done b => exact hr
      · intro r hr
        cases r with
        | cont y =>
          obtain ⟨s', i'⟩ := y
          obtain ⟨h1, h2, h3⟩ := hr
          simp only [Prod.fst, Prod.snd] at *
          exact ih (n.val - i') (by omega) s' i' hn (by omega) h2 rfl
        | done b => simpa using hr

  theorem maximum_tastiness_loop0_spec (price : Slice Std.I64) (n : Std.Usize)
      (hn : n.val = price.val.length) :
      WP.spec (maximum_tastiness_loop0 price n (alloc.vec.Vec.new Std.I64) 0#usize)
        (fun v => v.val = price.val) := by
    refine maximum_tastiness_loop0_aux price n _ (alloc.vec.Vec.new Std.I64) 0#usize hn ?_ ?_ rfl
    · simp
    · simp [alloc.vec.Vec.new]

  /-! ### The binary search `maximum_tastiness_loop1` -/

  theorem maximum_tastiness_loop1_aux (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (hsort : (sv sorted).Pairwise (· ≤ ·))
      (hnpos : 0 < (sv sorted).length)
      (hval : ∀ x ∈ sv sorted, 1 ≤ x ∧ x ≤ 1000000000)
      (hL : (sv sorted).length ≤ 100000)
      (hk : 2 ≤ k.val) :
      ∀ (m : ℕ) (lo hi : Std.I64),
        0 ≤ lo.val → lo.val < hi.val → hi.val ≤ 1000000001 →
        k.val ≤ (gsel (sv sorted) lo.val).length →
        (gsel (sv sorted) hi.val).length < k.val →
        (hi.val - lo.val).toNat = m →
        WP.spec (maximum_tastiness_loop1 k sorted lo hi)
          (fun r => 0 ≤ r.val ∧
            k.val ≤ (gsel (sv sorted) r.val).length ∧
            (gsel (sv sorted) (r.val + 1)).length < k.val) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro lo hi hlo0 hlt hhi hfeas hinfeas hm
      simp only [maximum_tastiness_loop1]
      rw [Aeneas.Std.loop.eq_def]
      have hb1 : Aeneas.Std.I64.min ≤ lo.val + 1 := by
        rw [Aeneas.Std.I64.min_eq]; omega
      have hb2 : lo.val + 1 ≤ Aeneas.Std.I64.max := by
        rw [Aeneas.Std.I64.max_eq]; omega
      refine WP.spec_bind (Pₘ := fun r => match r with
        | .cont y => 0 ≤ y.1.val ∧ y.1.val < y.2.val ∧ y.2.val ≤ 1000000001 ∧
            k.val ≤ (gsel (sv sorted) y.1.val).length ∧
            (gsel (sv sorted) y.2.val).length < k.val ∧
            (y.2.val - y.1.val).toNat < m
        | .done r' => 0 ≤ r'.val ∧ k.val ≤ (gsel (sv sorted) r'.val).length ∧
            (gsel (sv sorted) (r'.val + 1)).length < k.val) ?_ ?_
      · simp only [maximum_tastiness_loop1.body]
        step
        have hiv : (i : Std.I64).val = lo.val + 1 := i_post
        split
        case isTrue hcond =>
          have hcondl : lo.val + 1 < hi.val := by rw [← hiv]; simpa using hcond
          have hb3 : Aeneas.Std.I64.min ≤ hi.val - lo.val := by
            rw [Aeneas.Std.I64.min_eq]; omega
          have hb4 : hi.val - lo.val ≤ Aeneas.Std.I64.max := by
            rw [Aeneas.Std.I64.max_eq]; omega
          step
          have hi1v : i1.val = hi.val - lo.val := i1_post
          have hd1 : i1.val ≠ 0 := by omega
          have hd2 : ¬ (i1.val = Aeneas.Std.I64.min ∧ (2#i64).val = -1) := by
            intro h
            rw [Aeneas.Std.I64.min_eq] at h
            omega
          step
          have hi2v : i2.val = i1.val.tdiv 2 := i2_post
          have hi2lo : 1 ≤ i2.val := by
            rw [hi2v, Int.tdiv_eq_ediv_of_nonneg (by omega)]
            omega
          have hi2hi : i2.val ≤ i1.val - 1 := by
            rw [hi2v, Int.tdiv_eq_ediv_of_nonneg (by omega)]
            omega
          have hb5 : Aeneas.Std.I64.min ≤ lo.val + i2.val := by
            rw [Aeneas.Std.I64.min_eq]; omega
          have hb6 : lo.val + i2.val ≤ Aeneas.Std.I64.max := by
            rw [Aeneas.Std.I64.max_eq]; omega
          step
          have hmidv : mid.val = lo.val + i2.val := mid_post
          have hmid0 : 0 ≤ mid.val := by omega
          have hmidlo : lo.val < mid.val := by omega
          have hmidhi : mid.val < hi.val := by omega
          have hmidmax : mid.val ≤ 1000000001 := by omega
          have hdiff : (hi.val - mid.val).toNat < m := by
            have := hm
            omega
          have hdiff' : (mid.val - lo.val).toNat < m := by
            have := hm
            omega
          refine WP.spec_bind (Pₘ := fun (b : Bool) =>
            (b = true ↔ k.val ≤ (gsel (sv sorted) mid.val).length)) ?_ ?_
          · exact can_make_spec (alloc.vec.Vec.deref sorted) k mid hsort hmid0 hk hnpos hval hL
          · intro b hb
            cases b with
            | false =>
              have hb' : ¬ (k.val ≤ (gsel (sv sorted) mid.val).length) := by
                simpa using hb
              have hinfeas' : (gsel (sv sorted) mid.val).length < k.val := by omega
              simp only [Bool.false_eq_true, if_false, WP.spec_ok]
              exact ⟨hlo0, hmidlo, hmidmax, hfeas, hinfeas', hdiff'⟩
            | true =>
              have hb' : k.val ≤ (gsel (sv sorted) mid.val).length := by
                simpa using hb
              simp only [if_true, WP.spec_ok]
              exact ⟨hmid0, hmidhi, hhi, hb', hinfeas, hdiff⟩
        case isFalse hcond =>
          have hcondv : ¬ (i.val < hi.val) := by simpa using hcond
          have hie : lo.val + 1 = hi.val := by omega
          simp only [WP.spec_ok]
          refine ⟨hlo0, ?_, ?_⟩
          · exact hfeas
          · rw [hie]; exact hinfeas
      · intro r hr
        cases r with
        | cont y =>
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
          exact ih ((y.2.val - y.1.val).toNat) h6 y.1 y.2 h1 h2 h3 h4 h5 rfl
        | done r' => simpa using hr

  /-! ## The insertion sort returns a sorted permutation -/

  theorem cmp_I64_eq (x y : Aeneas.Std.I64) :
      Aeneas.Std.core.cmp.OrdI64.cmp x y = .ok (compare x.val y.val) := rfl

  theorem compare_eq_gt_of_lt {a b : ℤ} (h : b < a) : compare a b = Ordering.gt :=
    compare_gt_iff_gt.mpr h

  theorem compare_ne_gt_of_le {a b : ℤ} (h : a ≤ b) : compare a b ≠ Ordering.gt := by
    intro hc
    rw [compare_gt_iff_gt] at hc
    omega

  theorem sortInsert_spec (cmp : Aeneas.Std.I64 → Aeneas.Std.I64 → Result Ordering)
      (hcmp : ∀ x y, cmp x y = .ok (compare x.val y.val))
      (x : Aeneas.Std.I64) (l : List Aeneas.Std.I64)
      (hl : l.Pairwise (fun a b => a.val ≤ b.val)) :
      ∃ r, AegisShim.sortInsert cmp x l = .ok r ∧
        r.Perm (x :: l) ∧ r.Pairwise (fun a b => a.val ≤ b.val) := by
    revert hl
    induction l with
    | nil =>
      intro _
      exact ⟨[x], by simp [AegisShim.sortInsert], List.Perm.refl _,
        List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩⟩
    | cons y ys ih =>
      intro hl
      obtain ⟨hyall, htaily⟩ := List.pairwise_cons.mp hl
      obtain ⟨r, hr, hperm, hpw⟩ := ih htaily
      by_cases hlt : y.val < x.val
      · have hgt : compare x.val y.val = Ordering.gt := compare_eq_gt_of_lt hlt
        refine ⟨y :: r, ?_, ?_, ?_⟩
        · simp [AegisShim.sortInsert, hcmp, hgt, hr]
        · exact (List.Perm.cons y hperm).trans (List.Perm.swap x y ys)
        · refine List.pairwise_cons.mpr ⟨?_, hpw⟩
          intro a ha
          rcases List.mem_cons.mp (hperm.mem_iff.mp ha) with rfl | hmem
          · omega
          · exact hyall a hmem
      · have hge : x.val ≤ y.val := by omega
        have hngt : compare x.val y.val ≠ Ordering.gt := compare_ne_gt_of_le hge
        refine ⟨x :: y :: ys, ?_, List.Perm.refl _, ?_⟩
        · simp [AegisShim.sortInsert, hcmp, hngt, hr]
        · refine List.pairwise_cons.mpr ⟨?_, hl⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | hmem
          · omega
          · have := hyall a hmem
            omega

  theorem sortList_spec (L : List Aeneas.Std.I64) :
      ∃ L', AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp L = .ok L' ∧
        L'.Perm L ∧ L'.Pairwise (fun a b => a.val ≤ b.val) := by
    induction L with
    | nil =>
      exact ⟨[], by simp [AegisShim.sortList], List.Perm.refl _, List.Pairwise.nil⟩
    | cons x xs ih =>
      obtain ⟨r, hr, hperm, hpw⟩ := ih
      obtain ⟨r', hr', hperm', hpw'⟩ :=
        sortInsert_spec Aeneas.Std.core.cmp.OrdI64.cmp (fun a b => rfl) x r hpw
      refine ⟨r', ?_, ?_, hpw'⟩
      · simp only [AegisShim.sortList, hr, hr', bind_ok]
      · exact hperm'.trans (List.Perm.cons x hperm)

  theorem slice_sort_spec (s : Aeneas.Std.Slice Aeneas.Std.I64) :
      ∃ s', alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s = .ok s' ∧
        s'.val.Perm s.val ∧ s'.val.Pairwise (fun a b => a.val ≤ b.val) ∧
        s'.val.length = s.val.length := by
    obtain ⟨l, hl, hperm, hpw⟩ := sortList_spec s.val
    have hlen : l.length = s.val.length := hperm.length_eq
    have hbound : l.length ≤ Usize.max := by
      rw [hlen]
      exact s.property
    refine ⟨Slice.from l hbound, ?_, ?_, ?_, ?_⟩
    · simp only [alloc.slice.Slice.sort, hl, bind_ok]
      rw [dite_eq_left hbound]
    · simpa using hperm
    · simpa using hpw
    · simpa using hlen

  /-! ### Extracting the witness pair -/

  theorem absDiff_comm (a b : ℤ) : absDiff a b = absDiff b a := by
    have h : b - a = -(a - b) := by omega
    simp only [absDiff, h, Int.natAbs_neg]

  theorem absDiff_of_le {a b : ℤ} (h : a ≤ b) : absDiff b a = b - a := by
    have h' : 0 ≤ b - a := by omega
    simp only [absDiff]
    exact Int.natAbs_of_nonneg h'

  theorem pairwise_head_le {l : List ℤ} (h : l.Pairwise (· ≤ ·)) (hne : l ≠ []) :
      ∀ x ∈ l, l.head hne ≤ x := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_refl _
      · exact (List.pairwise_cons.mp h).1 x hx'

  theorem pairwise_le_getLast {l : List ℤ} (h : l.Pairwise (· ≤ ·)) (hne : l ≠ []) :
      ∀ x ∈ l, x ≤ l.getLast hne := by
    induction l with
    | nil => exact absurd rfl hne
    | cons a t ih =>
      cases t with
      | nil =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_refl _
        · exact absurd hx' (by simp)
      | cons b t' =>
        intro x hx
        obtain ⟨hab, hbt⟩ := List.pairwise_cons.mp h
        rcases List.mem_cons.mp hx with rfl | hx'
        · have hmem : (b :: t').getLast (by simp) ∈ b :: t' := List.getLast_mem ..
          have h1 := hab _ hmem
          simpa using h1
        · have h2 := ih hbt (by simp) x hx'
          simpa using h2

  theorem gsel_length_le_one {V : List ℤ} {d mn mx : ℤ}
      (hmn : ∀ x ∈ V, mn ≤ x) (hmx : ∀ x ∈ V, x ≤ mx) (hd : mx - mn < d) :
      (gsel V d).length ≤ 1 := by
    have hsub := gsel_sublist V d
    have hg := gaps_gsel V d
    rcases hW : gsel V d with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp
    · simp
    · exfalso
      rw [hW] at hsub hg
      obtain ⟨h1, -⟩ := hg
      have hma : a ∈ V := hsub.subset (by simp)
      have hmb : b ∈ V := hsub.subset (by simp)
      have h2 : b ≤ mx := hmx b hmb
      have h3 : mn ≤ a := hmn a hma
      omega

  theorem not_nodup_of_two_positions {l : List ℤ} {p q : ℕ} (hpq : p < q) (hq : q < l.length)
      (h : l.getD p 0 = l.getD q 0) : ¬ l.Nodup := by
    intro hnd
    have hinj : Function.Injective l.get := List.nodup_iff_injective_get.mp hnd
    have hp : p < l.length := by omega
    have hpq' : (⟨p, hp⟩ : Fin l.length) ≠ ⟨q, hq⟩ := by
      intro he
      have : p = q := by simpa using congrArg Fin.val he
      omega
    refine hpq' (hinj ?_)
    rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at h
    exact h

  theorem exists_two_of_not_nodup {l : List ℤ} (h : ¬ l.Nodup) :
      ∃ i j, i < j ∧ j < l.length ∧ l.getD i 0 = l.getD j 0 := by
    have hnotinj : ¬ Function.Injective l.get := by
      intro hh
      exact h (List.nodup_iff_injective_get.mpr hh)
    simp only [Function.Injective, not_forall, exists_prop] at hnotinj
    obtain ⟨i, j, hij, hne⟩ := hnotinj
    rcases lt_or_gt_of_ne (by intro he; exact hne (Fin.ext (by simpa using he))) with hlt | hlt
    · refine ⟨i.val, j.val, hlt, j.isLt, ?_⟩
      rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt]
      simpa using hij
    · refine ⟨j.val, i.val, hlt, i.isLt, ?_⟩
      rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt]
      simpa using hij.symm

  theorem exists_adjacent_of_gaps_not (d : ℤ) :
      ∀ (W : List ℤ), Gaps d W → ¬ Gaps (d + 1) W →
        ∃ i, ∃ (h : i + 1 < W.length), W[i + 1] - W[i] = d := by
    intro W
    induction W with
    | nil => intro _ h; exact absurd trivial h
    | cons a t ih =>
      cases t with
      | nil => intro _ h; exact absurd trivial h
      | cons b t' =>
        intro hg hng
        obtain ⟨h1, h2⟩ := hg
        by_cases hc : d + 1 ≤ b - a
        · have hng' : ¬ Gaps (d + 1) (b :: t') := by
            intro hgg
            exact hng ⟨hc, hgg⟩
          obtain ⟨i, hi, hadj⟩ := ih h2 hng'
          exact ⟨i + 1, by simpa using hi, by simpa using hadj⟩
        · refine ⟨0, by simp, ?_⟩
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          omega

  theorem pair_of_gsel {V : List ℤ} {r k : ℤ} (hsort : V.Pairwise (· ≤ ·))
      (hr0 : 0 ≤ r) (hk : 2 ≤ k) (hfeas : k ≤ (gsel V r).length)
      (hinfeas : (gsel V (r + 1)).length < k) :
      (∃ a ∈ V, ∃ b ∈ V, b - a = r) ∧ (r ≠ 0 ∨ ¬ V.Nodup) := by
    have hsub := gsel_sublist V r
    have hg := gaps_gsel V r
    have hlen : 2 ≤ (gsel V r).length := by omega
    constructor
    · by_cases hcase : Gaps (r + 1) (gsel V r)
      · exfalso
        have h3 := gsel_length_ge (r + 1) (by omega) V (gsel V r) hsort hsub hcase
        omega
      · obtain ⟨i, hi, hadj⟩ := exists_adjacent_of_gaps_not r (gsel V r) hg hcase
        have hmem1 : (gsel V r)[i] ∈ V := hsub.subset (List.getElem_mem (by omega))
        have hmem2 : (gsel V r)[i + 1] ∈ V := hsub.subset (List.getElem_mem hi)
        exact ⟨_, hmem1, _, hmem2, hadj⟩
    · by_cases hcase : Gaps (r + 1) (gsel V r)
      · exfalso
        have h3 := gsel_length_ge (r + 1) (by omega) V (gsel V r) hsort hsub hcase
        omega
      · obtain ⟨i, hi, hadj⟩ := exists_adjacent_of_gaps_not r (gsel V r) hg hcase
        rcases eq_or_ne r 0 with h0 | h0
        · right
          have hdup : ¬ (gsel V r).Nodup := by
            refine not_nodup_of_two_positions (p := i) (q := i + 1) (by omega) hi ?_
            rw [List.getD_eq_getElem _ _ (by omega : i < (gsel V r).length),
              List.getD_eq_getElem _ _ hi]
            omega
          intro hV
          exact hdup (hV.sublist hsub)
        · exact Or.inl h0

  /-- The witness pair for `spec_S8`: the returned value is the distance of two
  distinct positions of the price array. -/
  theorem final_pair {price : Slice Std.I64} {V : List ℤ} {r k : ℤ}
      (hperm : V.Perm (vals price)) (hsort : V.Pairwise (· ≤ ·))
      (hr0 : 0 ≤ r) (hk : 2 ≤ k)
      (hfeas : k ≤ (gsel V r).length) (hinfeas : (gsel V (r + 1)).length < k) :
      ∃ i j, i < j ∧ j < (vals price).length ∧
        r = absDiff ((vals price).getD i 0) ((vals price).getD j 0) := by
    obtain ⟨⟨a, ha, b, hb, hba⟩, hcase⟩ := pair_of_gsel hsort hr0 hk hfeas hinfeas
    rcases eq_or_ne r 0 with h0 | hne
    · subst h0
      have hVnd : ¬ V.Nodup := by
        rcases hcase with h | h
        · exact absurd rfl h
        · exact h
      have hnd : ¬ (vals price).Nodup := fun h => hVnd (hperm.nodup_iff.mpr h)
      obtain ⟨i, j, hij, hj, heq⟩ := exists_two_of_not_nodup hnd
      refine ⟨i, j, hij, hj, ?_⟩
      have hi : i < (vals price).length := by omega
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at heq
      rw [heq]
      simp [absDiff]
    · have hab : a ≠ b := by
        intro h
        apply hne
        rw [← hba, h]
        ring
      have hamem : a ∈ vals price := hperm.subset ha
      have hbmem : b ∈ vals price := hperm.subset hb
      obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hamem
      obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hbmem
      have hble : a ≤ b := by omega
      have hne_ij : i ≠ j := by
        intro h
        apply hab
        rw [← hiv, ← hjv]
        simp [h]
      rcases lt_or_gt_of_ne hne_ij with hlt | hlt
      · refine ⟨i, j, hlt, hj, ?_⟩
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hiv, hjv, absDiff_comm,
          absDiff_of_le hble]
        omega
      · refine ⟨j, i, hlt, hi, ?_⟩
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi, hjv, hiv,
          absDiff_of_le hble]
        omega

  /-! ### `step`-ready specifications for the outer program -/

  /-! ### Combinatorial facts used by the final assembly of `spec_S8` -/

  theorem sv_mk (s : Slice Std.I64) : sv { slice := s } = vals s := by
    rw [sv_eq]; rfl

  theorem map_val_getD (l : List Std.I64) (j : ℕ) :
      (l.map (fun x => x.val)).getD j 0 = (l.getD j 0#i64).val := by
    induction l generalizing j with
    | nil => cases j <;> simp [List.getD]
    | cons a t ih =>
      cases j with
      | zero => simp
      | succ k => simpa using ih k

  theorem gapsFrom_zero_of_pairwise {l : List ℤ} (h : l.Pairwise (· ≤ ·)) {last : ℤ}
      (hle : ∀ x ∈ l, last ≤ x) : GapsFrom 0 last l := by
    induction l generalizing last with
    | nil => trivial
    | cons y ys ih =>
      obtain ⟨hyall, hys⟩ := List.pairwise_cons.mp h
      exact ⟨by have := hle y (List.mem_cons_self ..); omega, ih hys hyall⟩

  theorem gsel_zero_of_pairwise {V : List ℤ} (h : V.Pairwise (· ≤ ·)) : gsel V 0 = V := by
    cases V with
    | nil => rfl
    | cons x xs =>
      obtain ⟨hxall, hxs⟩ := List.pairwise_cons.mp h
      simp only [gsel_cons]
      rw [gscan_eq_of_gapsFrom 0 x xs (gapsFrom_zero_of_pairwise hxs hxall)]

  theorem getD_le_of_pairwise {V : List ℤ} (h : V.Pairwise (· ≤ ·)) {j : ℕ}
      (hj : j < V.length) : V.getD 0 0 ≤ V.getD j 0 := by
    have h0 : 0 < V.length := by omega
    rcases Nat.eq_zero_or_pos j with hz | hp
    · subst hz; exact le_rfl
    · rw [List.getD_eq_getElem V 0 h0, List.getD_eq_getElem V 0 hj]
      exact (List.pairwise_iff_getElem.mp h) 0 j h0 hj hp

  theorem getD_le_last_of_pairwise {V : List ℤ} (h : V.Pairwise (· ≤ ·)) {i j : ℕ}
      (hi : i = V.length - 1) (hj : j < V.length) : V.getD j 0 ≤ V.getD i 0 := by
    have hi' : i < V.length := by omega
    rcases lt_or_eq_of_le (by omega : j ≤ i) with hlt | heq
    · rw [List.getD_eq_getElem V 0 hj, List.getD_eq_getElem V 0 hi']
      exact (List.pairwise_iff_getElem.mp h) j i hj hi' hlt
    · subst heq; exact le_rfl

  @[step] theorem slice_sort_step (s : Slice Std.I64) :
      WP.spec (alloc.slice.Slice.sort Aeneas.Std.core.cmp.OrdI64 s)
        (fun s' => s'.val.Perm s.val ∧ s'.val.Pairwise (fun a b => a.val ≤ b.val) ∧
          s'.val.length = s.val.length) := by
    obtain ⟨s', h1, h2, h3, h4⟩ := slice_sort_spec s
    rw [h1]
    simp only [WP.spec_ok]
    exact ⟨h2, h3, h4⟩

  @[step] theorem maximum_tastiness_loop1_step (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (hi : Std.I64)
      (hsort : (sv sorted).Pairwise (· ≤ ·)) (hne : sv sorted ≠ [])
      (hval : ∀ x ∈ sv sorted, 1 ≤ x ∧ x ≤ 1000000000) (hL : (sv sorted).length ≤ 100000)
      (hk : 2 ≤ k.val) (hhi0 : 0 < hi.val) (hhi1 : hi.val ≤ 1000000001)
      (hfeas0 : k.val ≤ (gsel (sv sorted) (0#i64).val).length)
      (hinfeas : (gsel (sv sorted) hi.val).length < k.val) :
      WP.spec (maximum_tastiness_loop1 k sorted 0#i64 hi)
        (fun r => 0 ≤ r.val ∧ k.val ≤ (gsel (sv sorted) r.val).length ∧
          (gsel (sv sorted) (r.val + 1)).length < k.val) := by
    have hr := maximum_tastiness_loop1_aux k sorted hsort (by
      rcases Nat.eq_zero_or_pos (sv sorted).length with h | h
      · exact absurd (List.eq_nil_of_length_eq_zero h) hne
      · exact h) hval hL hk ((hi.val - (0#i64).val).toNat) 0#i64 hi (by simp) (by simpa using hhi0)
        hhi1 (by simpa using hfeas0) hinfeas rfl
    simpa using hr

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
  theorem spec_8 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∃ i j : ℕ, i < j ∧ j < (vals price).length ∧
          r.val = absDiff ((vals price).getD i 0) ((vals price).getD j 0) := by
    have hwp : WP.spec (maximum_tastiness price k) (fun r => 0 ≤ r.val ∧
        ∃ V : List ℤ, V.Perm (vals price) ∧ V.Pairwise (· ≤ ·) ∧
          k.val ≤ (gsel V r.val).length ∧ (gsel V (r.val + 1)).length < k.val) := by
      have vdm : ∀ (v : alloc.vec.Vec Std.I64),
          (lift (alloc.vec.Vec.deref_mut v)) ⦃ (s, back) =>
            s.val = v.val ∧ back = (fun s' => { slice := s' }) ⦄ := by
        intro v
        unfold lift alloc.vec.Vec.deref_mut
        simp [WP.spec_ok, alloc.vec.Vec.val]
      unfold maximum_tastiness
      have hn0 : price.len ≠ 0#usize := by
        intro h'
        have h2 : price.val.length = 0 := by
          have := congrArg (fun u : Std.Usize => u.val) h'
          simpa using this
        have h3 := h_n
        simp only [Slice.length] at h3
        omega
      rw [if_neg hn0]
      step with maximum_tastiness_loop0_spec as ⟨ sorted, hs ⟩
      step with vdm as ⟨ sl, back, hsl, hback ⟩
      step as ⟨ s1, hperm, hpair, hlen ⟩
      subst back
      have hs1len : s1.val.length = price.val.length := by rw [hlen, hsl, hs]
      have hposlen : 0 < price.val.length := Nat.lt_of_lt_of_le (by norm_num) h_n
      have hs1perm : s1.val.Perm price.val := hperm.trans (by rw [hsl, hs])
      have hVeq : sv { slice := s1 } = vals s1 := sv_mk s1
      have hVsort : (vals s1).Pairwise (· ≤ ·) := by
        simp only [vals]
        exact hpair.map _ (fun a b hab => hab)
      have hVperm : (vals s1).Perm (vals price) := by
        simp only [vals]
        exact (hperm.map _).trans (by rw [hsl, hs])
      have hVlen : (vals s1).length = price.val.length := by
        simp only [vals, List.length_map]
        exact hs1len
      have hVne : vals s1 ≠ [] := by
        intro h
        have h0 : (vals s1).length = 0 := by rw [h]; rfl
        omega
      step as ⟨ i, hiv ⟩ by simp only [Slice.len_val]; omega
      have hb : i.val < s1.val.length := by
        rw [hiv, Slice.len_val, hs1len]
        exact Nat.sub_one_lt (Nat.ne_of_gt hposlen)
      step as ⟨ i1, hi1 ⟩
      case hbound => exact hb
      have hi1' : i1 = (s1.val)[i.val]'hb := hi1
      have hi1mem : i1 ∈ price.val :=
        hs1perm.mem_iff.mp (by rw [hi1']; exact List.getElem_mem hb)
      have hi1b := h_price i1 hi1mem
      step as ⟨ i2, hi2 ⟩
      case hbound =>
        show 0 < s1.val.length
        rw [hs1len]; exact hposlen
      have hi2' : i2 = (s1.val)[0]'(by omega) := hi2
      have hi2mem : i2 ∈ price.val :=
        hs1perm.mem_iff.mp (by rw [hi2']; exact List.getElem_mem _)
      have hi2b := h_price i2 hi2mem
      have hibV : i.val < (vals s1).length := by
        simp only [vals, List.length_map]; exact hb
      have hi1D : i1.val = (vals s1).getD i.val 0 := by
        rw [hi1']
        simp only [vals]
        rw [map_val_getD, List.getD_eq_getElem _ _ hb]
      have hi2D : i2.val = (vals s1).getD 0 0 := by
        rw [hi2']
        simp only [vals]
        rw [map_val_getD, List.getD_eq_getElem _ _ (by omega : 0 < s1.val.length)]
      have hiDlen : i.val = (vals s1).length - 1 := by
        rw [hiv, Slice.len_val, hVlen]
      have hi01 : i2.val ≤ i1.val := by
        rw [hi2D, hi1D]
        exact getD_le_of_pairwise hVsort hibV
      step as ⟨ max_diff, hmd ⟩
      step as ⟨ hi, hhi ⟩
      have hi_eq : (↑hi : ℤ) = (↑i1 : ℤ) - ↑i2 + 1 := by rw [hhi, hmd]
      step with maximum_tastiness_loop1_step as ⟨ r, hr0, hfeas, hinfeas ⟩
      case hval =>
        rw [hVeq]
        intro x hx
        simp only [vals] at hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact h_price y (hs1perm.mem_iff.mp hy)
      case hfeas0 =>
        have h0v : (↑(0#i64) : ℤ) = 0 := rfl
        have hgsel0 : gsel (sv { slice := s1 }) 0 = sv { slice := s1 } :=
          gsel_zero_of_pairwise (by rw [hVeq]; exact hVsort)
        rw [h0v, hgsel0, hVeq, hVlen]
        exact h_k_hi
      case hinfeas =>
        have hmnd : ∀ x ∈ sv { slice := s1 }, (↑i2 : ℤ) ≤ x := by
          rw [hVeq]
          intro x hx
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
          rw [hi2D, ← List.getD_eq_getElem (vals s1) 0 hj]
          exact getD_le_of_pairwise hVsort hj
        have hmxd : ∀ x ∈ sv { slice := s1 }, x ≤ (↑i1 : ℤ) := by
          rw [hVeq]
          intro x hx
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
          rw [hi1D, ← List.getD_eq_getElem (vals s1) 0 hj]
          exact getD_le_last_of_pairwise hVsort hiDlen hj
        have hle1 : (gsel (sv { slice := s1 }) (↑hi)).length ≤ 1 :=
          gsel_length_le_one hmnd hmxd (by rw [hi_eq]; omega)
        omega
      case a =>
        refine ⟨hr0, sv { slice := s1 }, ?_, ?_, hfeas, hinfeas⟩
        · rw [hVeq]; exact hVperm
        · rw [hVeq]; exact hVsort
    obtain ⟨r, hr, hr0, V, hVperm, hVsort, hfeas, hinfeas⟩ := spec_exists_ok hwp
    obtain ⟨i, j, hij, hj, heq⟩ := final_pair hVperm hVsort hr0 h_k_lo hfeas hinfeas
    exact ⟨r, hr, i, j, hij, hj, heq⟩

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
