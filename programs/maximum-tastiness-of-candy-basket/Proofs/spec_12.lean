import Aegis.MaximumTastiness.Code.Funs
import Mathlib.Data.Finset.Sort

/-
Proof of `AegisSpec.MaximumTastiness.spec_12` (maximum-tastiness-of-candy-basket).
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

  /-! ## Auxiliary material for the proof of `spec_S12`

  We model the greedy scan performed by `can_make` on a *nondecreasing* list of
  values, and relate it to the "maximal minimal consecutive gap" notion. -/

  /-- Greedy `d`-separated selection of *relative* indices in `l`: scan `l` from left to
  right, taking an element whenever it is at distance at least `d` from the last taken
  value (`v` plays the role of the last taken value before the scan starts). -/
  def gposFrom (l : List ℤ) (v d : ℤ) : List ℕ :=
    match l with
    | [] => []
    | x :: xs =>
        if d ≤ x - v then 0 :: (gposFrom xs x d).map (fun i => i + 1)
        else (gposFrom xs v d).map (fun i => i + 1)

  /-- The number of elements taken by the greedy scan. -/
  def gcount (l : List ℤ) (v d : ℤ) : ℕ := (gposFrom l v d).length

  /-- The gaps between *consecutive* elements of a list of values are at least `d`. -/
  def Gapped (d : ℤ) : List ℤ → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => d ≤ b - a ∧ Gapped d (b :: rest)

  /-- Like `Gapped`, but the first gap is measured against the value `v`. -/
  def GappedFrom (v d : ℤ) : List ℤ → Prop
    | [] => True
    | a :: rest => d ≤ a - v ∧ Gapped d (a :: rest)

  /-- The values selected by the index list `pos` in `l`. -/
  def valsOf (l : List ℤ) (pos : List ℕ) : List ℤ := pos.map (fun i => l.getD i 0)

  /-- An increasing list of positions in `l` such that consecutive selected values are at
  distance at least `d` (and the first one is at distance at least `d` from `v`). -/
  def FeasibleFrom (l : List ℤ) (v d : ℤ) (pos : List ℕ) : Prop :=
    pos.Pairwise (· < ·) ∧ (∀ i ∈ pos, i < l.length) ∧ GappedFrom v d (valsOf l pos)

  theorem gapped_cons (d a : ℤ) (rest : List ℤ) :
      Gapped d (a :: rest) ↔ GappedFrom a d rest := by
    cases rest with
    | nil => simp [Gapped, GappedFrom]
    | cons b rest =>
      cases rest with
      | nil => simp [Gapped, GappedFrom]
      | cons c rest => simp [Gapped, GappedFrom]

  theorem gappedFrom_cons (v d a : ℤ) (rest : List ℤ) :
      GappedFrom v d (a :: rest) ↔ d ≤ a - v ∧ GappedFrom a d rest := by
    show d ≤ a - v ∧ Gapped d (a :: rest) ↔ d ≤ a - v ∧ GappedFrom a d rest
    cases rest with
    | nil => simp [GappedFrom, Gapped]
    | cons b rest =>
      cases rest with
      | nil => simp [GappedFrom, Gapped]
      | cons c rest => simp [GappedFrom, Gapped]

  theorem gappedFrom_anti {v v' : ℤ} (d : ℤ) (hvv : v ≤ v') :
      ∀ vs : List ℤ, GappedFrom v' d vs → GappedFrom v d vs
    | [], _ => by simp [GappedFrom]
    | a :: rest, h => by
        rw [gappedFrom_cons] at h ⊢
        exact ⟨by linarith [h.1], h.2⟩

  theorem gappedFrom_imp_gapped (v d : ℤ) :
      ∀ vs : List ℤ, GappedFrom v d vs → Gapped d vs
    | [], _ => by simp [Gapped]
    | a :: rest, h => by
        rw [gappedFrom_cons] at h
        exact (gapped_cons d a rest).mpr h.2

  theorem valsOf_cons (l : List ℤ) (p : ℕ) (rest : List ℕ) :
      valsOf l (p :: rest) = l.getD p 0 :: valsOf l rest := rfl

  theorem valsOf_shift (x : ℤ) (xs : List ℤ) :
      ∀ g : List ℕ, valsOf (x :: xs) (g.map (fun i => i + 1)) = valsOf xs g
    | [] => rfl
    | a :: rest => by
        show (x :: xs).getD (a + 1) 0 :: valsOf (x :: xs) (rest.map (fun i => i + 1))
          = xs.getD a 0 :: valsOf xs rest
        rw [List.getD_cons_succ, valsOf_shift x xs rest]

  theorem getD_cons_of_pos {x : ℤ} {xs : List ℤ} {p : ℕ} (hp : 1 ≤ p) :
      (x :: xs).getD p 0 = xs.getD (p - 1) 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getD_cons_succ]
    simp

  theorem valsOf_shiftDown (x : ℤ) (xs : List ℤ) :
      ∀ pos : List ℕ, (∀ q ∈ pos, 1 ≤ q) →
        valsOf (x :: xs) pos = valsOf xs (pos.map (fun i => i - 1))
    | [], _ => by simp [valsOf]
    | p :: rest, h => by
        have hp : 1 ≤ p := h p (by simp)
        have hr : ∀ q ∈ rest, 1 ≤ q := fun q hq => h q (by simp [hq])
        show (x :: xs).getD p 0 :: valsOf (x :: xs) rest
          = xs.getD (p - 1) 0 :: valsOf xs (rest.map (fun i => i - 1))
        rw [getD_cons_of_pos hp, valsOf_shiftDown x xs rest hr]

  theorem pairwise_map_sub_one {pos : List ℕ} (h : pos.Pairwise (· < ·))
      (h1 : ∀ q ∈ pos, 1 ≤ q) :
      (pos.map (fun i => i - 1)).Pairwise (· < ·) := by
    induction pos with
    | nil => simp
    | cons a rest ih =>
      have hlt : ∀ b ∈ rest, a < b := (List.pairwise_cons.mp h).1
      have hrest : rest.Pairwise (· < ·) := (List.pairwise_cons.mp h).2
      have hrest1 : ∀ q ∈ rest, 1 ≤ q := fun q hq => h1 q (by simp [hq])
      have ha1 : 1 ≤ a := h1 a (by simp)
      simp only [List.map_cons]
      refine List.Pairwise.cons ?_ (ih hrest hrest1)
      intro b hb
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      have h1 := hlt b0 hb0
      have h2 := hrest1 b0 hb0
      show a - 1 < b0 - 1
      omega

  theorem getD_zero_le_getD {l : List ℤ} (hl : l.Pairwise (· ≤ ·)) {q : ℕ}
      (hq : q < l.length) : l.getD 0 0 ≤ l.getD q 0 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp
    · have h0 : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le q) hq
      rw [List.getD_eq_getElem l (0 : ℤ) h0, List.getD_eq_getElem l (0 : ℤ) hq]
      exact List.pairwise_iff_getElem.mp hl 0 q h0 hq hq0

  theorem gcount_nil (v d : ℤ) : gcount [] v d = 0 := rfl

  theorem gcount_cons_of_le {x : ℤ} {xs : List ℤ} {v d : ℤ} (h : d ≤ x - v) :
      gcount (x :: xs) v d = 1 + gcount xs x d := by
    rw [gcount, gposFrom, if_pos h]
    simp [gcount, Nat.add_comm]

  theorem gcount_cons_of_not_le {x : ℤ} {xs : List ℤ} {v d : ℤ} (h : ¬ d ≤ x - v) :
      gcount (x :: xs) v d = gcount xs v d := by
    rw [gcount, gposFrom, if_neg h]
    simp [gcount]

  theorem valsOf_zero_cons (x : ℤ) (xs : List ℤ) (g : List ℕ) :
      valsOf (x :: xs) (0 :: g.map (fun i => i + 1)) = x :: valsOf xs g := by
    rw [valsOf_cons, valsOf_shift]
    simp

  theorem gposFrom_sound (l : List ℤ) (v d : ℤ) :
      FeasibleFrom l v d (gposFrom l v d) := by
    induction l generalizing v with
    | nil => exact ⟨List.Pairwise.nil, by simp [gposFrom],
        by simp [gposFrom, valsOf, GappedFrom]⟩
    | cons x xs ih =>
      have ihv := ih v
      have ihx := ih x
      by_cases h : d ≤ x - v
      · refine ⟨?_, ?_, ?_⟩
        · rw [gposFrom, if_pos h]
          refine List.Pairwise.cons ?_ (List.Pairwise.map _ (fun a b hab => by omega) ihx.1)
          intro a ha
          obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
          omega
        · intro i hi
          rw [gposFrom, if_pos h] at hi
          simp only [List.mem_cons, List.mem_map] at hi
          obtain rfl | ⟨b, hb, rfl⟩ := hi
          · simp
          · have hb' := ihx.2.1 b hb
            simp only [List.length_cons]
            omega
        · rw [gposFrom, if_pos h]
          rw [valsOf_zero_cons, gappedFrom_cons]
          exact ⟨h, ihx.2.2⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [gposFrom, if_neg h]
          exact List.Pairwise.map _ (fun a b hab => by omega) ihv.1
        · intro i hi
          rw [gposFrom, if_neg h] at hi
          simp only [List.mem_map] at hi
          obtain ⟨b, hb, rfl⟩ := hi
          have hb' := ihv.2.1 b hb
          simp only [List.length_cons]
          omega
        · rw [gposFrom, if_neg h, valsOf_shift]
          exact ihv.2.2

  /-- Optimality and monotonicity of the greedy scan, proved simultaneously by strong
  induction on the length of the value list. -/
  private theorem gpos_main (n : ℕ) :
      ∀ l : List ℤ, l.length = n → l.Pairwise (· ≤ ·) →
        (∀ v d pos, FeasibleFrom l v d pos → pos.length ≤ gcount l v d) ∧
        (∀ d x c, (∀ y ∈ l, x ≤ y) → x ≤ c → gcount l c d ≤ gcount l x d) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hl hsort
      cases l with
      | nil =>
        refine ⟨?_, ?_⟩
        · intro v d pos hf
          have hpos : pos = [] := by
            cases pos with
            | nil => rfl
            | cons p rest => exact absurd (hf.2.1 p (by simp)) (by simp)
          simp [hpos, gcount_nil]
        · intro d x c _ _
          simp [gcount_nil]
      | cons x xs =>
        have hsortx : xs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
        have hxall : ∀ y ∈ xs, x ≤ y := (List.pairwise_cons.mp hsort).1
        have hxslen : xs.length < n := by
          simp only [List.length_cons] at hl
          omega
        have hih := ih xs.length hxslen xs rfl hsortx
        have hopt := hih.1
        have hmono := hih.2
        refine ⟨?_, ?_⟩
        · intro v d pos hf
          obtain ⟨hpw, hin, hgf⟩ := hf
          cases pos with
          | nil => simp [gcount]
          | cons p rest =>
            have hple : p < xs.length + 1 := by
              have := hin p (by simp)
              simpa using this
            have hrest1 : ∀ q ∈ rest, 1 ≤ q := by
              intro q hq
              have := (List.pairwise_cons.mp hpw).1 q hq
              omega
            have hrp : rest.Pairwise (· < ·) := (List.pairwise_cons.mp hpw).2
            have hv : valsOf (x :: xs) (p :: rest)
                = (x :: xs).getD p 0 :: valsOf (x :: xs) rest := rfl
            have hgf0 : GappedFrom v d (valsOf (x :: xs) (p :: rest)) := hgf
            rw [hv, gappedFrom_cons] at hgf
            have hshift : valsOf (x :: xs) rest = valsOf xs (rest.map (fun i => i - 1)) :=
              valsOf_shiftDown x xs rest hrest1
            have hfeas : FeasibleFrom xs ((x :: xs).getD p 0) d
                (rest.map (fun i => i - 1)) := by
              refine ⟨pairwise_map_sub_one hrp hrest1, ?_, ?_⟩
              · intro q hq
                obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
                have hq1 := hin q0 (by simp [hq0])
                have hq2 := hrest1 q0 hq0
                simp only [List.length_cons] at hq1
                omega
              · rw [← hshift]
                exact hgf.2
            have h1 : rest.length ≤ gcount xs ((x :: xs).getD p 0) d := by
              have := hopt ((x :: xs).getD p 0) d (rest.map (fun i => i - 1)) hfeas
              simpa using this
            by_cases hcase : d ≤ x - v
            · rw [gcount_cons_of_le hcase]
              have h2 : gcount xs ((x :: xs).getD p 0) d ≤ gcount xs x d :=
                hmono d x _ (fun y hy => hxall y hy)
                  (getD_zero_le_getD hsort (by simpa using hple))
              simp only [List.length_cons]
              omega
            · rw [gcount_cons_of_not_le hcase]
              have hp1 : 1 ≤ p := by
                rcases Nat.eq_zero_or_pos p with hp | hp
                · subst hp
                  exact absurd (by simpa using hgf.1) hcase
                · exact hp
              have hallge : ∀ q ∈ p :: rest, 1 ≤ q := by
                intro q hq
                rcases List.mem_cons.mp hq with rfl | hq
                · exact hp1
                · exact hrest1 q hq
              have hshift2 : valsOf (x :: xs) (p :: rest)
                  = valsOf xs ((p :: rest).map (fun i => i - 1)) :=
                valsOf_shiftDown x xs (p :: rest) hallge
              have hfeas2 : FeasibleFrom xs v d ((p :: rest).map (fun i => i - 1)) := by
                refine ⟨pairwise_map_sub_one hpw hallge, ?_, ?_⟩
                · intro q hq
                  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
                  have hq1 := hin q0 (by simp [hq0])
                  have hq2 := hallge q0 (by simp [hq0])
                  simp only [List.length_cons] at hq1
                  omega
                · rw [← hshift2]
                  exact hgf0
              have := hopt v d ((p :: rest).map (fun i => i - 1)) hfeas2
              simpa using this
        · intro d x0 c hx0 hxc
          have hx0x : x0 ≤ x := hx0 x (by simp)
          by_cases hcase : d ≤ x - x0
          · rw [gcount_cons_of_le hcase]
            by_cases hc : d ≤ x - c
            · rw [gcount_cons_of_le hc]
            · rw [gcount_cons_of_not_le hc]
              have hgc : gcount xs c d = (gposFrom xs c d).length := rfl
              rw [hgc]
              cases hg : gposFrom xs c d with
              | nil => simp only [List.length_nil]; omega
              | cons q rest' =>
                have hsound : FeasibleFrom xs c d (q :: rest') := by
                  exact hg ▸ gposFrom_sound xs c d
                have hgf' : GappedFrom c d (valsOf xs (q :: rest')) := hsound.2.2
                rw [valsOf_cons, gappedFrom_cons] at hgf'
                have hq : q < xs.length := hsound.2.1 q (by simp)
                have hxin : x ≤ xs.getD q 0 := by
                  have h := getD_zero_le_getD hsort (l := x :: xs) (q := q + 1) (by
                    simp only [List.length_cons]; omega)
                  simpa using h
                have htail : FeasibleFrom xs (xs.getD q 0) d rest' := by
                  refine ⟨?_, ?_, hgf'.2⟩
                  · exact (List.pairwise_cons.mp hsound.1).2
                  · intro i hi
                    exact hsound.2.1 i (by simp [hi])
                have h1 := hopt (xs.getD q 0) d rest' htail
                have h2 : gcount xs (xs.getD q 0) d ≤ gcount xs x d :=
                  hmono d x _ (fun y hy => hxall y hy) hxin
                simp only [List.length_cons]
                omega
          · rw [gcount_cons_of_not_le hcase]
            have hcx : ¬ d ≤ x - c := by omega
            rw [gcount_cons_of_not_le hcx]
            exact hmono d x0 c (fun y hy => hx0 y (by simp [hy])) hxc

  theorem gcount_optimal {l : List ℤ} (hl : l.Pairwise (· ≤ ·)) (v d : ℤ) (pos : List ℕ)
      (h : FeasibleFrom l v d pos) : pos.length ≤ gcount l v d :=
    (gpos_main l.length l rfl hl).1 v d pos h

  theorem gcount_mono {l : List ℤ} (hl : l.Pairwise (· ≤ ·)) (d x c : ℤ)
      (hx : ∀ y ∈ l, x ≤ y) (hxc : x ≤ c) : gcount l c d ≤ gcount l x d :=
    (gpos_main l.length l rfl hl).2 d x c hx hxc

  /-- Start-free feasibility: an increasing list of positions in `l` whose selected values
  have consecutive gaps at least `d`. -/
  def Feasible (l : List ℤ) (d : ℤ) (pos : List ℕ) : Prop :=
    pos.Pairwise (· < ·) ∧ (∀ i ∈ pos, i < l.length) ∧ Gapped d (valsOf l pos)

  /-- Set formulation of "there are `k` positions in `l` whose consecutive gaps are all at
  least `d`" (matching `consecutiveGaps`). -/
  def FeasibleSet (l : List ℤ) (k : ℕ) (d : ℤ) : Prop :=
    ∃ S : Finset ℕ, S ⊆ Finset.range l.length ∧ S.card = k ∧
      (consecutiveGaps l S).Nonempty ∧ ∀ g ∈ consecutiveGaps l S, d ≤ g

  theorem getD_le_getD_of_le {l : List ℤ} (hsort : l.Pairwise (· ≤ ·)) {a b : ℕ}
      (hab : a ≤ b) (hb : b < l.length) : l.getD a 0 ≤ l.getD b 0 := by
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · have ha : a < l.length := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hb)
      rw [List.getD_eq_getElem l (0 : ℤ) ha, List.getD_eq_getElem l (0 : ℤ) hb]
      exact List.pairwise_iff_getElem.mp hsort a b ha hb hlt

  theorem gapped_iff (d : ℤ) :
      ∀ vs : List ℤ, Gapped d vs ↔
        ∀ (t : ℕ) (h : t + 1 < vs.length), d ≤ vs[t + 1] - vs[t] := by
    intro vs
    induction vs with
    | nil => simp [Gapped]
    | cons a rest ih =>
      cases rest with
      | nil => simp [Gapped]
      | cons b rest =>
        have hgoal : Gapped d (a :: b :: rest) ↔ (d ≤ b - a ∧ Gapped d (b :: rest)) :=
          gapped_cons d a (b :: rest)
        rw [hgoal, ih]
        constructor
        · rintro ⟨h0, hrest⟩ t ht
          cases t with
          | zero =>
            simpa using h0
          | succ s =>
            have hlt : s + 1 < (b :: rest).length := by
              simp only [List.length_cons] at ht ⊢
              omega
            have hlt2 : s + 1 + 1 < (a :: b :: rest).length := ht
            have hlt3 : s + 1 < (a :: b :: rest).length := by
              simp only [List.length_cons] at hlt ⊢
              omega
            have h1 : (a :: b :: rest)[s + 1 + 1] = (b :: rest)[s + 1] :=
              List.getElem_cons_succ _ _ _ hlt2
            have h2 : (a :: b :: rest)[s + 1] = (b :: rest)[s] :=
              List.getElem_cons_succ _ _ _ hlt3
            rw [h1, h2]
            exact hrest s hlt
        · intro hall
          refine ⟨?_, ?_⟩
          · have := hall 0 (by simp)
            simpa using this
          · intro t ht
            have ht' : t + 1 + 1 < (a :: b :: rest).length := by
              simp only [List.length_cons] at ht ⊢
              omega
            have ht'' : t + 1 < (a :: b :: rest).length := by
              simp only [List.length_cons] at ht ⊢
              omega
            have := hall (t + 1) ht'
            have h1 : (a :: b :: rest)[t + 1 + 1] = (b :: rest)[t + 1] :=
              List.getElem_cons_succ _ _ _ ht'
            have h2 : (a :: b :: rest)[t + 1] = (b :: rest)[t] :=
              List.getElem_cons_succ _ _ _ ht''
            rw [h1, h2] at this
            exact this

  theorem gapped_take (d : ℤ) {vs : List ℤ} (h : Gapped d vs) (n : ℕ) :
      Gapped d (vs.take n) := by
    rw [gapped_iff] at h ⊢
    intro t ht
    have hle : (vs.take n).length ≤ vs.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    have ht' : t + 1 < vs.length := by omega
    rw [List.getElem_take, List.getElem_take]
    exact h t ht'

  theorem feasibleSet_le_spread {l : List ℤ} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ}
      (hkl : k ≤ l.length) {d : ℤ} (h : FeasibleSet l k d) :
      d ≤ l.getD (l.length - 1) 0 - l.getD 0 0 := by
    obtain ⟨S, hS, hcard, hne, hgap⟩ := h
    obtain ⟨g, hg⟩ := hne
    have h1 : d ≤ g := hgap g hg
    rw [consecutiveGaps] at hg
    obtain ⟨p, hp, hgp⟩ := Finset.mem_image.mp hg
    obtain ⟨hpprod, hij, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hiS, hjS⟩ := Finset.mem_product.mp hpprod
    obtain ⟨i, j⟩ := p
    simp only [Prod.fst, Prod.snd] at hgp hij
    have hiR : i < l.length := Finset.mem_range.mp (hS hiS)
    have hjR : j < l.length := Finset.mem_range.mp (hS hjS)
    have h2 : l.getD j 0 ≤ l.getD (l.length - 1) 0 := by
      refine getD_le_getD_of_le hsort (by omega) (by omega)
    have h3 : l.getD 0 0 ≤ l.getD i 0 := getD_le_getD_of_le hsort (by omega) hiR
    have h4 : l.getD j 0 - l.getD i 0 ≤ l.getD (l.length - 1) 0 - l.getD 0 0 := by omega
    rw [← hgp] at h1
    omega

  /-! ### Auxiliary lemmas for the correspondence between positions and selections -/

  /-- In a `Gapped` list the difference of two consecutive elements is at least `d`. -/
  private theorem gapped_nth {d : ℤ} (vs : List ℤ) (h : Gapped d vs) :
      ∀ t : ℕ, t + 1 < vs.length → d ≤ vs.getD (t + 1) 0 - vs.getD t 0 := by
    induction vs with
    | nil =>
      intro t ht
      simp at ht
    | cons a rest ih =>
      cases rest with
      | nil =>
        intro t ht
        simp at ht
      | cons b rest' =>
        intro t ht
        cases t with
        | zero => simpa [List.getD_cons_succ, List.getD_cons_zero] using h.1
        | succ t =>
          have h2 := ih h.2 t (by simp only [List.length_cons] at ht ⊢; omega)
          simpa [List.getD_cons_succ] using h2

  /-- A value list whose consecutive differences are at least `d` is `Gapped`. -/
  private theorem gapped_of_nth {d : ℤ} (vs : List ℤ)
      (h : ∀ t : ℕ, t + 1 < vs.length → d ≤ vs.getD (t + 1) 0 - vs.getD t 0) :
      Gapped d vs := by
    induction vs with
    | nil => simp [Gapped]
    | cons a rest ih =>
      cases rest with
      | nil => simp [Gapped]
      | cons b rest' =>
        refine ⟨?_, ?_⟩
        · simpa [List.getD_cons_succ, List.getD_cons_zero] using h 0 (by simp)
        · exact ih (fun t ht => by
            have hh := h (t + 1) (by simp only [List.length_cons] at ht ⊢; omega)
            simpa [List.getD_cons_succ] using hh)

  private theorem valsOf_length (l : List ℤ) (pos : List ℕ) :
      (valsOf l pos).length = pos.length := by
    simp [valsOf]

  /-- The value selected at relative index `t`. -/
  private theorem valsOf_getD (l : List ℤ) (pos : List ℕ) :
      ∀ t : ℕ, t < pos.length → (valsOf l pos).getD t 0 = l.getD (pos.getD t 0) 0 := by
    induction pos with
    | nil =>
      intro t ht
      simp at ht
    | cons p rest ih =>
      intro t ht
      cases t with
      | zero => simp [valsOf]
      | succ t =>
        have ht' : t < rest.length := by simp only [List.length_cons] at ht; omega
        simp only [valsOf_cons, List.getD_cons_succ]
        exact ih t ht'

  /-- A strictly increasing index list is strictly increasing for `getD`. -/
  private theorem getD_lt_mono {pos : List ℕ} (hpw : pos.Pairwise (· < ·)) :
      ∀ a b : ℕ, a < pos.length → b < pos.length → a < b → pos.getD a 0 < pos.getD b 0 := by
    have hmono := List.pairwise_iff_getElem.mp hpw
    intro a b ha hb hab
    rw [List.getD_eq_getElem pos 0 ha, List.getD_eq_getElem pos 0 hb]
    exact hmono a b ha hb hab

  /-- Order reflection for a strictly increasing index list. -/
  private theorem getD_lt_of_getD_lt {pos : List ℕ}
      (hmono : ∀ a b : ℕ, a < pos.length → b < pos.length → a < b →
        pos.getD a 0 < pos.getD b 0)
      {u v : ℕ} (hu : u < pos.length) (hv : v < pos.length)
      (h : pos.getD u 0 < pos.getD v 0) : u < v := by
    rcases lt_trichotomy u v with h1 | h1 | h1
    · exact h1
    · subst h1
      exact absurd h (lt_irrefl _)
    · exact absurd (hmono v u hv hu h1) (by omega)

  /-- Membership in `consecutiveGaps`, made explicit. -/
  private theorem mem_consecutiveGaps {l : List ℤ} {S : Finset ℕ} {g : ℤ} :
      g ∈ consecutiveGaps l S ↔
        ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ m ∈ S, ¬ (a < m ∧ m < b)) ∧
          g = l.getD b 0 - l.getD a 0 := by
    unfold consecutiveGaps
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hp, heq⟩
      rw [Finset.mem_filter] at hp
      obtain ⟨hprod, hlt, hbtw⟩ := hp
      have hmem2 : a ∈ S ∧ b ∈ S := by simpa using hprod
      exact ⟨a, hmem2.1, b, hmem2.2, hlt, hbtw, heq.symm⟩
    · rintro ⟨a, ha, b, hb, hlt, hbtw, rfl⟩
      refine ⟨(a, b), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨by simpa using (show (a, b) ∈ S ×ˢ S from Finset.mem_product.mpr ⟨ha, hb⟩),
        hlt, hbtw⟩

  /-- A set with at least two elements has two "adjacent" elements. -/
  private theorem exists_adjacent {S : Finset ℕ} (h : 2 ≤ S.card) :
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ ∀ m ∈ S, ¬ (a < m ∧ m < b) := by
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set a := S.min' hne with ha
    have haS : a ∈ S := by rw [ha]; exact Finset.min'_mem S hne
    have hcard : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem haS
    have hT : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
    set b := (S.erase a).min' hT with hb
    have hbT : b ∈ S.erase a := by rw [hb]; exact Finset.min'_mem _ hT
    have hbS : b ∈ S := Finset.mem_of_mem_erase hbT
    have hlt : a < b := by
      have h1 : a ≤ b := by rw [ha]; exact Finset.min'_le S b hbS
      have h2 : b ≠ a := (Finset.mem_erase.mp hbT).1
      omega
    refine ⟨a, haS, b, hbS, hlt, fun m hm hc => ?_⟩
    have hmT : m ∈ S.erase a := Finset.mem_erase.mpr ⟨by omega, hm⟩
    have h1 : b ≤ m := by rw [hb]; exact Finset.min'_le _ m hmT
    omega

  theorem FeasibleSet_mono {l : List ℤ} {k : ℕ} {d d' : ℤ} (hdd : d' ≤ d)
      (h : FeasibleSet l k d) : FeasibleSet l k d' := by
    obtain ⟨S, hsub, hcard, hne, hall⟩ := h
    exact ⟨S, hsub, hcard, hne, fun g hg => le_trans hdd (hall g hg)⟩

  theorem consecutiveGaps_nonempty_of_card {l : List ℤ} {S : Finset ℕ} (h : 2 ≤ S.card) :
      (consecutiveGaps l S).Nonempty := by
    obtain ⟨a, haS, b, hbS, hlt, hbtw⟩ := exists_adjacent h
    exact ⟨l.getD b 0 - l.getD a 0, mem_consecutiveGaps.mpr ⟨a, haS, b, hbS, hlt, hbtw, rfl⟩⟩

  /-- A feasible position list gives a feasible selection set. -/
  theorem FeasibleSet_of_feasible {l : List ℤ} {k : ℕ} {d : ℤ} (hk : 2 ≤ k) {pos : List ℕ}
      (h : Feasible l d pos) (hlen : pos.length = k) : FeasibleSet l k d := by
    obtain ⟨hpw, hin, hgap⟩ := h
    have hnodup : pos.Nodup := hpw.nodup
    have hmono := getD_lt_mono hpw
    refine ⟨pos.toFinset, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_range]
      exact hin a (List.mem_toFinset.mp ha)
    · rw [List.toFinset_card_of_nodup hnodup, hlen]
    · apply consecutiveGaps_nonempty_of_card
      rw [List.toFinset_card_of_nodup hnodup, hlen]
      exact hk
    · intro g hg
      obtain ⟨a, haS, b, hbS, hlt, hbtw, rfl⟩ := mem_consecutiveGaps.mp hg
      have ha : a ∈ pos := List.mem_toFinset.mp haS
      have hb : b ∈ pos := List.mem_toFinset.mp hbS
      obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
      obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
      have hlt' : pos.getD i 0 < pos.getD j 0 := by
        rw [List.getD_eq_getElem pos 0 hi, List.getD_eq_getElem pos 0 hj, hia, hjb]
        exact hlt
      have hij : i < j := getD_lt_of_getD_lt hmono hi hj hlt'
      have hji : j = i + 1 := by
        by_contra hcon
        have h2 : i + 1 < j := by omega
        have hi1 : i + 1 < pos.length := by omega
        have hmid : pos.getD (i + 1) 0 ∈ pos.toFinset := by
          rw [List.getD_eq_getElem pos 0 hi1]
          exact List.mem_toFinset.mpr (List.getElem_mem hi1)
        refine hbtw (pos.getD (i + 1) 0) hmid ⟨?_, ?_⟩
        · have h1 : pos.getD i 0 < pos.getD (i + 1) 0 := hmono i (i + 1) hi hi1 (by omega)
          rw [List.getD_eq_getElem pos 0 hi, hia] at h1
          exact h1
        · have h1 : pos.getD (i + 1) 0 < pos.getD j 0 := hmono (i + 1) j hi1 hj h2
          rw [List.getD_eq_getElem pos 0 hj, hjb] at h1
          exact h1
      have ht : i + 1 < (valsOf l pos).length := by
        rw [valsOf_length]
        omega
      have hbnd := gapped_nth (valsOf l pos) hgap i ht
      have e1 := valsOf_getD l pos (i + 1) (by omega)
      have e2 := valsOf_getD l pos i hi
      rw [e1, e2] at hbnd
      have e3 : pos.getD (i + 1) 0 = b := by
        rw [← hji, List.getD_eq_getElem pos 0 hj, hjb]
      have e4 : pos.getD i 0 = a := by
        rw [List.getD_eq_getElem pos 0 hi, hia]
      rw [e3, e4] at hbnd
      exact hbnd

  /-- A feasible selection set gives a feasible position list of the same length. -/
  theorem feasible_of_FeasibleSet {l : List ℤ} {k : ℕ} {d : ℤ} (h : FeasibleSet l k d) :
      ∃ pos : List ℕ, Feasible l d pos ∧ pos.length = k := by
    obtain ⟨S, hSsub, hScard, hSne, hgall⟩ := h
    have hpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hle :=
        List.pairwise_iff_getElem.mp (Finset.pairwise_sort S (· ≤ ·)) i j hi hj hij
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hcon : i = j :=
        ((Finset.sort_nodup S (· ≤ ·)).getElem_inj (hi := hi) (hj := hj)).mp heq
      omega
    have hmono := getD_lt_mono hpair
    refine ⟨S.sort (· ≤ ·), ⟨hpair, ?_, ?_⟩, ?_⟩
    · intro a ha
      have haS : a ∈ S := (Finset.mem_sort (· ≤ ·)).mp ha
      simpa using hSsub haS
    · apply gapped_of_nth
      intro t ht
      have htlong : t + 1 < (S.sort (· ≤ ·)).length := by
        rw [valsOf_length] at ht
        exact ht
      have htpos : t < (S.sort (· ≤ ·)).length := by omega
      have hpS : (S.sort (· ≤ ·)).getD t 0 ∈ S := by
        rw [List.getD_eq_getElem (S.sort (· ≤ ·)) 0 htpos]
        exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem htpos)
      have hqS : (S.sort (· ≤ ·)).getD (t + 1) 0 ∈ S := by
        rw [List.getD_eq_getElem (S.sort (· ≤ ·)) 0 htlong]
        exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem htlong)
      have hpq : (S.sort (· ≤ ·)).getD t 0 < (S.sort (· ≤ ·)).getD (t + 1) 0 :=
        hmono t (t + 1) htpos htlong (by omega)
      have hbtw : ∀ m ∈ S,
          ¬ ((S.sort (· ≤ ·)).getD t 0 < m ∧ m < (S.sort (· ≤ ·)).getD (t + 1) 0) := by
        intro m hm hc
        obtain ⟨h1, h2⟩ := hc
        have hm' : m ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hm
        obtain ⟨u, hu, hum⟩ := List.getElem_of_mem hm'
        have hum' : (S.sort (· ≤ ·)).getD u 0 = m := by
          rw [List.getD_eq_getElem (S.sort (· ≤ ·)) 0 hu]
          exact hum
        have h1' : (S.sort (· ≤ ·)).getD t 0 < (S.sort (· ≤ ·)).getD u 0 := by
          rw [hum']
          exact h1
        have h2' : (S.sort (· ≤ ·)).getD u 0 < (S.sort (· ≤ ·)).getD (t + 1) 0 := by
          rw [hum']
          exact h2
        have htu : t < u := getD_lt_of_getD_lt hmono htpos hu h1'
        have hut : u < t + 1 := getD_lt_of_getD_lt hmono hu htlong h2'
        omega
      have hmem : l.getD ((S.sort (· ≤ ·)).getD (t + 1) 0) 0
          - l.getD ((S.sort (· ≤ ·)).getD t 0) 0 ∈ consecutiveGaps l S :=
        mem_consecutiveGaps.mpr ⟨_, hpS, _, hqS, hpq, hbtw, rfl⟩
      have hb := hgall _ hmem
      have e1 := valsOf_getD l (S.sort (· ≤ ·)) (t + 1) htlong
      have e2 := valsOf_getD l (S.sort (· ≤ ·)) t htpos
      rw [e1, e2]
      exact hb
    · rw [Finset.length_sort (· ≤ ·), hScard]

  /-- `maxMinConsecutiveGap` is the greatest feasible threshold. -/
  theorem maxMinConsecutiveGap_spec {l : List ℤ} {k : ℕ} (hk2 : 2 ≤ k) (hkl : k ≤ l.length) :
      FeasibleSet l k (maxMinConsecutiveGap l k) ∧
        ∀ d : ℤ, FeasibleSet l k d → d ≤ maxMinConsecutiveGap l k := by
    have hne : (kSelections l k).Nonempty := by
      obtain ⟨S, hsub, hcard⟩ :=
        Finset.exists_subset_card_eq (s := Finset.range l.length) (n := k) (by simpa using hkl)
      exact ⟨S, by
        rw [kSelections, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hsub, hcard⟩⟩
    have hM : ((kSelections l k).image (minConsecutiveGap l)).Nonempty :=
      Finset.Nonempty.image hne _
    have hmax : maxMinConsecutiveGap l k =
        ((kSelections l k).image (minConsecutiveGap l)).max' hM := by
      rw [maxMinConsecutiveGap, dif_pos hne]
    constructor
    · obtain ⟨S0, hS0mem, hS0eq⟩ :=
        Finset.mem_image.mp (Finset.max'_mem ((kSelections l k).image (minConsecutiveGap l)) hM)
      rw [kSelections, Finset.mem_filter, Finset.mem_powerset] at hS0mem
      obtain ⟨hS0sub, hS0card⟩ := hS0mem
      have hS0ne : (consecutiveGaps l S0).Nonempty :=
        consecutiveGaps_nonempty_of_card (by omega)
      have hmin : minConsecutiveGap l S0 = (consecutiveGaps l S0).min' hS0ne := by
        rw [minConsecutiveGap, dif_pos hS0ne]
      refine ⟨S0, hS0sub, hS0card, hS0ne, ?_⟩
      intro g hg
      rw [hmax, ← hS0eq, hmin]
      exact Finset.min'_le _ g hg
    · intro d hd
      obtain ⟨S, hsub, hcard, hSne, hgall⟩ := hd
      have hSmem : S ∈ kSelections l k := by
        rw [kSelections, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hsub, hcard⟩
      have himg : minConsecutiveGap l S ∈ (kSelections l k).image (minConsecutiveGap l) :=
        Finset.mem_image.mpr ⟨S, hSmem, rfl⟩
      have h2 : minConsecutiveGap l S ≤
          ((kSelections l k).image (minConsecutiveGap l)).max' hM :=
        Finset.le_max' ((kSelections l k).image (minConsecutiveGap l))
          (minConsecutiveGap l S) himg
      have hmin : minConsecutiveGap l S = (consecutiveGaps l S).min' hSne := by
        rw [minConsecutiveGap, dif_pos hSne]
      have h4 : d ≤ (consecutiveGaps l S).min' hSne := Finset.le_min' _ hSne d hgall
      rw [hmax]
      exact le_trans h4 (hmin ▸ h2)

  /-! ### Filling the array: `maximum_tastiness_loop0` -/

  /-- A feasible position list is also feasible when the "previous value" is set below the
  smallest value of the list. -/
  theorem feasibleFrom_of_feasible {l : List ℤ} (hsort : l.Pairwise (· ≤ ·)) {d : ℤ}
      {pos : List ℕ} (h : Feasible l d pos) (hne : pos ≠ []) :
      FeasibleFrom l (l.getD 0 0 - d) d pos := by
    obtain ⟨hpw, hin, hgap⟩ := h
    cases pos with
    | nil => exact absurd rfl hne
    | cons p rest =>
      have hp : p < l.length := hin p (by simp)
      have hhead : l.getD 0 0 ≤ l.getD p 0 := getD_zero_le_getD hsort hp
      refine ⟨hpw, hin, ?_⟩
      rw [valsOf_cons, gapped_cons] at hgap
      rw [valsOf_cons, gappedFrom_cons]
      exact ⟨by linarith, hgap⟩

  /-- The greedy scan from the first element picks `k` elements exactly when `k` positions
  with all consecutive gaps at least `d` exist. -/
  theorem feasibleSet_iff_gcount {l : List ℤ} {k : ℕ} (hsort : l.Pairwise (· ≤ ·))
      (hk : 2 ≤ k) (hkl : k ≤ l.length) {d : ℤ} :
      FeasibleSet l k d ↔ (k : ℤ) ≤ (1 : ℤ) + ((gcount (l.drop 1) (l.getD 0 0) d : ℕ) : ℤ) := by
    obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
      cases l with
      | nil => simp at hkl; omega
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hsortx : xs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
    have hxall : ∀ y ∈ xs, x ≤ y := (List.pairwise_cons.mp hsort).1
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have hdrop : (x :: xs).drop 1 = xs := rfl
    have hgd : (x :: xs).getD 0 0 = x := rfl
    rw [hdrop, hgd]
    constructor
    · intro hf
      obtain ⟨pos, hfeas, hposlen⟩ := feasible_of_FeasibleSet hf
      have hne : pos ≠ [] := by
        intro hp
        rw [hp] at hposlen
        simp at hposlen
        omega
      have hff := feasibleFrom_of_feasible hsort hfeas hne
      have hopt := gcount_optimal hsort (x - d) d pos hff
      have hg : gcount (x :: xs) (x - d) d = 1 + gcount xs x d := by
        refine gcount_cons_of_le ?_
        linarith
      rw [hg] at hopt
      rw [hposlen] at hopt
      have : (k : ℤ) ≤ ((1 + gcount xs x d : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        omega
      simpa using this
    · intro hge
      have hG : gposFrom (x :: xs) (x - d) d = 0 :: (gposFrom xs x d).map (fun i => i + 1) := by
        rw [gposFrom, if_pos (by show d ≤ x - (x - d); linarith)]
      have hsound := gposFrom_sound (x :: xs) (x - d) d
      rw [hG] at hsound
      have hlenG : (0 :: (gposFrom xs x d).map (fun i => i + 1)).length
          = 1 + gcount xs x d := by
        simp only [List.length_cons, List.length_map, gcount]
        omega
      have hfeas : Feasible (x :: xs) d (0 :: (gposFrom xs x d).map (fun i => i + 1)) :=
        ⟨hsound.1, hsound.2.1, gappedFrom_imp_gapped _ _ _ hsound.2.2⟩
      have htake : Feasible (x :: xs) d
          ((0 :: (gposFrom xs x d).map (fun i => i + 1)).take k) := by
        refine ⟨List.Pairwise.take hfeas.1, ?_, ?_⟩
        · intro i hi
          exact hfeas.2.1 i (List.mem_of_mem_take hi)
        · rw [valsOf, List.map_take]
          exact gapped_take d hfeas.2.2 k
      have htake_len : ((0 :: (gposFrom xs x d).map (fun i => i + 1)).take k).length = k := by
        rw [List.length_take, hlenG, Nat.min_eq_left]
        have : (k : ℤ) ≤ 1 + (gcount xs x d : ℤ) := by simpa using hge
        omega
      exact FeasibleSet_of_feasible hk htake htake_len

  theorem usize_max_ge : 1000000 ≤ Std.Usize.max := by
    rcases Std.Usize.bounds_eq with h | h <;> rw [h] <;>
      norm_num [Std.U32.max_eq, Std.U64.max_eq]

  theorem i64_sub_eq {x y : Std.I64} (h1 : Std.I64.min ≤ x.val - y.val)
      (h2 : x.val - y.val ≤ Std.I64.max) :
      ∃ z : Std.I64, x - y = ok z ∧ z.val = x.val - y.val := by
    have hin : Std.IScalar.inBounds .I64 (x.val - y.val) := by
      simp only [Std.IScalar.inBounds, Std.IScalarTy.I64_numBits_eq, Std.I64.min_eq,
        Std.I64.max_eq] at h1 h2 ⊢
      constructor <;> omega
    have hcb : Std.IScalar.check_bounds .I64 (x.val - y.val) = true :=
      (Std.IScalar.check_bounds_eq_inBounds .I64 (x.val - y.val)).mpr hin
    refine ⟨Std.I64.ofIntCore (x.val - y.val) hin, ?_, Std.I64.ofInt_val_eq hin⟩
    show Std.IScalar.sub x y = ok (Std.I64.ofIntCore (x.val - y.val) hin)
    rw [Std.IScalar.sub, Std.IScalar.tryMk, Std.IScalar.tryMkOpt, dif_pos hcb]
    rfl

  theorem i64_add_eq {x y : Std.I64} (h1 : Std.I64.min ≤ x.val + y.val)
      (h2 : x.val + y.val ≤ Std.I64.max) :
      ∃ z : Std.I64, x + y = ok z ∧ z.val = x.val + y.val := by
    have hin : Std.IScalar.inBounds .I64 (x.val + y.val) := by
      simp only [Std.IScalar.inBounds, Std.IScalarTy.I64_numBits_eq, Std.I64.min_eq,
        Std.I64.max_eq] at h1 h2 ⊢
      constructor <;> omega
    have hcb : Std.IScalar.check_bounds .I64 (x.val + y.val) = true :=
      (Std.IScalar.check_bounds_eq_inBounds .I64 (x.val + y.val)).mpr hin
    refine ⟨Std.I64.ofIntCore (x.val + y.val) hin, ?_, Std.I64.ofInt_val_eq hin⟩
    show Std.IScalar.add x y = ok (Std.I64.ofIntCore (x.val + y.val) hin)
    rw [Std.IScalar.add, Std.IScalar.tryMk, Std.IScalar.tryMkOpt, dif_pos hcb]
    rfl

  theorem i64_div_eq {x y : Std.I64} (hz : y.val ≠ 0)
      (hno : ¬ (x.val = Std.I64.min ∧ y.val = -1)) :
      ∃ z : Std.I64, x / y = ok z ∧ z.val = x.val.tdiv y.val := by
    have hno' : ¬ (x.val = Std.IScalar.min .I64 ∧ y.val = -1) := by
      simpa [Std.I64.min, Std.I64.numBits, Std.IScalar.min, Std.IScalarTy.I64_numBits_eq]
        using hno
    obtain ⟨z, hz', hzv, -⟩ := Std.IScalar.div_bv_spec (x := x) (y := y) hz hno'
    exact ⟨z, hz', hzv⟩

  theorem usize_add_eq {x y : Std.Usize}
      (h : x.val + y.val < 2 ^ Std.UScalarTy.Usize.numBits) :
      ∃ z : Std.Usize, x + y = ok z ∧ z.val = x.val + y.val := by
    have hcb : Std.UScalar.check_bounds .Usize (x.val + y.val) = true :=
      (Std.UScalar.check_bounds_eq_inBounds .Usize (x.val + y.val)).mpr h
    refine ⟨Std.Usize.ofNatCore (x.val + y.val) h, ?_, Std.Usize.ofNatCore_val_eq h⟩
    show Std.UScalar.add x y = ok (Std.Usize.ofNatCore (x.val + y.val) h)
    rw [Std.UScalar.add, Std.UScalar.tryMk, Std.UScalar.tryMkOpt, dif_pos hcb]
    rfl

  theorem usize_sub_eq {x y : Std.Usize} (h : y.val ≤ x.val) :
      ∃ z : Std.Usize, x - y = ok z ∧ z.val = x.val - y.val := by
    have hlt : ¬ (x.val < y.val) := by omega
    refine ⟨⟨BitVec.ofNat Std.UScalarTy.Usize.numBits (x.val - y.val)⟩, ?_, ?_⟩
    · show Std.UScalar.sub x y
        = ok ⟨BitVec.ofNat Std.UScalarTy.Usize.numBits (x.val - y.val)⟩
      rw [Std.UScalar.sub]
      simp only [hlt, if_false]
    · show (BitVec.ofNat Std.UScalarTy.Usize.numBits (x.val - y.val)).toNat = x.val - y.val
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have hb := Std.UScalar.hBounds x
      have : 0 < 2 ^ Std.UScalarTy.Usize.numBits := by positivity
      omega

  theorem vec_push_spec {α : Type} (v : alloc.vec.Vec α) (x : α)
      (h : v.val.length < Std.Usize.max) :
      ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val = v.val ++ [x] := by
    have hle : v.val.length + 1 ≤ Std.Usize.max := by omega
    have hlen : (v.val ++ [x]).length ≤ Std.Usize.max := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hcond : (decide (v.val.length + 1 ≤ Std.U32.max) ||
        decide (v.val.length + 1 ≤ Std.Usize.max)) = true := by
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact hle
    refine ⟨alloc.vec.Vec.from (v.val ++ [x]) hlen, ?_, ?_⟩
    · unfold alloc.vec.Vec.push
      dsimp only
      rw [dif_pos hcond]
      simp only [List.concat_eq_append]
    · rw [alloc.vec.Vec.from_val]

  theorem index_usize_eq (price : Slice Std.I64) (i : Std.Usize) (h : i.val < price.length) :
      Slice.index_usize price i = ok (price.val[i.val]'h) := by
    have h1 : price[i]? = some price.val[i.val] := by
      rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h]
    simp only [Slice.index_usize, h1]

  theorem loop0_stop (price : Slice Std.I64) (v : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (h : price.length ≤ i.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price) v i = ok v := by
    have hc : ¬ (i < Slice.len price) := by
      show ¬ (i.val < (Slice.len price).val)
      rw [Slice.len_val]
      omega
    conv_lhs => rw [Aegis.MaximumTastiness.maximum_tastiness_loop0, Std.loop.eq_def]
    dsimp only
    rw [Aegis.MaximumTastiness.maximum_tastiness_loop0.body]
    rw [if_neg hc]
    simp

  theorem loop0_step (price : Slice Std.I64) (v : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (h : i.val < price.length) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price) v i =
        (do let x ← Slice.index_usize price i
            let v1 ← alloc.vec.Vec.push v x
            let i2 ← i + 1#usize
            Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price) v1 i2) := by
    have hc : i < Slice.len price := by
      show i.val < (Slice.len price).val
      rw [Slice.len_val]
      exact h
    conv_lhs => rw [Aegis.MaximumTastiness.maximum_tastiness_loop0, Std.loop.eq_def]
    dsimp only
    rw [Aegis.MaximumTastiness.maximum_tastiness_loop0.body]
    rw [if_pos hc]
    simp
    rfl

  theorem loop0_spec (price : Slice Std.I64) (hL : price.length < Std.Usize.max) (m : ℕ) :
      ∀ (i : Std.Usize) (v : alloc.vec.Vec Std.I64),
        price.length - i.val ≤ m → i.val ≤ price.length →
        v.val = price.val.take i.val →
        ∃ v', Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price) v i = ok v' ∧
          v'.val = price.val := by
    induction m with
    | zero =>
      intro i v hm hi hv
      have hieq : i.val = price.length := by omega
      refine ⟨v, loop0_stop price v i (by omega), ?_⟩
      rw [hv, hieq, List.take_of_length_le (le_refl _)]
    | succ m ih =>
      intro i v hm hi hv
      by_cases hlt : i.val < price.length
      · have hlen : v.val.length < Std.Usize.max := by
          rw [hv]
          have h1 : (price.val.take i.val).length ≤ price.length := by
            rw [List.length_take]
            exact Nat.min_le_right _ _
          omega
        obtain ⟨v1, hv1, hv1val⟩ := vec_push_spec v (price.val[i.val]'hlt) hlen
        obtain ⟨i2, hi2eq, hi2val⟩ := usize_add_eq (x := i) (y := 1#usize) (by
          have h2 : i.val < Std.Usize.max := by omega
          rw [Std.Usize.max, Std.Usize.numBits] at h2
          show i.val + 1 < 2 ^ Std.UScalarTy.Usize.numBits
          omega)
        have hi2' : i2.val = i.val + 1 := by
          rw [hi2val]
          rfl
        rw [loop0_step price v i hlt, hi2eq, index_usize_eq price i hlt]
        simp
        rw [hv1]
        simp
        refine ih i2 v1 ?_ ?_ ?_
        · rw [hi2']; omega
        · rw [hi2']; omega
        · rw [hv1val, hv, hi2']
          exact List.take_concat_get' price.val i.val hlt
      · have hle : price.length ≤ i.val := by omega
        refine ⟨v, loop0_stop price v i hle, ?_⟩
        rw [hv, List.take_of_length_le (by omega)]

  /-! ### Insertion sort (`AegisShim.sortList`) -/

  /-- Inserting a value into a nondecreasing list yields a nondecreasing list that is a
  permutation of the value consed onto the input. -/
  theorem sortInsert_spec (x : Std.I64) :
      ∀ l : List Std.I64, l.Pairwise (fun a b => a.val ≤ b.val) →
        ∃ l', AegisShim.sortInsert Std.core.cmp.OrdI64.cmp x l = ok l' ∧
          l'.Perm (x :: l) ∧ l'.Pairwise (fun a b => a.val ≤ b.val) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨[x], ?_, ?_, ?_⟩
      · simp [AegisShim.sortInsert]
      · exact List.Perm.refl _
      · exact List.Pairwise.cons (by simp) List.Pairwise.nil
    | cons y ys ih =>
      intro hsort
      have hys : ys.Pairwise (fun a b => a.val ≤ b.val) := (List.pairwise_cons.mp hsort).2
      have hyall : ∀ a ∈ ys, y.val ≤ a.val := (List.pairwise_cons.mp hsort).1
      obtain ⟨ys', hok, hperm, hpw⟩ := ih hys
      have hstep : AegisShim.sortInsert Std.core.cmp.OrdI64.cmp x (y :: ys)
          = if (compare x.val y.val == Ordering.gt) then
              ((AegisShim.sortInsert Std.core.cmp.OrdI64.cmp x ys) >>= fun r => ok (y :: r))
            else ok (x :: y :: ys) := by
        simp [AegisShim.sortInsert]
        rfl
      by_cases hc : (compare x.val y.val == Ordering.gt) = true
      · have hyx : y.val ≤ x.val := by
          rw [beq_iff_eq, compare_gt_iff_gt] at hc
          omega
        refine ⟨y :: ys', ?_, ?_, ?_⟩
        · rw [hstep, if_pos hc, hok]
          simp
        · exact (List.Perm.cons y hperm).trans (List.Perm.swap x y ys)
        · refine List.Pairwise.cons ?_ hpw
          intro a ha
          have hm : a ∈ x :: ys := hperm.subset ha
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hyx
          · exact hyall a hm
      · have hle : x.val ≤ y.val := by
          rw [beq_iff_eq, compare_gt_iff_gt] at hc
          omega
        refine ⟨x :: y :: ys, ?_, ?_, ?_⟩
        · rw [hstep, if_neg hc]
        · exact List.Perm.refl _
        · refine List.Pairwise.cons ?_ hsort
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hle
          · exact le_trans hle (hyall a ha)

  /-- Insertion sort produces a nondecreasing permutation of its input. -/
  theorem sortList_spec (l : List Std.I64) :
      ∃ l', AegisShim.sortList Std.core.cmp.OrdI64.cmp l = ok l' ∧
        l'.Perm l ∧ l'.Pairwise (fun a b => a.val ≤ b.val) := by
    induction l with
    | nil =>
      exact ⟨[], by simp [AegisShim.sortList], List.Perm.refl _, List.Pairwise.nil⟩
    | cons x xs ih =>
      obtain ⟨xs', hok, hperm, hpw⟩ := ih
      obtain ⟨l', hok', hperm', hpw'⟩ := sortInsert_spec x xs' hpw
      refine ⟨l', ?_, ?_, hpw'⟩
      · simp only [AegisShim.sortList]
        rw [hok, Aeneas.Std.bind_ok]
        exact hok'
      · exact hperm'.trans (List.Perm.cons x hperm)

  /-- Sorting a slice returns a slice whose contents are a nondecreasing permutation of the
  original contents (in particular the length bound is preserved, so no panic occurs). -/
  theorem slice_sort_spec (s : Slice Std.I64) :
      ∃ s' : Slice Std.I64, alloc.slice.Slice.sort Std.core.cmp.OrdI64 s = ok s' ∧
        s'.val.Perm s.val ∧ s'.val.Pairwise (fun a b => a.val ≤ b.val) := by
    obtain ⟨l', hok, hperm, hpw⟩ := sortList_spec s.val
    have hlen : l'.length ≤ Usize.max := by
      rw [hperm.length_eq]
      exact s.property
    refine ⟨Slice.from l' hlen, ?_, ?_, ?_⟩
    · simp only [alloc.slice.Slice.sort]
      rw [hok]
      simp only [bind_ok]
      rw [dif_pos hlen]
    · simpa using hperm
    · simpa using hpw

  /-! ### Specification of the feasibility loop `can_make_loop` -/

  theorem ite_bind_result {c : Prop} [Decidable c] {α β : Type} (a b : Result α)
      (f : α → Result β) :
      Std.bind (if c then a else b) f = if c then Std.bind a f else Std.bind b f := by
    by_cases h : c <;> simp [h]

  theorem can_make_loop_stop (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize) (h : n.val ≤ i.val) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i =
        ok (decide (count ≥ k)) := by
    have hc : ¬ (i < n) := by
      show ¬ (i.val < n.val)
      omega
    conv_lhs => rw [Aegis.MaximumTastiness.can_make_loop, Std.loop.eq_def]
    dsimp only
    rw [Aegis.MaximumTastiness.can_make_loop.body]
    rw [if_neg hc]
    simp

  theorem can_make_loop_step (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (count last : Std.I64) (i : Std.Usize) (h : i.val < n.val) :
      Aegis.MaximumTastiness.can_make_loop sorted k d n count last i
        = Std.bind (Slice.index_usize sorted i) (fun i1 =>
            Std.bind (i1 - last) (fun i2 =>
              if i2 ≥ d then
                Std.bind (count + 1#i64) (fun count1 =>
                  if count1 ≥ k then ok true
                  else Std.bind (i + 1#usize) (fun i3 =>
                    Aegis.MaximumTastiness.can_make_loop sorted k d n count1 i1 i3))
              else Std.bind (i + 1#usize) (fun i3 =>
                Aegis.MaximumTastiness.can_make_loop sorted k d n count last i3))) := by
    have hc : i < n := by
      show i.val < n.val
      exact h
    conv_lhs => rw [Aegis.MaximumTastiness.can_make_loop, Std.loop.eq_def]
    dsimp only
    rw [Aegis.MaximumTastiness.can_make_loop.body]
    rw [if_pos hc]
    simp only [Std.bind_tc_ok, Std.bind_assoc_eq, Std.bind_tc_eq, ite_bind_result, Std.bind_ok,
      Std.bind_assoc]
    simp only [Aegis.MaximumTastiness.can_make_loop]

  theorem usize_succ_eq {i : Std.Usize} (h : i.val + 1 ≤ Std.Usize.max) :
      ∃ i3 : Std.Usize, i + 1#usize = ok i3 ∧ i3.val = i.val + 1 := by
    have h1 : (1#usize : Std.Usize).val = 1 := rfl
    have h2 : i.val + (1#usize : Std.Usize).val < 2 ^ Std.UScalarTy.Usize.numBits := by
      rw [Std.Usize.max, Std.Usize.numBits] at h
      rw [h1]
      omega
    exact usize_add_eq (x := i) (y := 1#usize) h2

  /-! ### Specification of the feasibility test `can_make` -/

  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) (n : Std.Usize)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hn : n.val = sorted.val.length)
      (hnmax : n.val ≤ 1000000)
      (hkmax : k.val ≤ 1000000000) :
      ∀ (m : ℕ) (count last : Std.I64) (i : Std.Usize),
        n.val - i.val ≤ m → i.val ≤ n.val → 0 ≤ count.val → count.val ≤ k.val →
        1 ≤ last.val → last.val ≤ 1000000000 →
        ∃ b, Aegis.MaximumTastiness.can_make_loop sorted k d n count last i = ok b ∧
          (b = true ↔
            (k.val : ℤ) ≤ (count.val : ℤ) +
              ((gcount ((vals sorted).drop i.val) last.val d.val : ℕ) : ℤ)) := by
    intro m
    induction m with
    | zero =>
      intro count last i hm hi hc0 hck hl1 hl2
      have hieq : i.val = n.val := by omega
      have hdrop0 : (vals sorted).drop i.val = [] := by
        rw [List.drop_of_length_le]
        simp only [vals, List.length_map]
        omega
      refine ⟨decide (count ≥ k), can_make_loop_stop sorted k d n count last i (by omega), ?_⟩
      rw [hdrop0, gcount_nil]
      simp only [decide_eq_true_eq, Std.IScalar.le_equiv, Nat.cast_zero]
      constructor <;> intro h <;> omega
    | succ m ih =>
      intro count last i hm hi hc0 hck hl1 hl2
      by_cases hlt : i.val < n.val
      · have hlenv : i.val < sorted.val.length := by rw [← hn]; exact hlt
        set x : Std.I64 := sorted.val[i.val]'hlenv with hxdef
        have hxmem : x ∈ sorted.val := by
          rw [hxdef]
          exact List.getElem_mem hlenv
        have hxb := hval x hxmem
        have hidx : Slice.index_usize sorted i = ok x := by
          rw [index_usize_eq sorted i hlenv]
        have hsub_lo : Std.I64.min ≤ x.val - last.val := by
          simp only [Std.I64.min_eq]
          omega
        have hsub_hi : x.val - last.val ≤ Std.I64.max := by
          simp only [Std.I64.max_eq]
          omega
        obtain ⟨i2, hi2eq, hi2val⟩ := i64_sub_eq (x := x) (y := last) hsub_lo hsub_hi
        have hdrop : (vals sorted).drop i.val = x.val :: (vals sorted).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (l := vals sorted) (i := i.val) (by
            simp only [vals, List.length_map]
            omega)]
          congr 1
          simp only [vals, List.getElem_map]
          exact (congrArg (fun y : Std.I64 => y.val) hxdef).symm
        have hi3 : ∃ i3 : Std.Usize, i + 1#usize = ok i3 ∧ i3.val = i.val + 1 :=
          usize_succ_eq (i := i) (by have h := usize_max_ge; omega)
        have hp : (1#i64 : Std.I64).val = 1 := rfl
        rw [can_make_loop_step sorted k d n count last i hlt]
        simp only [hidx, Std.bind_ok, Std.bind_tc_ok]
        rw [hi2eq]
        simp only [Std.bind_ok, Std.bind_tc_ok]
        rw [hdrop]
        by_cases hacc : d.val ≤ x.val - last.val
        · rw [if_pos (show d ≤ i2 by
            simp only [Std.IScalar.le_equiv]
            omega)]
          obtain ⟨count1, hc1eq, hc1val⟩ := i64_add_eq (x := count) (y := 1#i64) (by
            simp only [Std.I64.min_eq, hp]
            omega) (by
            simp only [Std.I64.max_eq, hp]
            omega)
          rw [hc1eq]
          simp only [Std.bind_ok, Std.bind_tc_ok]
          rw [gcount_cons_of_le (x := x.val) (xs := (vals sorted).drop (i.val + 1))
            (v := last.val) (d := d.val) hacc]
          by_cases hfin : k.val ≤ count1.val
          · rw [if_pos (show k ≤ count1 by
              simp only [Std.IScalar.le_equiv]
              exact hfin)]
            refine ⟨true, rfl, ?_⟩
            simp only [true_iff, Nat.cast_add, Nat.cast_one]
            omega
          · rw [if_neg (show ¬ (k ≤ count1) by
              simp only [Std.IScalar.le_equiv]
              omega)]
            obtain ⟨i3, hi3eq, hi3val⟩ := hi3
            rw [hi3eq]
            simp only [Std.bind_ok, Std.bind_tc_ok]
            obtain ⟨b, hb, hiff⟩ :=
              ih count1 x i3 (by omega) (by omega) (by omega) (by omega) hxb.1 hxb.2
            refine ⟨b, hb, ?_⟩
            rw [hiff, hi3val, hc1val, Nat.cast_add, Nat.cast_one]
            constructor <;> intro h <;> omega
        · rw [if_neg (show ¬ (d ≤ i2) by
            simp only [Std.IScalar.le_equiv]
            omega)]
          obtain ⟨i3, hi3eq, hi3val⟩ := hi3
          rw [hi3eq]
          simp only [Std.bind_ok, Std.bind_tc_ok]
          rw [gcount_cons_of_not_le (x := x.val) (xs := (vals sorted).drop (i.val + 1))
            (v := last.val) (d := d.val) hacc]
          obtain ⟨b, hb, hiff⟩ :=
            ih count last i3 (by omega) (by omega) hc0 hck hl1 hl2
          refine ⟨b, hb, ?_⟩
          rw [hiff, hi3val]
      · have hge : n.val ≤ i.val := by omega
        have hieq : i.val = n.val := by omega
        have hdrop0 : (vals sorted).drop i.val = [] := by
          rw [List.drop_of_length_le]
          simp only [vals, List.length_map]
          omega
        refine ⟨decide (count ≥ k), can_make_loop_stop sorted k d n count last i hge, ?_⟩
        rw [hdrop0, gcount_nil]
        simp only [decide_eq_true_eq, Std.IScalar.le_equiv, Nat.cast_zero]
        constructor <;> intro h <;> omega

  theorem can_make_spec (s : Slice Std.I64) (k d : Std.I64)
      (hval : ∀ x ∈ s.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hsort : (vals s).Pairwise (· ≤ ·))
      (hd0 : 0 ≤ d.val)
      (hk2 : 2 ≤ k.val.toNat) (hklen : k.val.toNat ≤ (vals s).length)
      (hsl : (vals s).length ≤ 1000000)
      (hkmax : k.val ≤ 1000000000) :
      ∃ b, Aegis.MaximumTastiness.can_make s k d = ok b ∧
        (b = true ↔ FeasibleSet (vals s) k.val.toNat d.val) := by
    have hlenv : (vals s).length = s.val.length := by simp [vals]
    have hknat : ((k.val.toNat : ℕ) : ℤ) = k.val := by
      have h := Nat.zero_le k.val.toNat
      omega
    have hkval : 2 ≤ k.val := by
      have h := hknat
      have := hk2
      omega
    have hp1 : (1#i64 : Std.I64).val = 1 := rfl
    have hp1u : (1#usize : Std.Usize).val = 1 := rfl
    have hp0 : (0#usize : Std.Usize).val = 0 := rfl
    have hc1 : ¬ (k ≤ (1#i64 : Std.I64)) := by
      show ¬ (k.val ≤ (1#i64 : Std.I64).val)
      rw [hp1]
      omega
    have hpos : 0 < s.val.length := by
      rw [hlenv] at hklen
      omega
    have h0lt : (0#usize).val < s.val.length := by
      rw [hp0]
      omega
    have hn : (Slice.len s).val = s.val.length := by simp [Slice.len_val]
    have hnmax : (Slice.len s).val ≤ 1000000 := by
      rw [hn, ← hlenv]
      exact hsl
    have hstep : Aegis.MaximumTastiness.can_make s k d
        = (do let last ← Slice.index_usize s (0#usize)
              Aegis.MaximumTastiness.can_make_loop s k d (Slice.len s) 1#i64 last
                1#usize) := by
      rw [Aegis.MaximumTastiness.can_make]
      rw [if_neg hc1]
    rw [hstep]
    have hidx : Slice.index_usize s (0#usize) = ok (s.val[(0#usize).val]'h0lt) :=
      index_usize_eq s (0#usize) h0lt
    rw [hidx, Std.bind_ok]
    obtain ⟨b, hb, hiff⟩ := can_make_loop_spec s k d (Slice.len s) hval
      (by rw [hn]) hnmax hkmax (Slice.len s).val (1#i64)
      (s.val[(0#usize).val]'h0lt) (1#usize)
      (by rw [hp1u]; omega) (by rw [hp1u]; rw [hn]; omega)
      (by rw [hp1]; omega) (by rw [hp1]; omega)
      (hval _ (List.getElem_mem h0lt)).1 (hval _ (List.getElem_mem h0lt)).2
    refine ⟨b, hb, ?_⟩
    rw [hiff, feasibleSet_iff_gcount (l := vals s) hsort hk2 hklen]
    have hgetD : (vals s).getD 0 0 = (s.val[(0#usize).val]'h0lt).val := by
      rw [List.getD_eq_getElem _ (0 : ℤ) (by
        simp only [vals, List.length_map, hp0]
        exact h0lt)]
      simp only [vals, List.getElem_map, hp0]
    rw [hknat, hp1, hp1u, hgetD]

  /-! ### The binary search loop `maximum_tastiness_loop1` -/

  theorem tdiv_two_bounds {a : ℤ} (h : 2 ≤ a) : 1 ≤ a.tdiv 2 ∧ a.tdiv 2 < a := by
    have h2 : a.tdiv 2 = a / 2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
    refine ⟨?_, ?_⟩
    · rw [h2, Int.le_ediv_iff_mul_le (by norm_num)]
      norm_num
      omega
    · rw [h2]
      exact Int.ediv_lt_self_of_pos_of_ne_one (by omega) (by norm_num)

  theorem maximum_tastiness_loop1_step (k : Std.I64) (sorted : alloc.vec.Vec Std.I64)
      (lo hi : Std.I64) :
      Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi
        = (do let i ← lo + 1#i64
              if i < hi then
                (do let i1 ← hi - lo
                    let i2 ← i1 / 2#i64
                    let mid ← lo + i2
                    let s := alloc.vec.Vec.deref sorted
                    let b ← Aegis.MaximumTastiness.can_make s k mid
                    if b then Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted mid hi
                    else Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo mid)
              else ok lo) := by
    conv_lhs => rw [Aegis.MaximumTastiness.maximum_tastiness_loop1, Std.loop.eq_def]
    dsimp only
    rw [Aegis.MaximumTastiness.maximum_tastiness_loop1.body]
    simp only [Std.bind_tc_ok, Std.bind_assoc_eq, Std.bind_tc_eq, ite_bind_result, Std.bind_ok,
      Std.bind_assoc]
    simp only [Aegis.MaximumTastiness.maximum_tastiness_loop1]

  theorem FeasibleSet_mono_not {l : List ℤ} {k : ℕ} {d d' : ℤ}
      (h : ¬ FeasibleSet l k d) (hdd : d ≤ d') : ¬ FeasibleSet l k d' :=
    fun h' => h (FeasibleSet_mono hdd h')

  theorem FeasibleSet_zero {l : List ℤ} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ}
      (hk2 : 2 ≤ k) (hkl : k ≤ l.length) : FeasibleSet l k 0 := by
    have hkR : (Finset.range k).card = k := Finset.card_range k
    refine ⟨Finset.range k, ?_, hkR, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_range]
      exact lt_of_lt_of_le (Finset.mem_range.mp ha) hkl
    · exact consecutiveGaps_nonempty_of_card (by rw [hkR]; exact hk2)
    · intro g hg
      obtain ⟨a, haS, b, hbS, hlt, hbtw, rfl⟩ := mem_consecutiveGaps.mp hg
      have hb : b < l.length := lt_of_lt_of_le (Finset.mem_range.mp hbS) hkl
      have hle := getD_le_getD_of_le hsort (le_of_lt hlt) hb
      omega

  theorem loop1_spec (sorted : alloc.vec.Vec Std.I64) (k : Std.I64)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hsort : (vals (alloc.vec.Vec.deref sorted)).Pairwise (· ≤ ·))
      (hk2 : 2 ≤ k.val.toNat)
      (hklen : k.val.toNat ≤ (vals (alloc.vec.Vec.deref sorted)).length)
      (hsl : (vals (alloc.vec.Vec.deref sorted)).length ≤ 1000000)
      (hkmax : k.val ≤ 1000000000) :
      ∀ (m : ℕ) (lo hi : Std.I64),
        0 ≤ lo.val → lo.val < hi.val → hi.val ≤ 1000000001 → hi.val - lo.val ≤ m →
        FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat lo.val →
        (∀ d : ℤ, hi.val ≤ d →
          ¬ FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat d) →
        ∃ r, Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi = ok r ∧
          FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat r.val ∧
          ¬ FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat (r.val + 1) := by
    intro m
    induction m with
    | zero =>
      intro lo hi hlo0 hlt hhi hm hfeas hnot
      have hp1 : (1#i64 : Std.I64).val = 1 := rfl
      obtain ⟨i, hieq, hival⟩ := i64_add_eq (x := lo) (y := 1#i64) (by
        simp only [Std.I64.min_eq, hp1]; omega) (by
        simp only [Std.I64.max_eq, hp1]; omega)
      rw [maximum_tastiness_loop1_step k sorted lo hi, hieq]
      simp only [Std.bind_ok, Std.bind_tc_ok]
      rw [if_neg (by
        show ¬ (i < hi)
        simp only [Std.IScalar.lt_equiv]
        omega)]
      exact ⟨lo, rfl, hfeas, hnot (lo.val + 1) (by omega)⟩
    | succ m ih =>
      intro lo hi hlo0 hlt hhi hm hfeas hnot
      have hp1 : (1#i64 : Std.I64).val = 1 := rfl
      have hp2 : (2#i64 : Std.I64).val = 2 := rfl
      obtain ⟨i, hieq, hival⟩ := i64_add_eq (x := lo) (y := 1#i64) (by
        simp only [Std.I64.min_eq, hp1]; omega) (by
        simp only [Std.I64.max_eq, hp1]; omega)
      rw [maximum_tastiness_loop1_step k sorted lo hi, hieq]
      simp only [Std.bind_ok, Std.bind_tc_ok]
      by_cases hstop : hi.val ≤ lo.val + 1
      · rw [if_neg (by
          show ¬ (i < hi)
          simp only [Std.IScalar.lt_equiv]
          omega)]
        exact ⟨lo, rfl, hfeas, hnot (lo.val + 1) (by omega)⟩
      · have hlt2 : lo.val + 1 < hi.val := by omega
        rw [if_pos (by
          show i < hi
          simp only [Std.IScalar.lt_equiv]
          omega)]
        obtain ⟨d1, hd1eq, hd1val⟩ := i64_sub_eq (x := hi) (y := lo) (by
          simp only [Std.I64.min_eq]; omega) (by
          simp only [Std.I64.max_eq]; omega)
        rw [hd1eq]
        simp only [Std.bind_ok, Std.bind_tc_ok]
        obtain ⟨hb2a, hb2b⟩ := tdiv_two_bounds (a := d1.val) (by omega)
        obtain ⟨d2, hd2eq, hd2val⟩ := i64_div_eq (x := d1) (y := 2#i64) (by
          rw [hp2]; norm_num) (by
          intro h
          rw [hp2] at h
          omega)
        rw [hd2eq]
        simp only [Std.bind_ok, Std.bind_tc_ok]
        have hd2val' : d2.val = d1.val.tdiv 2 := by rw [hd2val, hp2]
        obtain ⟨mid, hmeq, hmval⟩ := i64_add_eq (x := lo) (y := d2) (by
          simp only [Std.I64.min_eq]; omega) (by
          simp only [Std.I64.max_eq]; omega)
        rw [hmeq]
        simp only [Std.bind_ok, Std.bind_tc_ok]
        have hval' : ∀ x ∈ (alloc.vec.Vec.deref sorted).val,
            1 ≤ x.val ∧ x.val ≤ 1000000000 := by
          intro x hx
          exact hval x (by simpa [alloc.vec.Vec.deref] using hx)
        obtain ⟨b, hb, hbiff⟩ := can_make_spec (alloc.vec.Vec.deref sorted) k mid hval'
          hsort (by omega) hk2 hklen hsl hkmax
        rw [hb]
        simp only [Std.bind_ok, Std.bind_tc_ok]
        by_cases hbtrue : b = true
        · rw [if_pos hbtrue]
          have hmid : FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat mid.val :=
            hbiff.mp hbtrue
          obtain ⟨r, hr, hfr, hnfr⟩ :=
            ih mid hi (by omega) (by omega) hhi (by omega) hmid hnot
          exact ⟨r, hr, hfr, hnfr⟩
        · rw [if_neg hbtrue]
          have hmid : ¬ FeasibleSet (vals (alloc.vec.Vec.deref sorted)) k.val.toNat mid.val :=
            fun h => hbtrue (hbiff.mpr h)
          obtain ⟨r, hr, hfr, hnfr⟩ :=
            ih lo mid hlo0 (by omega) (by omega) (by omega) hfeas
              (fun d hd => FeasibleSet_mono_not hmid hd)
          exact ⟨r, hr, hfr, hnfr⟩

  /-! ## Specifications -/

  /-! ### Auxiliary facts about indexing into the sorted vector -/

  theorem vec_index_spec (v : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (h : i.val < v.val.length) :
      ∃ x : Std.I64,
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64) v i = ok x ∧
          x = v.val[i.val]'h := by
    refine ⟨v.val[i.val]'h, ?_, rfl⟩
    rw [alloc.vec.Vec.index_slice_index]
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]

  theorem vals_deref_getD {v : alloc.vec.Vec Std.I64} {i : ℕ} (h : i < v.val.length) :
      (vals (alloc.vec.Vec.deref v)).getD i 0 = (v.val[i]'h).val := by
    have h1 : (vals (alloc.vec.Vec.deref v)).length = v.val.length := by
      simp [vals, alloc.vec.Vec.deref]
    rw [List.getD_eq_getElem _ (0 : ℤ) (by rw [h1]; exact h)]
    simp [vals, alloc.vec.Vec.deref]

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
  theorem spec_12 (price : Slice Std.I64) (k : Std.I64) (s : List ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_sorted : s.Pairwise (· ≤ ·)) (h_perm : s.Perm (vals price)) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = maxMinConsecutiveGap s k.val.toNat := by
    have hp0 : (0#usize : Std.Usize).val = 0 := rfl
    have hp1u : (1#usize : Std.Usize).val = 1 := rfl
    have hp1 : (1#i64 : Std.I64).val = 1 := rfl
    have hn0 : ¬ (Slice.len price = (0#usize)) := by
      intro h
      have h2 : (Slice.len price).val = 0 := by rw [h]; rfl
      have h3 : (Slice.len price).val = price.length := by simp [Slice.len_val]
      omega
    have hL : price.length < Std.Usize.max := by
      have := usize_max_ge
      omega
    have hknat : ((k.val.toNat : ℕ) : ℤ) = k.val := by omega
    have hk2 : 2 ≤ k.val.toNat := by omega
    have hkmax : k.val ≤ 1000000000 := by omega
    have hvl : (vals price).length = price.length := by simp [vals]
    have hklen : k.val.toNat ≤ (vals price).length := by rw [hvl]; omega
    rw [Aegis.MaximumTastiness.maximum_tastiness]
    rw [if_neg hn0]
    obtain ⟨v, hv, hvval⟩ :=
      loop0_spec price hL price.length (0#usize) (alloc.vec.Vec.new Std.I64)
        (by rw [hp0]; omega) (by rw [hp0]; omega) (by simp)
    rw [hv]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    simp only [lift, alloc.vec.Vec.deref_mut, Std.bind_ok, Std.bind_tc_ok]
    show ∃ r : Std.I64,
      (do let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 v.slice
          let i ← Slice.len price - 1#usize
          let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64)
            (⟨s1⟩ : alloc.vec.Vec Std.I64) i
          let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I64)
            (⟨s1⟩ : alloc.vec.Vec Std.I64) 0#usize
          let max_diff ← i1 - i2
          let hi ← max_diff + 1#i64
          Aegis.MaximumTastiness.maximum_tastiness_loop1 k
            (⟨s1⟩ : alloc.vec.Vec Std.I64) 0#i64 hi) = ok r ∧
        r.val = maxMinConsecutiveGap s k.val.toNat
    obtain ⟨s1, hs1eq, hs1perm, hs1sort⟩ := slice_sort_spec v.slice
    rw [hs1eq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    have hs1len : s1.val.length = price.length := by
      rw [hs1perm.length_eq]
      have h := congrArg List.length hvval
      simpa [alloc.vec.Vec.val] using h
    have hvprice : ∀ x ∈ (↑v : List Std.I64), 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      exact h_price x (hvval ▸ hx)
    obtain ⟨i, hieq, hival⟩ :=
      usize_sub_eq (x := Slice.len price) (y := 1#usize) (by
        rw [hp1u, Slice.len_val]; omega)
    rw [hieq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    have hival' : i.val = price.length - 1 := by
      rw [hival, hp1u]
      have h3 : (Slice.len price).val = price.length := by simp [Slice.len_val]
      omega
    have hilt : i.val < s1.val.length := by rw [hs1len, hival']; omega
    obtain ⟨x1, hx1eq, hx1def⟩ := vec_index_spec ⟨s1⟩ i (by simpa [alloc.vec.Vec.val] using hilt)
    rw [hx1eq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    have h0lt : (0#usize).val < s1.val.length := by rw [hp0, hs1len]; omega
    obtain ⟨x2, hx2eq, hx2def⟩ :=
      vec_index_spec ⟨s1⟩ (0#usize) (by simpa [alloc.vec.Vec.val] using h0lt)
    rw [hx2eq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    have hx1mem : x1 ∈ (↑v : List Std.I64) := by
      have h1 : x1 ∈ (↑s1 : List Std.I64) := by
        rw [hx1def]
        simpa [alloc.vec.Vec.val] using List.getElem_mem hilt
      simpa [alloc.vec.Vec.val] using hs1perm.subset h1
    have hx2mem : x2 ∈ (↑v : List Std.I64) := by
      have h1 : x2 ∈ (↑s1 : List Std.I64) := by
        rw [hx2def]
        simpa [alloc.vec.Vec.val] using List.getElem_mem h0lt
      simpa [alloc.vec.Vec.val] using hs1perm.subset h1
    have hx1b := hvprice x1 hx1mem
    have hx2b := hvprice x2 hx2mem
    obtain ⟨md, hmeq, hmval⟩ :=
      i64_sub_eq (x := x1) (y := x2) (by simp only [Std.I64.min_eq]; omega) (by
        simp only [Std.I64.max_eq]; omega)
    rw [hmeq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    obtain ⟨hi, hhieq, hhival⟩ :=
      i64_add_eq (x := md) (y := 1#i64) (by simp only [Std.I64.min_eq, hp1]; omega) (by
        simp only [Std.I64.max_eq, hp1]; omega)
    rw [hhieq]
    simp only [Std.bind_ok, Std.bind_tc_ok]
    have hp0i : (0#i64 : Std.I64).val = 0 := rfl
    set l : List ℤ := vals (alloc.vec.Vec.deref (⟨s1⟩ : alloc.vec.Vec Std.I64)) with hldef
    have hvs : (↑(⟨s1⟩ : alloc.vec.Vec Std.I64) : List Std.I64) = s1.val := rfl
    have hl_pair : l.Pairwise (· ≤ ·) := by
      rw [hldef]
      have h1 : vals (alloc.vec.Vec.deref (⟨s1⟩ : alloc.vec.Vec Std.I64))
          = s1.val.map (fun x => x.val) := by
        simp [vals, alloc.vec.Vec.deref, alloc.vec.Vec.val]
      rw [h1]
      exact List.Pairwise.map (fun x : Std.I64 => x.val) (fun a b h => h) hs1sort
    have hl_len : l.length = price.length := by
      rw [hldef]
      simp only [vals, alloc.vec.Vec.deref, Slice.from_val, List.length_map, alloc.vec.Vec.val]
      exact hs1len
    have hklen_l : k.val.toNat ≤ l.length := by rw [hl_len]; omega
    have hsl_l : l.length ≤ 1000000 := by rw [hl_len]; omega
    have hval_s : ∀ x ∈ (↑(⟨s1⟩ : alloc.vec.Vec Std.I64) : List Std.I64),
        1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      rw [hvs] at hx
      exact hvprice x (hs1perm.subset hx)
    have hilt' : i.val < (↑(⟨s1⟩ : alloc.vec.Vec Std.I64) : List Std.I64).length := by
      rw [hvs]; exact hilt
    have h0lt' : (0#usize).val < (↑(⟨s1⟩ : alloc.vec.Vec Std.I64) : List Std.I64).length := by
      rw [hvs]; exact h0lt
    have hx1D : x1.val = l.getD (l.length - 1) 0 := by
      have h1 : l.getD i.val 0 = x1.val := by
        rw [hldef, vals_deref_getD (v := (⟨s1⟩ : alloc.vec.Vec Std.I64)) (i := i.val) hilt',
          ← hx1def]
      have h2 : l.length - 1 = i.val := by rw [hl_len, hival']
      rw [h2, ← h1]
    have hx2D : x2.val = l.getD 0 0 := by
      have h1 : l.getD (0#usize).val 0 = x2.val := by
        rw [hldef, vals_deref_getD (v := (⟨s1⟩ : alloc.vec.Vec Std.I64)) (i := (0#usize).val) h0lt',
          ← hx2def]
      rw [hp0] at h1
      rw [← h1]
    have hfeas0 : FeasibleSet l k.val.toNat 0 := FeasibleSet_zero hl_pair hk2 hklen_l
    have hxle : x2.val ≤ x1.val := by
      rw [hx1D, hx2D]
      exact getD_le_getD_of_le hl_pair (by omega) (by omega)
    have hnot : ∀ d : ℤ, hi.val ≤ d → ¬ FeasibleSet l k.val.toNat d := by
      intro d hd hfe
      have hsp := feasibleSet_le_spread hl_pair hklen_l hfe
      rw [hx1D.symm, hx2D.symm] at hsp
      omega
    obtain ⟨r, hr, hfr, hnfr⟩ :=
      loop1_spec (⟨s1⟩ : alloc.vec.Vec Std.I64) k hval_s hl_pair hk2 hklen_l hsl_l hkmax
        hi.val.toNat (0#i64) hi (by omega) (by omega) (by omega)
        (by omega) hfeas0 hnot
    have hM := maxMinConsecutiveGap_spec (l := l) (k := k.val.toNat) hk2 hklen_l
    have hrM : r.val = maxMinConsecutiveGap l k.val.toNat := by
      have h1 : r.val ≤ maxMinConsecutiveGap l k.val.toNat := hM.2 r.val hfr
      have h2 : maxMinConsecutiveGap l k.val.toNat ≤ r.val := by
        by_contra hcon
        have h3 : r.val + 1 ≤ maxMinConsecutiveGap l k.val.toNat := by omega
        exact hnfr (FeasibleSet_mono h3 hM.1)
      omega
    have hl_perm : l.Perm s := by
      rw [hldef]
      have h1 : vals (alloc.vec.Vec.deref (⟨s1⟩ : alloc.vec.Vec Std.I64))
          = s1.val.map (fun x => x.val) := by
        simp [vals, alloc.vec.Vec.deref, alloc.vec.Vec.val]
      rw [h1]
      have h3 : (↑s1 : List Std.I64).Perm (↑v : List Std.I64) := by
        simpa [alloc.vec.Vec.val] using hs1perm
      have h2 : s1.val.Perm price.val := by
        rw [hvval] at h3
        exact h3
      exact (List.Perm.map (fun x : Std.I64 => x.val) h2).trans h_perm.symm
    have heq : l = s := hl_perm.eq_of_pairwise' hl_pair h_sorted
    refine ⟨r, hr, ?_⟩
    rw [hrM, heq]

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
