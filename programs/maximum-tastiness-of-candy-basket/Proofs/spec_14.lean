import Aegis.MaximumTastiness.Code.Funs

/-
Proof of `AegisSpec.MaximumTastiness.spec_14` (maximum-tastiness-of-candy-basket).
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
  theorem spec_S13 (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, (vals q).Perm (vals price) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    sorry

  /-! ## Tools used in the proof of `spec_S14`

  The proof of `spec_S14` does *not* characterise the value returned by the program.
  Instead it shows that the program is *equivariant* under a uniform shift of all the
  entries of the array.  Every stage of the program is described by a pure function on
  the list of integer values, and the invariance of those pure functions is proved by
  elementary inductions. -/

  /-- Values of a list of machine integers. -/
  def lvals (l : List Std.I64) : List ℤ := l.map fun x => x.val

  /-- The comparison used by the insertion sort below, in `ok` form. -/
  theorem i64cmp_spec (x y : Std.I64) :
      Aeneas.Std.core.cmp.OrdI64.cmp x y = .ok (compare x.val y.val) := rfl

  /-- Comparing two integers is invariant under a simultaneous shift. -/
  theorem compare_add_add (a b c : ℤ) : compare (a + c) (b + c) = compare a b := by
    rcases h : compare (a + c) (b + c) with _ | _ | _ <;>
      rcases h' : compare a b with _ | _ | _ <;>
      simp_all [Std.compare_eq_lt, Std.compare_eq_gt] <;> omega

  /-- Insertion of an integer into a nondecreasing list: the pure model of the insertion
  sort used by the extracted program. -/
  def insV (a : ℤ) : List ℤ → List ℤ
    | [] => [a]
    | b :: bs => if b < a then b :: insV a bs else a :: b :: bs

  /-- Insertion sort on integers. -/
  def sortV : List ℤ → List ℤ
    | [] => []
    | x :: xs => insV x (sortV xs)

  theorem insV_shift (a c : ℤ) : ∀ l : List ℤ,
      insV (a + c) (l.map (fun x => x + c)) = (insV a l).map (fun x => x + c)
    | [] => by simp [insV]
    | b :: bs => by
      simp only [List.map_cons, insV, insV_shift a c bs]
      by_cases h : b < a
      · rw [if_pos h, if_pos (show b + c < a + c by omega)]; simp
      · rw [if_neg h, if_neg (show ¬ b + c < a + c by omega)]; simp

  theorem sortV_shift (c : ℤ) : ∀ l : List ℤ,
      sortV (l.map (fun x => x + c)) = (sortV l).map (fun x => x + c)
    | [] => by simp [sortV]
    | x :: xs => by
      rw [List.map_cons, sortV, sortV, sortV_shift c xs, insV_shift]

  /-- Inversion principle for `bind` at an `ok` value. -/
  theorem bind_ok_iff {α β : Type} {m : Result α} {f : α → Result β} {b : β} :
      Aeneas.Std.bind m f = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
    constructor
    · intro h
      cases hm : m.match with
      | ok a =>
        refine ⟨a, Result.match.isOk.mp hm, ?_⟩
        rw [Result.match.isOk.mp hm] at h
        simpa using h
      | div =>
        exfalso
        rw [Result.match.isDiv.mp hm] at h
        simp [Aeneas.Std.bind_div] at h
      | vis e k =>
        exfalso
        rw [Result.match.isVis.mp hm] at h
        simp [Aeneas.Std.bind_vis] at h
    · rintro ⟨a, rfl, h⟩
      simpa using h

  theorem insV_length (a : ℤ) : ∀ l : List ℤ, (insV a l).length = l.length + 1
    | [] => rfl
    | b :: bs => by
      rw [insV]
      by_cases h : b < a <;> simp [h, insV_length a bs]

  theorem sortV_length : ∀ l : List ℤ, (sortV l).length = l.length
    | [] => rfl
    | x :: xs => by
      rw [sortV, insV_length, sortV_length xs]
      rfl

  /-- The insertion sort of the program, described on the list of values. -/
  theorem sortInsert_spec (x : Std.I64) : ∀ (r : List Std.I64),
      ∃ s, AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x r = .ok s ∧
        lvals s = insV x.val (lvals r) := by
    intro r
    induction r with
    | nil => exact ⟨[x], rfl, by simp [lvals, insV]⟩
    | cons y ys ih =>
      obtain ⟨r0, hr0, hrv⟩ := ih
      have hstep : AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x (y :: ys) =
          (do let c ← Aeneas.Std.core.cmp.OrdI64.cmp x y
              if c == Ordering.gt then do
                let r ← AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x ys
                pure (y :: r)
              else pure (x :: y :: ys)) := rfl
      rw [hstep, i64cmp_spec, bind_ok]
      rcases hc : compare x.val y.val with _ | _ | _
      · have h1 : ¬ y.val < x.val := by rw [← Std.compare_eq_gt, hc]; simp
        exact ⟨x :: y :: ys, by simp [h1, Aeneas.Std.pure_tc_eq], by simp [lvals, insV, h1]⟩
      · have h1 : y.val = x.val := by
          exact (Std.compare_eq_iff_eq.mp hc).symm
        have h2 : ¬ y.val < x.val := by omega
        exact ⟨x :: y :: ys, by simp [h1, h2, Aeneas.Std.pure_tc_eq], by simp [lvals, insV, h2]⟩
      · have h1 : y.val < x.val := Std.compare_eq_gt.mp hc
        refine ⟨y :: r0, ?_, ?_⟩
        · simp [h1, hr0, Aeneas.Std.pure_tc_eq]
        · simp only [lvals, List.map_cons, insV, if_pos h1] at hrv ⊢
          rw [hrv]

  /-- The full insertion sort of the program, described on the list of values. -/
  theorem sortList_spec : ∀ (l : List Std.I64),
      ∃ s, AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp l = .ok s ∧
        lvals s = sortV (lvals l) := by
    intro l
    induction l with
    | nil => exact ⟨[], rfl, by simp [lvals, sortV]⟩
    | cons x xs ih =>
      obtain ⟨r0, hr0, hrv⟩ := ih
      obtain ⟨r1, hr1, hr1v⟩ := sortInsert_spec x r0
      refine ⟨r1, ?_, ?_⟩
      · rw [show AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp (x :: xs) =
            (do let r ← AegisShim.sortList Aeneas.Std.core.cmp.OrdI64.cmp xs
                AegisShim.sortInsert Aeneas.Std.core.cmp.OrdI64.cmp x r) from rfl,
          hr0]
        simpa using hr1
      · rw [hr1v, hrv]
        rfl

  /-- The greedy "can we pick `k` values with pairwise distance at least `d`" scan,
  as a pure function on the list of values. -/
  def cmAux (l : List ℤ) (k d count last : ℤ) (i : ℕ) : Bool :=
    if i < l.length then
      (if l.getD i 0 - last ≥ d then
        (if count + 1 ≥ k then true else cmAux l k d (count + 1) (l.getD i 0) (i + 1))
      else cmAux l k d count last (i + 1))
    else decide (count ≥ k)
  termination_by l.length - i
  decreasing_by all_goals omega

  /-- The pure model of `can_make`. -/
  def cmTop (l : List ℤ) (k d : ℤ) : Bool :=
    if k ≤ 1 then true else cmAux l k d 1 (l.getD 0 0) 1

  /-- The first gap of the sorted values, used to bound the binary search. -/
  def hiV (l : List ℤ) : ℤ := l.getD (l.length - 1) 0 - l.getD 0 0 + 1

  /-- The pure model of the binary search loop. -/
  def bsAux (l : List ℤ) (k lo hi : ℤ) : ℤ :=
    if lo + 1 < hi then
      (if cmTop l k (lo + (hi - lo) / 2) then bsAux l k (lo + (hi - lo) / 2) hi
       else bsAux l k lo (lo + (hi - lo) / 2))
    else lo
  termination_by (hi - lo).toNat
  decreasing_by all_goals omega

  theorem getD_map_add (c : ℤ) (l : List ℤ) (i : ℕ) (h : i < l.length) :
      (l.map (fun x => x + c)).getD i 0 = l.getD i 0 + c := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem h]
    simp

  theorem cmAux_shift (c : ℤ) (l : List ℤ) (k d : ℤ) :
      ∀ (count last : ℤ) (i : ℕ),
        cmAux (l.map (fun x => x + c)) k d count (last + c) i
          = cmAux l k d count last i := by
    refine cmAux.induct l k d (fun count last i =>
      cmAux (l.map (fun x => x + c)) k d count (last + c) i
        = cmAux l k d count last i) ?_ ?_ ?_ ?_
    · intro count last i hi hd hk
      conv_lhs => rw [cmAux.eq_def]
      conv_rhs => rw [cmAux.eq_def]
      simp only [List.length_map, getD_map_add c l i hi, if_pos hi]
      rw [show l.getD i 0 + c - (last + c) = l.getD i 0 - last by omega]
      simp only [if_pos hd, if_pos hk]
    · intro count last i hi hd hk ihh
      conv_lhs => rw [cmAux.eq_def]
      conv_rhs => rw [cmAux.eq_def]
      simp only [List.length_map, getD_map_add c l i hi, if_pos hi]
      rw [show l.getD i 0 + c - (last + c) = l.getD i 0 - last by omega]
      simp only [if_pos hd, if_neg hk]
      exact ihh
    · intro count last i hi hd ihh
      conv_lhs => rw [cmAux.eq_def]
      conv_rhs => rw [cmAux.eq_def]
      simp only [List.length_map, getD_map_add c l i hi, if_pos hi]
      rw [show l.getD i 0 + c - (last + c) = l.getD i 0 - last by omega]
      simp only [if_neg hd]
      exact ihh
    · intro count last i hi
      conv_lhs => rw [cmAux.eq_def]
      conv_rhs => rw [cmAux.eq_def]
      simp only [List.length_map, if_neg hi]

  theorem cmTop_shift (c : ℤ) (l : List ℤ) (hl : 0 < l.length) (k d : ℤ) :
      cmTop (l.map (fun x => x + c)) k d = cmTop l k d := by
    unfold cmTop
    rw [getD_map_add c l 0 hl, cmAux_shift]

  theorem hiV_shift (c : ℤ) (l : List ℤ) :
      hiV (l.map (fun x => x + c)) = hiV l := by
    unfold hiV
    simp only [List.length_map]
    by_cases h : l.length = 0
    · simp [h]
    · have h1 : 0 < l.length := by omega
      rw [getD_map_add c l (l.length - 1) (by omega), getD_map_add c l 0 h1]
      ring

  theorem bsAux_shift (c : ℤ) (l : List ℤ) (hl : 0 < l.length) (k : ℤ) :
      ∀ (lo hi : ℤ), bsAux (l.map (fun x => x + c)) k lo hi = bsAux l k lo hi := by
    have key : ∀ n, ∀ (lo hi : ℤ), (hi - lo).toNat = n →
        bsAux (l.map (fun x => x + c)) k lo hi = bsAux l k lo hi := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro lo hi hn
        conv_lhs => rw [bsAux.eq_def]
        conv_rhs => rw [bsAux.eq_def]
        by_cases h : lo + 1 < hi
        · simp only [if_pos h]
          rw [cmTop_shift c l hl k]
          by_cases hc : cmTop l k (lo + (hi - lo) / 2)
          · simp only [if_pos hc]
            exact ih (hi - (lo + (hi - lo) / 2)).toNat (by omega) _ _ rfl
          · simp only [if_neg hc]
            exact ih ((lo + (hi - lo) / 2) - lo).toNat (by omega) _ _ rfl
        · simp only [if_neg h]
    intro lo hi
    exact key (hi - lo).toNat lo hi rfl

  theorem lvals_getD (s : Slice Std.I64) (i : ℕ) (h : i < s.val.length) :
      (lvals s.val).getD i 0 = (s.val[i]).val := by
    simp only [lvals, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem h]
    simp

  /-- Functional description of the greedy scan of `can_make`. -/
  theorem can_make_loop_spec (sorted : Slice Std.I64) (k d : Std.I64) :
      ∀ (m : ℕ) (n : Std.Usize) (count last : Std.I64) (i : Std.Usize),
        n.val = sorted.length → n.val ≤ 100000 → n.val - i.val = m → i.val ≤ sorted.length →
        (∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) →
        1 ≤ last.val → last.val ≤ 1000000000 →
        1 ≤ count.val → count.val ≤ i.val →
        Aegis.MaximumTastiness.can_make_loop sorted k d n count last i
          ⦃ b => b = cmAux (lvals sorted.val) k.val d.val count.val last.val i.val ⦄ := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro n count last i hn hnl hm hi hval hl1 hl2 hc1 hc2
      unfold Aegis.MaximumTastiness.can_make_loop
      simp only [Aegis.MaximumTastiness.can_make_loop.body]
      rw [Aeneas.Std.loop.eq_def]
      split
      · rename_i hlt
        have hlt' : i.val < sorted.length := by
          have h2 : i.val < n.val := hlt
          omega
        have hlen : i.val < (lvals sorted.val).length := by
          simp only [lvals, List.length_map]; exact hlt'
        have hget : (lvals sorted.val).getD i.val 0 = (sorted.val[i.val]).val :=
          lvals_getD sorted i.val hlt'
        step as ⟨ x, hx ⟩
        have hxval : x.val = (sorted.val[i.val]).val := by rw [hx]
        have hxb : 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
          have hmem : x ∈ sorted.val := hx ▸ List.mem_of_getElem rfl
          exact hval x hmem
        step as ⟨ diff, hdiff ⟩
        split
        · rename_i hge
          have hge'' : (sorted.val[i.val]).val - last.val ≥ d.val := by
            rw [← hxval, ← hdiff]; exact hge
          step as ⟨ count1, hcount1 ⟩
          split
          · rename_i hk
            have hk' : count.val + 1 ≥ k.val := by rw [← hcount1]; exact hk
            have hcx : cmAux (lvals sorted.val) k.val d.val count.val last.val i.val = true := by
              conv_lhs => rw [cmAux.eq_def]
              rw [hget]
              simp only [if_pos hlen, if_pos hge'', if_pos hk']
            simp only [Aeneas.Std.bind_ok, Aeneas.Std.WP.spec_ok]
            exact hcx.symm
          · rename_i hk
            have hk' : ¬ count.val + 1 ≥ k.val := by rw [← hcount1]; exact hk
            step as ⟨ i3, hi3 ⟩
            have hconv : cmAux (lvals sorted.val) k.val d.val count.val last.val i.val
                = cmAux (lvals sorted.val) k.val d.val count1.val x.val i3.val := by
              conv_lhs => rw [cmAux.eq_def]
              rw [hget]
              simp only [if_pos hlen, if_pos hge'', if_neg hk', hcount1, hxval, hi3]
            have hi3' : i3.val ≤ sorted.length := by rw [hi3]; omega
            have hm3 : n.val - i3.val < m := by rw [hi3]; omega
            have hih : Aegis.MaximumTastiness.can_make_loop sorted k d n count1 x i3
                ⦃ b => b = cmAux (lvals sorted.val) k.val d.val count1.val x.val i3.val ⦄ :=
              ih (n.val - i3.val) hm3 (n := n) (count := count1) (last := x)
                (i := i3) hn hnl rfl hi3' hval hxb.1 hxb.2
                (by rw [hcount1]; omega) (by rw [hcount1]; omega)
            refine Aeneas.Std.WP.spec_mono hih ?_
            intro b hb
            rw [hconv]
            exact hb
        · rename_i hge
          have hge'' : ¬ ((sorted.val[i.val]).val - last.val ≥ d.val) := by
            rw [← hxval, ← hdiff]; exact hge
          step as ⟨ i3, hi3 ⟩
          have hconv : cmAux (lvals sorted.val) k.val d.val count.val last.val i.val
              = cmAux (lvals sorted.val) k.val d.val count.val last.val i3.val := by
            conv_lhs => rw [cmAux.eq_def]
            rw [hget]
            simp only [if_pos hlen, if_neg hge'', hi3]
          have hi3' : i3.val ≤ sorted.length := by rw [hi3]; omega
          have hm3 : n.val - i3.val < m := by rw [hi3]; omega
          have hih : Aegis.MaximumTastiness.can_make_loop sorted k d n count last i3
              ⦃ b => b = cmAux (lvals sorted.val) k.val d.val count.val last.val i3.val ⦄ :=
            ih (n.val - i3.val) hm3 (n := n) (count := count) (last := last)
              (i := i3) hn hnl rfl hi3' hval hl1 hl2 hc1 (by rw [hi3]; omega)
          refine Aeneas.Std.WP.spec_mono hih ?_
          intro b hb
          rw [hconv]
          exact hb
      · rename_i hge
        have hlen_eq : (lvals sorted.val).length = n.val := by
          simp only [lvals, List.length_map]; exact hn.symm
        have hge' : ¬ i.val < (lvals sorted.val).length := by
          rw [hlen_eq]
          exact hge
        have hcx : cmAux (lvals sorted.val) k.val d.val count.val last.val i.val
            = decide (count.val ≥ k.val) := by
          conv_lhs => rw [cmAux.eq_def]
          simp only [if_neg hge']
        simp only [Aeneas.Std.bind_ok, Aeneas.Std.WP.spec_ok]
        rw [hcx]
        rfl

  /-- Functional description of `can_make`. -/
  theorem can_make_spec (sorted : Slice Std.I64) (k d : Std.I64)
      (hne : 0 < sorted.length) (hlen : sorted.length ≤ 100000)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      Aegis.MaximumTastiness.can_make sorted k d
        ⦃ b => b = cmTop (lvals sorted.val) k.val d.val ⦄ := by
    unfold Aegis.MaximumTastiness.can_make
    simp only [Slice.len_val]
    split
    · rename_i hk
      simp only [Aeneas.Std.bind_ok, Aeneas.Std.WP.spec_ok]
      simp only [cmTop, if_pos (show k.val ≤ 1 by simpa using hk)]
    · rename_i hk
      have hk' : ¬ k.val ≤ 1 := hk
      step as ⟨ last, hlast ⟩
      have hlastv : 1 ≤ last.val ∧ last.val ≤ 1000000000 := by
        have hmem : last ∈ sorted.val := hlast ▸ List.mem_of_getElem rfl
        exact hval last hmem
      have hlastL : (lvals sorted.val).getD 0 0 = last.val := by
        rw [lvals_getD sorted 0 hne, hlast]
      have hconv : cmTop (lvals sorted.val) k.val d.val
          = cmAux (lvals sorted.val) k.val d.val 1 last.val 1 := by
        simp only [cmTop, if_neg hk', hlastL]
      have h1u : (1#usize).val = 1 := by simp
      have h1i : (1#i64).val = 1 := by simp
      have h1le : (1#usize).val ≤ sorted.length := by omega
      have h1k : (1 : ℤ) ≤ (1#i64).val := by omega
      have hci : (1#i64).val ≤ (1#usize).val := by omega
      have hmi : (Slice.len sorted).val - (1#usize).val = sorted.length - 1 := by
        rw [Slice.len_val, h1u]
      have hcl := can_make_loop_spec sorted k d (sorted.length - 1)
        (Slice.len sorted) (1#i64) last (1#usize) (Slice.len_val sorted).symm hlen hmi
        h1le hval hlastv.1 hlastv.2 h1k hci
      refine Aeneas.Std.WP.spec_mono
        (m := Aegis.MaximumTastiness.can_make_loop sorted k d (Slice.len sorted) (1#i64) last (1#usize)) hcl ?_
      intro b hb
      rw [hconv]
      exact hb

  /-- A Hoare triple for a terminating computation yields its actual result. -/
  theorem spec_exists_ok {α : Type} {m : Result α} {p : α → Prop}
      (h : Aeneas.Std.WP.spec m p) : ∃ r, m = .ok r ∧ p r := by
    cases hm : m.match with
    | ok a =>
      refine ⟨a, Result.match.isOk.mp hm, ?_⟩
      rw [Result.match.isOk.mp hm] at h
      exact (Aeneas.Std.WP.spec_ok a).mp h
    | div =>
      rw [Result.match.isDiv.mp hm] at h
      exact absurd h (by simp)
    | vis e k =>
      rw [Result.match.isVis.mp hm] at h
      exact absurd h (by simp)

  /-- Functional description of the binary search loop. -/
  theorem loop1_spec (sorted : Std.alloc.vec.Vec Std.I64) (k : Std.I64)
      (hval : ∀ x ∈ sorted.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hne : 0 < sorted.length) (hlen : sorted.length ≤ 100000) :
      ∀ (m : ℕ) (lo hi : Std.I64),
        lo.val ≤ hi.val → 0 ≤ lo.val → hi.val ≤ 1000000001 →
        (hi.val - lo.val).toNat = m →
        Aegis.MaximumTastiness.maximum_tastiness_loop1 k sorted lo hi
          ⦃ r => r.val = bsAux (lvals sorted.val) k.val lo.val hi.val ⦄ := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro lo hi hle hlo hhi hm
      unfold Aegis.MaximumTastiness.maximum_tastiness_loop1
      simp only [Aegis.MaximumTastiness.maximum_tastiness_loop1.body]
      rw [Aeneas.Std.loop.eq_def]
      simp only
      step as ⟨ i, hi1 ⟩
      split
      · rename_i hc
        step as ⟨ i1, hi2 ⟩ ; try scalar_tac
        step as ⟨ i2, hi3 ⟩ ; try scalar_tac
        have h20 : 0 ≤ i2.val := by
          rw [hi3]; exact Int.tdiv_nonneg (by omega) (by norm_num)
        have h21 : i2.val ≤ i1.val := by
          rw [hi3]; exact Int.tdiv_le_self 2 (by omega)
        have hpos : 1 ≤ i2.val := by
          rw [hi3]; exact Int.le_tdiv_of_mul_le (by norm_num) (by scalar_tac)
        have hdiv : (hi.val - lo.val) / 2 = i2.val := by
          rw [← Int.tdiv_eq_ediv_of_nonneg (show (0:ℤ) ≤ hi.val - lo.val by omega), ← hi2, ← hi3]
        step as ⟨ mid, hi4 ⟩ ; try scalar_tac
        have hmid : lo.val + (hi.val - lo.val) / 2 = mid.val := by rw [hdiv]; omega
        have hcm : Aegis.MaximumTastiness.can_make sorted.deref k mid ⦃ b => b = cmTop (lvals sorted.val) k.val mid.val ⦄ := by
          have h1 : 0 < sorted.deref.length := by
            simpa [Aeneas.Std.alloc.vec.Vec.deref] using hne
          have h2 : ∀ x ∈ sorted.deref.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
            simpa [Aeneas.Std.alloc.vec.Vec.deref] using hval
          have h3 : sorted.deref.length ≤ 100000 := by
            simpa [Aeneas.Std.alloc.vec.Vec.deref] using hlen
          simpa [Aeneas.Std.alloc.vec.Vec.deref] using
            (can_make_spec sorted.deref k mid h1 h3 h2)
        step with hcm as ⟨ b, hb ⟩ ; try scalar_tac
        split
        · rename_i hbtrue
          simp only [Aeneas.Std.bind_ok]
          refine Aeneas.Std.WP.spec_mono (P₀ := fun r => r.val = bsAux (lvals sorted.val) k.val mid.val hi.val) ?_ ?_
          · refine ih (hi.val - mid.val).toNat ?_ mid hi (by omega) (by omega) hhi rfl
            rw [← hm]
            exact Int.toNat_lt_toNat (by omega) |>.mpr (by omega)
          · intro r hr
            rw [hr]
            conv_rhs => rw [bsAux.eq_def]
            have hlt : lo.val + 1 < hi.val := by omega
            have hcond : cmTop (lvals sorted.val) k.val (lo.val + (hi.val - lo.val) / 2) = true := by
              rw [hmid, ← hb, hbtrue]
            rw [ite_eq_left hlt, ite_eq_left hcond, hmid]
        · rename_i hbfalse
          simp only [Aeneas.Std.bind_ok]
          refine Aeneas.Std.WP.spec_mono (P₀ := fun r => r.val = bsAux (lvals sorted.val) k.val lo.val mid.val) ?_ ?_
          · refine ih (mid.val - lo.val).toNat ?_ lo mid (by omega) hlo (by omega) rfl
            rw [← hm]
            refine Int.toNat_lt_toNat (by omega) |>.mpr ?_
            have h1 : mid.val - lo.val = i2.val := by omega
            have h3 : (hi.val - lo.val) / 2 < hi.val - lo.val :=
              Int.ediv_lt_self_of_pos_of_ne_one (by omega) (by norm_num)
            omega
          · intro r hr
            rw [hr]
            conv_rhs => rw [bsAux.eq_def]
            have hlt : lo.val + 1 < hi.val := by omega
            have hcond : ¬ (cmTop (lvals sorted.val) k.val (lo.val + (hi.val - lo.val) / 2) = true) := by
              rw [hmid, ← hb]
              exact hbfalse
            rw [ite_eq_left hlt, ite_eq_right hcond, hmid]
      · rename_i hc
        simp only [Aeneas.Std.bind_ok]
        conv_rhs => rw [bsAux.eq_def]
        have hlt : ¬ (lo.val + 1 < hi.val) := by
          intro h'
          apply hc
          show i.val < hi.val
          omega
        rw [ite_eq_right hlt]
        exact (Aeneas.Std.WP.spec_ok lo).mpr rfl


  /-- Functional description of the loop which copies the price array into a vector. -/
  theorem maximum_tastiness_loop0_spec (price : Slice Std.I64) (n : Std.Usize)
      (m : ℕ) (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize)
      (hn : n.val = price.length)
      (hm : price.length - i.val = m)
      (hi : i.val ≤ price.length)
      (hs : sorted.val = price.val.take i.val) :
      Aegis.MaximumTastiness.maximum_tastiness_loop0 price n sorted i
        ⦃ v => v.val = price.val ⦄ := by
    have key : ∀ (n : Std.Usize) (m : ℕ) (sorted : alloc.vec.Vec Std.I64) (i : Std.Usize),
        n.val = price.length → price.length - i.val = m → i.val ≤ price.length →
        sorted.val = price.val.take i.val →
        Aegis.MaximumTastiness.maximum_tastiness_loop0 price n sorted i
          ⦃ v => v.val = price.val ⦄ := by
      intro n m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro sorted i hn hm hi hs
        unfold Aegis.MaximumTastiness.maximum_tastiness_loop0
        simp only [Aegis.MaximumTastiness.maximum_tastiness_loop0.body]
        rw [Aeneas.Std.loop.eq_def]
        split
        · rename_i hlt
          have hlt' : i.val < price.length := by
            have h2 : i.val < n.val := hlt
            omega
          step as ⟨ x, hx ⟩
          step as ⟨ s1, h1 ⟩
          step as ⟨ i2, h2 ⟩
          have hs1 : s1.val = price.val.take i2.val := by
            rw [h1, hs, hx, h2, ← List.concat_eq_append, List.take_concat_get hlt']
          have hi2 : i2.val ≤ price.length := by omega
          have hmi : price.length - i2.val < m := by omega
          exact ih (price.length - i2.val) hmi s1 i2 hn rfl hi2 hs1
        · rename_i hge
          have hge' : price.length ≤ i.val := by
            have h2 : ¬ i.val < n.val := hge
            omega
          simp only [Aeneas.Std.bind_ok, Aeneas.Std.WP.spec_ok]
          rw [hs, List.take_of_length_le hge']
    exact key n m sorted i hn hm hi hs

  /-- The insertion sort on lists permutes its input. -/
  theorem insV_perm (a : ℤ) : ∀ l : List ℤ, (insV a l).Perm (a :: l)
    | [] => by simp [insV]
    | b :: bs => by
      rw [insV]
      by_cases h : b < a
      · rw [if_pos h]
        exact (insV_perm a bs).cons b |>.trans (List.Perm.swap a b bs)
      · rw [if_neg h]

  /-- The insertion sort on lists permutes its input. -/
  theorem sortV_perm : ∀ l : List ℤ, (sortV l).Perm l
    | [] => List.Perm.refl []
    | x :: xs => by
      rw [sortV]
      exact (insV_perm x (sortV xs)).trans ((sortV_perm xs).cons x)

  /-- The sorted values stay within the bounds of the input values. -/
  theorem sortV_bound (l : List ℤ) (h : ∀ x ∈ l, 1 ≤ x ∧ x ≤ 1000000000) :
      ∀ x ∈ sortV l, 1 ≤ x ∧ x ≤ 1000000000 :=
    fun x hx => h x ((sortV_perm l).mem_iff.mp hx)

  /-- The insertion sort on lists produces a nondecreasing list. -/
  theorem insV_sorted (a : ℤ) : ∀ l : List ℤ, l.Pairwise (· ≤ ·) → (insV a l).Pairwise (· ≤ ·)
    | [], _ => by simp [insV]
    | b :: bs, h => by
      have hb : ∀ x ∈ bs, b ≤ x := fun x hx =>
        (List.pairwise_cons.mp h).1 x hx
      rw [insV]
      by_cases hlt : b < a
      · rw [if_pos hlt]
        refine List.pairwise_cons.mpr ⟨?_, insV_sorted a bs (List.pairwise_cons.mp h).2⟩
        intro x hx
        rcases List.mem_cons.mp ((insV_perm a bs).mem_iff.mp hx) with rfl | hx'
        · omega
        · exact hb x hx'
      · rw [if_neg hlt]
        have hab : a ≤ b := by omega
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hab
        · exact le_trans hab (hb x hx')

  /-- The insertion sort on lists produces a nondecreasing list. -/
  theorem sortV_sorted : ∀ l : List ℤ, (sortV l).Pairwise (· ≤ ·)
    | [] => by simp [sortV]
    | x :: xs => by
      rw [sortV]
      exact insV_sorted x (sortV xs) (sortV_sorted xs)

  /-- In a nondecreasing list the first entry is at most the last one. -/
  theorem sorted_getD_head_le_last (l : List ℤ) (h : l.Pairwise (· ≤ ·)) (h0 : 0 < l.length) :
      l.getD 0 0 ≤ l.getD (l.length - 1) 0 := by
    rw [List.getD_eq_getElem l 0 h0, List.getD_eq_getElem l 0 (by omega)]
    by_cases h1 : l.length - 1 = 0
    · simp only [h1]
      exact le_rfl
    · exact (List.pairwise_iff_getElem.mp h) 0 (l.length - 1) h0 (by omega) (by omega)

  /-- The `sort` call of the program, described on the list of values. -/
  theorem slice_sort_spec (s : Slice Std.I64) :
      alloc.slice.Slice.sort core.cmp.OrdI64 s
        ⦃ s' => lvals s'.val = sortV (lvals s.val) ⦄ := by
    obtain ⟨l, hl, hlv⟩ := sortList_spec s.val
    have hlen : l.length ≤ Usize.max := by
      have h1 : l.length = (lvals l).length := by simp [lvals]
      have h2 : (lvals l).length = s.val.length := by rw [hlv, sortV_length]; simp [lvals]
      have h3 := s.property
      omega
    simp only [alloc.slice.Slice.sort, hl, Aeneas.Std.bind_ok, dif_pos hlen,
      Aeneas.Std.WP.spec_ok, Slice.from_val, hlv]

  /-- The value returned by `maximum_tastiness`, described on the list of values. -/
  theorem maximum_tastiness_spec (price : Slice Std.I64) (k : Std.I64)
      (h_n : 2 ≤ price.length) (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        r.val = bsAux (sortV (vals price)) k.val 0 (hiV (sortV (vals price))) := by
    have hne : 0 < price.length := by omega
    have hlenle : (Slice.len price).val ≤ 100000 := by
      simp only [Slice.len_val]; exact h_len
    have hvaleq : vals price = lvals price.val := rfl
    have hwp : maximum_tastiness price k
        ⦃ r => r.val = bsAux (sortV (lvals price.val)) k.val 0 (hiV (sortV (lvals price.val))) ⦄ := by
      unfold Aegis.MaximumTastiness.maximum_tastiness
      simp only [Slice.len_val]
      split
      · rename_i h0
        have h1 : price.length = 0 := by
          have h2 : (Slice.len price).val = (0#usize).val := by rw [h0]
          simpa using h2
        exact absurd h1 (by omega)
      · rename_i h0
        have h0u : (0#usize).val = 0 := by simp
        have hloop0 : Aegis.MaximumTastiness.maximum_tastiness_loop0 price (Slice.len price)
            (alloc.vec.Vec.new I64) 0#usize ⦃ v' => v'.val = price.val ⦄ :=
          maximum_tastiness_loop0_spec price (Slice.len price) price.length
            (alloc.vec.Vec.new I64) 0#usize (Slice.len_val price) (by rw [h0u]; simp) (by simp)
            (by simp)
        step with hloop0 as ⟨ v0, hv0 ⟩
        simp only [Aeneas.Std.lift, Aeneas.Std.bind_ok, Function.uncurry_apply_pair,
          Aeneas.Std.alloc.vec.Vec.deref_mut]
        change (do
          let s1 ← alloc.slice.Slice.sort core.cmp.OrdI64 v0.slice
          let i ← price.len - 1#usize
          let i1 ← ({ slice := s1 } : alloc.vec.Vec I64).index_usize i
          let i2 ← ({ slice := s1 } : alloc.vec.Vec I64).index_usize 0#usize
          let max_diff ← i1 - i2
          let hi ← max_diff + 1#i64
          Aegis.MaximumTastiness.maximum_tastiness_loop1 k { slice := s1 } 0#i64 hi) ⦃
          r => r.val = bsAux (sortV (lvals price.val)) k.val 0 (hiV (sortV (lvals price.val))) ⦄
        refine Aeneas.Std.WP.spec_bind (m := alloc.slice.Slice.sort core.cmp.OrdI64 v0.slice)
          (slice_sort_spec v0.slice) ?_
        intro s1 hs1
        have hv0' : v0.slice.val = price.val := hv0
        have hs1' : lvals s1.val = sortV (lvals price.val) := by rw [hs1, hv0']
        have hs1len : s1.val.length = price.length := by
          have h := congrArg List.length hs1'
          simp only [lvals, List.length_map, sortV_length] at h
          exact h
        have hval1 : ∀ x ∈ s1.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
          intro x hx
          have hx1 : x.val ∈ lvals s1.val := List.mem_map.mpr ⟨x, hx, rfl⟩
          rw [hs1'] at hx1
          obtain ⟨y, hy, hyv⟩ := List.mem_map.mp ((sortV_perm (lvals price.val)).mem_iff.mp hx1)
          rw [← hyv]
          exact h_price y hy
        step as ⟨ i, hi ⟩
        have hiv : i.val = price.length - 1 := by rw [hi, Slice.len_val]
        step as ⟨ i1, hi1 ⟩
        · show i.val < s1.val.length; omega
        have hb1 : i.val < s1.val.length := by rw [hs1len]; omega
        have h1v : i1.val = (s1.val[i.val]'hb1).val := by rw [hi1]; rfl
        have hi1v : i1.val = (sortV (lvals price.val)).getD (price.length - 1) 0 := by
          have hL : (lvals s1.val).getD i.val 0 = (s1.val[i.val]'hb1).val :=
            lvals_getD s1 i.val hb1
          rw [h1v, ← hL, hs1', hiv]
        have hi1b : 1 ≤ i1.val ∧ i1.val ≤ 1000000000 := by
          have hm : s1.val[i.val]'hb1 ∈ s1.val := List.getElem_mem hb1
          have h := hval1 _ hm
          rw [h1v]; exact h
        step as ⟨ i2, hi2 ⟩
        · show (0#usize).val < s1.val.length; rw [hs1len]; omega
        have hb2 : 0 < s1.val.length := by rw [hs1len]; omega
        have h2v : i2.val = (s1.val[0]'hb2).val := by rw [hi2]; rfl
        have hi2v : i2.val = (sortV (lvals price.val)).getD 0 0 := by
          have hL : (lvals s1.val).getD 0 0 = (s1.val[0]'hb2).val := lvals_getD s1 0 hb2
          rw [h2v, ← hL, hs1']
        have hi2b : 1 ≤ i2.val ∧ i2.val ≤ 1000000000 := by
          have hm : s1.val[0]'hb2 ∈ s1.val := List.getElem_mem hb2
          have h := hval1 _ hm
          rw [h2v]; exact h
        step as ⟨ md, hmd ⟩
        step as ⟨ hl, hhl ⟩
        have h0i : (0#i64).val = 0 := rfl
        have hhi : hl.val = hiV (sortV (lvals price.val)) := by
          rw [hhl, hmd, hi1v, hi2v]
          unfold hiV
          rw [sortV_length]
          simp only [lvals, List.length_map]
        have hlen2 : 0 < (sortV (lvals price.val)).length := by
          rw [sortV_length]
          simp only [lvals, List.length_map]
          omega
        have hlast := sorted_getD_head_le_last (sortV (lvals price.val))
          (sortV_sorted (lvals price.val)) hlen2
        have hhib : hl.val ≤ 1000000001 := by
          rw [hhl, hmd]
          omega
        have hhlo : (0#i64).val ≤ hl.val := by
          rw [hhi]
          unfold hiV
          omega
        have hloop := loop1_spec ({ slice := s1 } : alloc.vec.Vec I64) k hval1
          (by show 0 < s1.val.length; omega)
          (by show s1.val.length ≤ 100000; omega)
          ((hl.val - (0#i64).val).toNat) 0#i64 hl hhlo (by rw [h0i]) hhib rfl
        refine Aeneas.Std.WP.spec_mono hloop ?_
        intro r hr
        rw [hr]
        show bsAux (lvals s1.val) k.val (0#i64).val hl.val
          = bsAux (sortV (lvals price.val)) k.val 0 (hiV (sortV (lvals price.val)))
        rw [hs1', hhi]
        rfl
    exact spec_exists_ok hwp

  /-- **S14 (invariance under a uniform shift).**  Shifting all prices by the same integer
  `c` (staying within `[1, 10^9]`) does not change the maximal tastiness. -/
  theorem spec_14 (price : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_n : 2 ≤ price.length)
      (h_k_lo : 2 ≤ k.val) (h_k_hi : k.val ≤ (price.length : ℤ))
      (h_len : price.length ≤ 100000)
      (h_price : ∀ x ∈ price.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (h_c : ∀ x ∈ vals price, 1 ≤ x + c ∧ x + c ≤ 1000000000) :
      ∃ r, maximum_tastiness price k = ok r ∧
        ∀ q : Slice Std.I64, vals q = (vals price).map (fun x => x + c) →
          ∃ r', maximum_tastiness q k = ok r' ∧ r'.val = r.val := by
    obtain ⟨r, hr, hrval⟩ := maximum_tastiness_spec price k h_n h_len h_price
    refine ⟨r, hr, ?_⟩
    intro q hq
    have hq_len : q.length = price.length := by
      have := congrArg List.length hq
      simpa [vals] using this
    have hq_price : ∀ x ∈ q.val, 1 ≤ x.val ∧ x.val ≤ 1000000000 := by
      intro x hx
      have h1 : x.val ∈ vals q := by
        simp only [vals]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hq] at h1
      obtain ⟨y, hy, hyc⟩ := List.mem_map.mp h1
      obtain ⟨h2a, h2b⟩ := h_c y hy
      constructor <;> omega
    have hq_n : 2 ≤ q.length := by rw [hq_len]; exact h_n
    have hq_l : q.length ≤ 100000 := by rw [hq_len]; exact h_len
    obtain ⟨r', hr', hr'val⟩ := maximum_tastiness_spec q k hq_n hq_l hq_price
    refine ⟨r', hr', ?_⟩
    have hs : sortV (vals q) = (sortV (vals price)).map (fun x => x + c) := by
      rw [hq, sortV_shift]
    have hlen2 : 0 < (sortV (vals price)).length := by
      rw [sortV_length]
      simp only [vals, List.length_map]
      exact Nat.lt_of_lt_of_le (by decide) h_n
    have key : bsAux (sortV (vals q)) k.val 0 (hiV (sortV (vals q)))
        = bsAux (sortV (vals price)) k.val 0 (hiV (sortV (vals price))) := by
      rw [hs, hiV_shift]
      exact bsAux_shift c (sortV (vals price)) hlen2 k.val 0 (hiV (sortV (vals price)))
    rw [hr'val, hrval]
    exact key

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

theorem probeSlot : True := by
  trivial

