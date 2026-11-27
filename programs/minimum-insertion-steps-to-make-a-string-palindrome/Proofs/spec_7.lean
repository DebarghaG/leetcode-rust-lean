import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_7` (minimum-insertion-steps-to-make-a-string-palindrome).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false
  set_option maxHeartbeats 4000000

  namespace AegisSpec.MinInsertions

  /-!
  ### Conventions

  `min_insertions` takes an Aeneas slice `s : Slice U8`.  The byte string held by the slice is
  `s.val : List U8`, and `len(s)` of the informal specification is `s.val.length`
  (see `slice_length_eq_val`); the ASCII code of a byte `b` is `b.val : Nat` and the numeric
  result of a call is `r.val : Int` for a returned `r : I64`.
  -/

  /-! ### Helper notions used by the specifications -/

  /-- `s.length` is the length of the list underlying the slice `s`. -/
  theorem slice_length_eq_val {α : Type} (s : Slice α) : s.length = s.val.length := by
    simp [Slice.length]

  /-- `b` is the ASCII code of a lowercase English letter, i.e. `97 ≤ b ≤ 122`. -/
  def isLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  /-- `l` is a palindrome: `l[j] = l[len(l) - 1 - j]` for every index `j` in range. -/
  def isPalindrome (l : List U8) : Prop :=
    ∀ (j : Nat), (hj : j < l.length) → l[j] = l[l.length - 1 - j]

  /-- `s` occurs in `t` as a subsequence: there are indices
  `idx 0 < idx 1 < … < idx (len s - 1)` inside `t` carrying the bytes of `s` in order. -/
  def isSubsequence (s t : List U8) : Prop :=
    ∃ idx : Nat → Nat,
      (∀ (a : Nat), a < s.length → idx a < t.length) ∧
        (∀ (a b : Nat), a < b → b < s.length → idx a < idx b) ∧
          (∀ (a : Nat), a < s.length → t[idx a]? = s[a]?)

  /-- `s` has a palindromic supersequence of length `len s + k`: there is a byte string `t`
  with `len t = len s + k`, `t` palindromic and `s` a subsequence of `t`. -/
  def hasPalindromicSupersequence (s : List U8) (k : Nat) : Prop :=
    ∃ t : List U8, t.length = s.length + k ∧ isPalindrome t ∧ isSubsequence s t

  /-- `s` has a palindromic subsequence of size `m`, witnessed by indices
  `i_0 < i_1 < … < i_(m-1)` with `s[i_a] = s[i_(m-1-a)]` for every `a < m`. -/
  def isPalindromicSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → s[i a]? = s[i (m - 1 - a)]?)

  /-- `s` has a common subsequence with its reversal of size `m`, witnessed by indices
  `i_0 < i_1 < … < i_(m-1)` and `j_0 < j_1 < … < j_(m-1)` with
  `s[i_a] = s[len(s) - 1 - j_a]` for every `a < m`. -/
  def isCommonSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i j : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → j a < s.length) ∧
            (∀ (a b : Nat), a < b → b < m → j a < j b) ∧
              (∀ (a : Nat), a < m → s[i a]? = s[s.length - 1 - j a]?)

  /-! ### Specifications -/

  /-! ### Auxiliary definitions for the proof of `spec_S10` -/

  /-- The substring of `l` from index `a` to index `b` (both inclusive). -/
  def subList (l : List U8) (a b : Nat) : List U8 := (l.drop a).take (b + 1 - a)

  /-- The number of insertions needed to turn `l` into a palindrome, defined by the
  same recursion as the dynamic program: if the two end bytes agree we strip them,
  otherwise we pay one insertion and keep the cheaper of the two shortenings. -/
  def minIns (l : List U8) : Nat :=
    if _ : l.length ≤ 1 then 0
    else if l[0]? = l[l.length - 1]? then
      minIns ((l.drop 1).take (l.length - 2))
    else 1 + min (minIns (l.drop 1)) (minIns (l.take (l.length - 1)))
  termination_by l.length
  decreasing_by
    all_goals simp only [List.length_take, List.length_drop]
    all_goals omega

  theorem minIns_le_length (l : List U8) : minIns l ≤ l.length := by
    induction l using minIns.induct with
    | case1 l h =>
      rw [minIns.eq_def]
      rw [dif_pos h]
      omega
    | case2 l h heq ih =>
      rw [minIns.eq_def]
      rw [dif_neg h, if_pos heq]
      refine ih.trans ?_
      simp only [List.length_take, List.length_drop]
      omega
    | case3 l h heq ih1 ih2 =>
      rw [minIns.eq_def]
      rw [dif_neg h, if_neg heq]
      simp only [List.length_take, List.length_drop] at ih1 ih2 ⊢
      omega

  theorem subList_length_le (l : List U8) (a b : Nat) : (subList l a b).length ≤ l.length := by
    simp only [subList, List.length_take, List.length_drop]
    omega

  theorem subList_length_eq (l : List U8) {a b : Nat} (ha : a ≤ b + 1) (hb : b < l.length) :
      (subList l a b).length = b + 1 - a := by
    simp only [subList, List.length_take, List.length_drop]
    omega

  theorem subList_getElem? (l : List U8) (a b i : Nat) :
      (subList l a b)[i]? = if i < b + 1 - a then l[a + i]? else none := by
    simp only [subList, List.getElem?_take, List.getElem?_drop]

  theorem subList_drop_one (l : List U8) (a b : Nat) :
      (subList l a b).drop 1 = subList l (a + 1) b := by
    simp only [subList, List.drop_take, List.drop_drop, Nat.add_comm 1 a]
    congr 1

  theorem subList_take_pred (l : List U8) {a b : Nat} (hab : a < b) (hb : b < l.length) :
      (subList l a b).take ((subList l a b).length - 1) = subList l a (b - 1) := by
    have h : (subList l a b).length - 1 = b - a := by
      rw [subList_length_eq l (by omega) hb]; omega
    rw [h]
    simp only [subList, List.take_take]
    rw [Nat.min_eq_left (by omega)]
    congr 1
    omega

  theorem subList_interior (l : List U8) {a b : Nat} (hab : a < b) (hb : b < l.length) :
      List.take ((subList l a b).length - 2) ((subList l a b).drop 1) =
        subList l (a + 1) (b - 1) := by
    have h : (subList l a b).length - 2 = b - a - 1 := by
      rw [subList_length_eq l (by omega) hb]; omega
    rw [h, subList_drop_one]
    simp only [subList, List.take_take]
    rw [Nat.min_eq_left (by omega)]
    congr 1
    omega

  theorem subList_getElem?_zero (l : List U8) {a b : Nat} (ha : a < b) :
      (subList l a b)[0]? = l[a]? := by
    rw [subList_getElem?]
    simp only [Nat.add_zero]
    rw [if_pos (by omega)]

  theorem subList_getElem?_last (l : List U8) {a b : Nat} (ha : a < b) (hb : b < l.length) :
      (subList l a b)[(subList l a b).length - 1]? = l[b]? := by
    rw [subList_getElem?, subList_length_eq l (by omega) hb]
    rw [if_pos (by omega)]
    congr 1
    omega

  theorem minIns_subList_self (l : List U8) {a : Nat} (ha : a < l.length) :
      minIns (subList l a a) = 0 := by
    rw [minIns.eq_def]
    rw [dif_pos (by rw [subList_length_eq l (by omega) ha]; omega)]

  theorem minIns_subList_eq (l : List U8) {a b : Nat} (hab : a < b) (hb : b < l.length)
      (heq : l[a] = l[b]) :
      minIns (subList l a b) = minIns (subList l (a + 1) (b - 1)) := by
    have h0 := subList_getElem?_zero l hab
    have h1 := subList_getElem?_last l hab hb
    have hlen : 1 < (subList l a b).length := by
      rw [subList_length_eq l (by omega) hb]; omega
    have hopt : (subList l a b)[0]? = (subList l a b)[(subList l a b).length - 1]? := by
      rw [h0, h1, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [heq]
    rw [minIns.eq_def]
    rw [dif_neg (by omega)]
    rw [if_pos hopt]
    congr 1
    exact subList_interior l hab hb

  theorem minIns_subList_ne (l : List U8) {a b : Nat} (hab : a < b) (hb : b < l.length)
      (hne : l[a] ≠ l[b]) :
      minIns (subList l a b) =
        1 + min (minIns (subList l (a + 1) b)) (minIns (subList l a (b - 1))) := by
    have h0 := subList_getElem?_zero l hab
    have h1 := subList_getElem?_last l hab hb
    have hlen : 1 < (subList l a b).length := by
      rw [subList_length_eq l (by omega) hb]; omega
    have hopt : ¬ ((subList l a b)[0]? = (subList l a b)[(subList l a b).length - 1]?) := by
      rw [h0, h1, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [ne_eq, Option.some.injEq]
      exact hne
    rw [minIns.eq_def]
    rw [dif_neg (by omega), if_neg hopt]
    congr 1
    rw [subList_drop_one, subList_take_pred l hab hb]

  theorem minIns_nil : minIns [] = 0 := by
    rw [minIns.eq_def]
    rw [dif_pos (by simp)]

  theorem subList_eq_nil {l : List U8} {a b : Nat} (h : b + 1 ≤ a) : subList l a b = [] := by
    simp [subList, Nat.sub_eq_zero_of_le h]

  theorem minIns_subList_eq_zero {l : List U8} {a b : Nat} (hab : a < b) (hb : b < l.length)
      (h1 : b = a + 1) (heq : l[a] = l[b]) : minIns (subList l a b) = 0 := by
    rw [minIns_subList_eq l hab hb heq]
    have hnil : subList l (a + 1) (b - 1) = [] := by
      apply subList_eq_nil
      omega
    rw [hnil, minIns_nil]

  theorem subList_full {l : List U8} (h : 0 < l.length) : subList l 0 (l.length - 1) = l := by
    simp [subList]
    omega

  /-- Writing to a cell of the table: the two-level `index_mut` used by the program. -/
  theorem getElem?_of_getElem {α : Type} (l : List α) (i : Nat) (h : i < l.length) (x : α)
      (hx : l[i] = x) : l[i]? = some x := by
    rw [← hx, List.getElem?_eq_getElem h]

  /-- Reading a cell of the table. -/
  theorem vec_index_eq {α : Type} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
      alloc.vec.Vec.index_usize v i = ok (v.val[i.val]'h) := by
    simp only [alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq,
      List.getElem?_eq_getElem h]

  theorem index_mut_two (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Usize) (x : I64)
      (h1 : i.val < dp.val.length) (h2 : j.val < (dp.val[i.val]).val.length) :
      (do let (v, back) ← dp.index_mut_usize i
          let (_, back1) ← v.index_mut_usize j
          ok (back (back1 x))) = ok (dp.set i ((dp.val[i.val]).set j x)) := by
    have h1' : dp.val[i.val]? = some (dp.val[i.val]) := List.getElem?_eq_getElem h1
    have h2' : (dp.val[i.val]).val[j.val]? = some ((dp.val[i.val]).val[j.val]) :=
      List.getElem?_eq_getElem h2
    simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
      alloc.vec.Vec.getElem?_Nat_eq, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_ok,
      Aeneas.Std.uncurry_apply_pair, h1', h2']

  /-! ### Specification of the first (initialisation) loop -/

  theorem List.replicate_succ_sub {α : Type} (x : α) {j k : Nat} (h : j ≤ k) :
      List.replicate (k + 1 - j) x = List.replicate (k - j) x ++ [x] := by
    rw [show k + 1 - j = (k - j) + 1 from by omega, List.replicate_succ']

  @[step]
  theorem loop0_loop0_spec (n : Usize) (row : alloc.vec.Vec I64) (j : Usize) (hn : n.val ≤ 500)
      (hj : j.val ≤ n.val) (hrow : row.val.length + (n.val - j.val) ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ (v : alloc.vec.Vec I64) =>
        v.val = row.val ++ List.replicate (n.val - j.val) (0#i64) ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0
    apply loop.spec_decr_nat (measure := fun p : alloc.vec.Vec I64 × Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec I64 × Usize =>
        p.1.val = row.val ++ List.replicate (p.2.val - j.val) (0#i64) ∧
        j.val ≤ p.2.val ∧ p.2.val ≤ n.val)
      (post := fun (v : alloc.vec.Vec I64) =>
        v.val = row.val ++ List.replicate (n.val - j.val) (0#i64))
    · rintro ⟨row1, j1⟩ ⟨hr, h1, h2⟩
      simp at hr h1 h2
      unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
      step*
      · rename_i hlt hrow1 hrow2
        refine ⟨?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
        rw [row1_post, j1_post, hr, List.replicate_succ_sub (h := by scalar_tac),
          List.append_assoc]
    · simp [hj]

  /-! ### The dynamic-programming table as a matrix of integers -/

  /-- The rows of the table `dp`, as a list of lists of integers. -/
  def matVal (dp : List (alloc.vec.Vec I64)) : List (List I64) := dp.map (fun r => r.val)

  /-- The `(a, b)`-th cell of the matrix `m`, as an integer. -/
  def cellOf (m : List (List I64)) (a b : Nat) : Option Int :=
    (m[a]?).bind (fun row => (row[b]?).map (fun x => x.val))

  /-- The value of a cell, as an integer. -/
  def insVal (l : List U8) : Int := (minIns l : Int)

  /-- Invariant of the table once all sub-strings of length `< len` are computed. -/
  def DPInv (s : List U8) (n len : Nat) (m : List (List I64)) : Prop :=
    m.length = n ∧ (∀ r ∈ m, r.length = n) ∧
      ∀ a b, a ≤ b → b < n → b + 1 - a < len → cellOf m a b = some (insVal (subList s a b))

  /-- Invariant of the table during the inner loop (over `start`) for a fixed `len`:
  all cells with `b + 1 - a < len` are correct, and so are the cells of length exactly `len`
  whose start index is `< start`. -/
  def DPInvS (s : List U8) (n len start : Nat) (m : List (List I64)) : Prop :=
    m.length = n ∧ (∀ r ∈ m, r.length = n) ∧ start ≤ n ∧
      ∀ a b, a ≤ b → b < n → (b + 1 - a < len ∨ (b + 1 - a = len ∧ a < start)) →
        cellOf m a b = some (insVal (subList s a b))

  theorem matVal_length (dp : List (alloc.vec.Vec I64)) : (matVal dp).length = dp.length := by
    simp [matVal]

  theorem matVal_getElem? (dp : List (alloc.vec.Vec I64)) (a : Nat) :
      (matVal dp)[a]? = (dp[a]?).map (fun r => r.val) := by
    simp [matVal]

  theorem matVal_set (dp : List (alloc.vec.Vec I64)) (a : Usize) (r : alloc.vec.Vec I64) :
      matVal (dp.set a r) = (matVal dp).set a.val r.val := by
    simp only [matVal, List.map_set, alloc.vec.Vec.set_val_eq]

  theorem matVal_append (l1 l2 : List (alloc.vec.Vec I64)) :
      matVal (l1 ++ l2) = matVal l1 ++ matVal l2 := by
    simp [matVal]

  theorem matVal_singleton (r : alloc.vec.Vec I64) : matVal [r] = [r.val] := by
    simp [matVal]

  theorem cellOf_of_getElem? (m : List (List I64)) (a b : Nat) (row : List I64)
      (h : m[a]? = some row) : cellOf m a b = (row[b]?).map (fun x => x.val) := by
    simp [cellOf, h]

  theorem cellOf_congr_getElem? (m m' : List (List I64)) (a b : Nat) (h : m[a]? = m'[a]?) :
      cellOf m a b = cellOf m' a b := by
    simp [cellOf, h]

  theorem cellOf_eq_of_getElem? (m : List (List I64)) (a b : Nat) (row : List I64)
      (h : m[a]? = some row) (r : Int) (h2 : cellOf m a b = some r) :
      (row[b]?).map (fun x => x.val) = some r := by
    rw [← cellOf_of_getElem? m a b row h]
    exact h2

  theorem cellOf_update {m : List (List I64)} {a b : Nat} {row : List I64} {x : I64}
      (hrow : m[a]? = some row) (hb : b < row.length) (a' c : Nat) :
      cellOf (m.set a (row.set b x)) a' c =
        if a = a' ∧ b = c then some x.val else cellOf m a' c := by
    have ha : a < m.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hrow
      exact absurd hrow (by simp)
    by_cases h1 : a = a'
    · subst h1
      rw [cellOf_of_getElem? _ _ _ _ (List.getElem?_set_self (by simpa using ha)),
        cellOf_of_getElem? _ _ _ _ hrow]
      by_cases h2 : b = c
      · subst h2
        rw [List.getElem?_set_self hb]
        simp
      · rw [List.getElem?_set_ne (by omega : b ≠ c)]
        simp [h2]
    · rw [cellOf_congr_getElem? _ _ _ _ (List.getElem?_set_ne h1)]
      simp [h1]

  @[step]
  theorem loop0_spec (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Usize)
      (hn : n.val ≤ 500) (hi : i.val ≤ n.val)
      (hdp : (matVal dp.val).length + (n.val - i.val) ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n dp i ⦃
        (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        matVal v.val = matVal dp.val ++ List.replicate (n.val - i.val) (List.replicate n.val (0#i64)) ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        (matVal p.1.val).length = (matVal dp.val).length + (p.2.val - i.val) ∧
        matVal p.1.val = matVal dp.val ++
          List.replicate (p.2.val - i.val) (List.replicate n.val (0#i64)) ∧
        i.val ≤ p.2.val ∧ p.2.val ≤ n.val)
      (post := fun (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        matVal v.val = matVal dp.val ++
          List.replicate (n.val - i.val) (List.replicate n.val (0#i64)))
    · rintro ⟨dp1, j1⟩ ⟨h1, hr, h2, h3⟩
      simp at h1 hr h2 h3
      unfold Aegis.MinInsertions.min_insertions_loop0.body
      step*
      · rw [← matVal_length, h1]
        scalar_tac
      · refine ⟨?_, ?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
        · rw [dp1_post, matVal_append, matVal_singleton, i1_post, List.length_append, h1]
          simp only [List.length_cons, List.length_nil]
          scalar_tac
        · rw [dp1_post, matVal_append, matVal_singleton, hr, row_post, i1_post]
          simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append, List.replicate_zero,
            Nat.sub_zero]
          rw [List.replicate_succ_sub (h := by scalar_tac), List.append_assoc]
    · simp [hi]

  /-- One iteration of the inner loop of the dynamic program: writing the value `x` of the
  sub-string `s[start .. start + len - 1]` into the cell `(start, start + len - 1)` preserves
  the invariant. -/
  theorem DPInvS_step (s : List U8) {n len start : Nat} {m : List (List I64)} {row : List I64}
      {x : I64} (hinv : DPInvS s n len start m) (hrow : m[start]? = some row)
      (hx : x.val = insVal (subList s start (start + len - 1)))
      (hlen : 2 ≤ len) (hend : start + len ≤ n) :
      DPInvS s n len (start + 1) (m.set start (row.set (start + len - 1) x)) := by
    obtain ⟨hm, hrows, hstart, hcells⟩ := hinv
    have hstart_lt : start < m.length := by rw [hm]; omega
    have hmem : row ∈ m := List.mem_iff_getElem?.mpr ⟨start, hrow⟩
    have hrowlen : row.length = n := hrows row hmem
    have hb : start + len - 1 < row.length := by omega
    refine ⟨by rw [List.length_set, hm], ?_, by omega, ?_⟩
    · intro r hr
      rcases List.mem_or_eq_of_mem_set hr with h | h
      · exact hrows r h
      · rw [h, List.length_set]; exact hrowlen
    · intro a b hab hbn hcond
      by_cases hcell : start = a ∧ start + len - 1 = b
      · obtain ⟨rfl, rfl⟩ := hcell
        rw [cellOf_update hrow hb]
        simp only [and_self, if_true]
        rw [hx]
      · rw [cellOf_update hrow hb]
        simp only [hcell, if_false]
        apply hcells a b hab hbn
        rcases hcond with h | ⟨h, ha⟩
        · left; omega
        · right
          refine ⟨h, ?_⟩
          rcases Nat.lt_or_ge a start with hlt | hge
          · exact hlt
          · exfalso
            apply hcell
            exact ⟨by omega, by omega⟩

  /-! ### The inner loop of the dynamic program -/

  @[step]
  theorem loop1_loop0_spec (s : Slice U8) (n len : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (start : Usize)
      (hsn : s.val.length = n.val) (hn : n.val ≤ 500) (hlen : 2 ≤ len.val)
      (hlenle : len.val ≤ n.val)
      (hinv : DPInvS s.val n.val len.val start.val (matVal dp.val)) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start ⦃
        (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        DPInv s.val n.val (len.val + 1) (matVal v.val) ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        DPInvS s.val n.val len.val p.2.val (matVal p.1.val))
      (post := fun (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        DPInv s.val n.val (len.val + 1) (matVal v.val))
    · rintro ⟨dp1, j1⟩ hinv1
      have hinv1' : DPInvS s.val n.val len.val j1.val (matVal dp1.val) := hinv1
      unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
      step* 40
      · by_cases heq : i1 = i2
        · rw [if_pos heq]
          split_ifs with h2
          · have hguard : i ≤ n := by assumption
            obtain ⟨hm, hrows, hs, hcells⟩ := hinv1'
            have hend : «end».val = j1.val + len.val - 1 := by scalar_tac
            have hjle : j1.val + len.val ≤ n.val := by scalar_tac
            have hm' : dp1.val.length = n.val := by rw [← matVal_length]; exact hm
            have hrowslen : ∀ r ∈ dp1.val, r.val.length = n.val := by
              intro r hr
              apply hrows
              simp only [matVal]
              exact List.mem_map.mpr ⟨r, hr, rfl⟩
            have hb1 : j1.val < dp1.val.length := by scalar_tac
            have hb2 : «end».val < (dp1.val[j1.val]).val.length := by
              have := hrowslen _ (List.mem_iff_getElem.mpr ⟨j1.val, hb1, rfl⟩)
              scalar_tac
            have hget : (matVal dp1.val)[j1.val]? = some (dp1.val[j1.val]).val := by
              rw [matVal_getElem?, List.getElem?_eq_getElem hb1]
              rfl
            have hsi : s.val[j1.val] = s.val[«end».val] := by
              rw [← i1_post, ← i2_post]
              exact heq
            have hx : (0#i64).val =
                insVal (subList s.val j1.val (j1.val + len.val - 1)) := by
              rw [← hend, insVal,
                minIns_subList_eq_zero (a := j1.val) (b := «end».val)
                  (by scalar_tac) (by rw [hsn]; scalar_tac) (by scalar_tac) hsi]
              rfl
            rw [index_mut_two dp1 j1 «end» (0#i64) hb1 hb2]
            step* 40
            refine ⟨?_, by scalar_tac⟩
            rw [start1_post, alloc.vec.Vec.set_val_eq, matVal_set, alloc.vec.Vec.set_val_eq,
              hend]
            exact DPInvS_step s.val ⟨hm, hrows, hs, hcells⟩ hget hx hlen hjle
          · have hguard : i ≤ n := by assumption
            obtain ⟨hm, hrows, hs, hcells⟩ := hinv1'
            have hend : «end».val = j1.val + len.val - 1 := by scalar_tac
            have hjle : j1.val + len.val ≤ n.val := by scalar_tac
            have hm' : dp1.val.length = n.val := by rw [← matVal_length]; exact hm
            have hrowslen : ∀ r ∈ dp1.val, r.val.length = n.val := by
              intro r hr
              apply hrows
              simp only [matVal]
              exact List.mem_map.mpr ⟨r, hr, rfl⟩
            have hb1 : j1.val < dp1.val.length := by scalar_tac
            have hb2 : «end».val < (dp1.val[j1.val]).val.length := by
              have := hrowslen _ (List.mem_iff_getElem.mpr ⟨j1.val, hb1, rfl⟩)
              scalar_tac
            let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
            let* ⟨ v, v_post ⟩ ← alloc.vec.Vec.index_usize_spec
            let* ⟨ i4, i4_post, _i4_post1 ⟩ ← Usize.sub_spec
            have hvrow : v.val.length = n.val := by
              have hmem : v ∈ dp1.val := by
                rw [v_post]
                exact List.getElem_mem (by scalar_tac)
              exact hrowslen v hmem
            let* ⟨ i5, i5_post ⟩ ← alloc.vec.Vec.index_usize_spec
            have hsi : s.val[j1.val] = s.val[«end».val] := by
              rw [← i1_post, ← i2_post]
              exact heq
            have hxins : i5.val = insVal (subList s.val j1.val (j1.val + len.val - 1)) := by
              have hveq : v.val = (dp1.val[i3.val]).val := by simp only [v_post]
              have hcell := hcells (j1.val + 1) («end».val - 1) (by scalar_tac) (by scalar_tac)
                (Or.inl (by scalar_tac))
              have hrowv2 : (matVal dp1.val)[j1.val + 1]? = some (dp1.val[i3.val]).val := by
                rw [matVal_getElem?, ← i3_post,
                  List.getElem?_eq_getElem (show i3.val < dp1.val.length by scalar_tac)]
                rfl
              have hev := cellOf_eq_of_getElem? _ _ _ _ hrowv2 _ hcell
              obtain ⟨z, hz, hzv⟩ := Option.map_eq_some_iff.mp hev
              have hb3 : i4.val < v.val.length := by rw [hvrow, i4_post, hend]; scalar_tac
              have hz5 : v.val[«end».val - 1]? = some i5 := by
                rw [← i4_post, i5_post]
                exact List.getElem?_eq_getElem hb3
              rw [hveq] at hz5
              have hzi : i5 = z := (Option.some.inj (hz.symm.trans hz5)).symm
              rw [hzi, hzv, ← hend]
              simp only [insVal]
              rw [minIns_subList_eq s.val (a := j1.val) (b := «end».val)
                (by scalar_tac) (by rw [hsn]; scalar_tac) hsi]
            step* 40
            have hx : x = (dp1.val[j1.val], dp1.set j1) := Prod.ext x_post x_post1
            rw [hx]
            step* 60
            have hx2 : x = ((dp1.val[j1.val]).val[«end».val], (dp1.val[j1.val]).set «end») :=
              Prod.ext x_post x_post1
            rw [hx2]
            step* 40
            refine ⟨?_, by rw [start1_post]; scalar_tac⟩
            rw [start1_post, alloc.vec.Vec.set_val_eq, matVal_set, alloc.vec.Vec.set_val_eq,
              hend]
            exact DPInvS_step s.val ⟨hm, hrows, hs, hcells⟩
              (by rw [matVal_getElem?, List.getElem?_eq_getElem hb1]; rfl) hxins hlen hjle
        · rw [if_neg heq]
          obtain ⟨hm, hrows, hs, hcells⟩ := hinv1'
          have hend : «end».val = j1.val + len.val - 1 := by scalar_tac
          have hjle : j1.val + len.val ≤ n.val := by scalar_tac
          have hm' : dp1.val.length = n.val := by rw [← matVal_length]; exact hm
          have hrowslen : ∀ r ∈ dp1.val, r.val.length = n.val := by
            intro r hr
            apply hrows
            simp only [matVal]
            exact List.mem_map.mpr ⟨r, hr, rfl⟩
          have hb1 : j1.val < dp1.val.length := by scalar_tac
          have hb2 : «end».val < (dp1.val[j1.val]).val.length := by
            have := hrowslen _ (List.mem_iff_getElem.mpr ⟨j1.val, hb1, rfl⟩)
            scalar_tac
          have hmin_le : ∀ (a b : Nat), minIns (subList s.val a b) ≤ 500 := by
            intro a b
            have h2 := minIns_le_length (subList s.val a b)
            have h3 := subList_length_le s.val a b
            have h4 : s.val.length ≤ 500 := by rw [hsn]; exact hn
            omega
          let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
          let* ⟨ v, v_post ⟩ ← alloc.vec.Vec.index_usize_spec
          have hvrow : v.val.length = n.val := by
            have hmem : v ∈ dp1.val := by
              rw [v_post]
              exact List.getElem_mem (by scalar_tac)
            exact hrowslen v hmem
          let* ⟨ left, left_post ⟩ ← alloc.vec.Vec.index_usize_spec
          let* ⟨ v1, v1_post ⟩ ← alloc.vec.Vec.index_usize_spec
          let* ⟨ i4, i4_post, _i4_post1 ⟩ ← Usize.sub_spec
          have hv1row : v1.val.length = n.val := by
            have hmem : v1 ∈ dp1.val := by
              rw [v1_post]
              exact List.getElem_mem (by scalar_tac)
            exact hrowslen v1 hmem
          let* ⟨ right, right_post ⟩ ← alloc.vec.Vec.index_usize_spec
          have hne : s.val[j1.val] ≠ s.val[«end».val] := by
            intro h
            apply heq
            rw [i1_post, i2_post]
            exact h
          have hA : left.val = insVal (subList s.val (j1.val + 1) «end».val) := by
            have hveq : v.val = (dp1.val[i3.val]).val := by simp only [v_post]
            have hcellA := hcells (j1.val + 1) «end».val (by scalar_tac) (by scalar_tac)
              (Or.inl (by scalar_tac))
            have hrowv2 : (matVal dp1.val)[j1.val + 1]? = some (dp1.val[i3.val]).val := by
              rw [matVal_getElem?, ← i3_post,
                List.getElem?_eq_getElem (show i3.val < dp1.val.length by scalar_tac)]
              rfl
            have hevA := cellOf_eq_of_getElem? _ _ _ _ hrowv2 _ hcellA
            obtain ⟨zA, hzA, hzvA⟩ := Option.map_eq_some_iff.mp hevA
            have hb5 : «end».val < v.val.length := by rw [hvrow]; scalar_tac
            have hz5A : v.val[«end».val]? = some left := by
              rw [left_post, List.getElem?_eq_getElem hb5]
            rw [hveq] at hz5A
            have hleft : left = zA := (Option.some.inj (hzA.symm.trans hz5A)).symm
            rw [hleft, hzvA]
          have hB : right.val = insVal (subList s.val j1.val («end».val - 1)) := by
            have hveq1 : v1.val = (dp1.val[j1.val]).val := by simp only [v1_post]
            have hcellB := hcells j1.val («end».val - 1) (by scalar_tac) (by scalar_tac)
              (Or.inl (by scalar_tac))
            have hrowv1 : (matVal dp1.val)[j1.val]? = some (dp1.val[j1.val]).val := by
              rw [matVal_getElem?, List.getElem?_eq_getElem hb1]
              rfl
            have hevB := cellOf_eq_of_getElem? _ _ _ _ hrowv1 _ hcellB
            obtain ⟨zB, hzB, hzvB⟩ := Option.map_eq_some_iff.mp hevB
            have hb6 : i4.val < v1.val.length := by rw [hv1row, i4_post, hend]; scalar_tac
            have hz5B : v1.val[i4.val]? = some right := by
              rw [right_post, List.getElem?_eq_getElem hb6]
            rw [hveq1, i4_post] at hz5B
            have hright : right = zB := (Option.some.inj (hzB.symm.trans hz5B)).symm
            rw [hright, hzvB]
          have hA2 : (minIns (subList s.val (j1.val + 1) «end».val) : Int) = left.val :=
            hA.symm
          have hB2 : (minIns (subList s.val j1.val («end».val - 1)) : Int) = right.val :=
            hB.symm
          by_cases hlt : left < right
          · rw [if_pos hlt]
            let* ⟨ i5, i5_post ⟩ ← I64.add_spec
            have hxins : i5.val = insVal (subList s.val j1.val (j1.val + len.val - 1)) := by
              have hltv : left.val < right.val := hlt
              have hAB : minIns (subList s.val (j1.val + 1) «end».val) <
                  minIns (subList s.val j1.val («end».val - 1)) := by
                have h2 : (minIns (subList s.val (j1.val + 1) «end».val) : Int) <
                    (minIns (subList s.val j1.val («end».val - 1)) : Int) := by
                  rw [hA2, hB2]
                  exact hltv
                omega
              rw [i5_post, ← hend, insVal,
                minIns_subList_ne s.val (a := j1.val) (b := «end».val)
                  (by scalar_tac) (by rw [hsn]; scalar_tac) hne, hA, insVal,
                Nat.min_eq_left (le_of_lt hAB)]
              push_cast
              omega
            step* 40
            have hx : x = (dp1.val[j1.val], dp1.set j1) := Prod.ext x_post x_post1
            rw [hx]
            step* 60
            have hx2 : x = ((dp1.val[j1.val]).val[«end».val], (dp1.val[j1.val]).set «end») :=
              Prod.ext x_post x_post1
            rw [hx2]
            step* 40
            refine ⟨?_, by rw [start1_post]; scalar_tac⟩
            rw [start1_post, alloc.vec.Vec.set_val_eq, matVal_set, alloc.vec.Vec.set_val_eq,
              hend]
            exact DPInvS_step s.val ⟨hm, hrows, hs, hcells⟩
              (by rw [matVal_getElem?, List.getElem?_eq_getElem hb1]; rfl) hxins hlen hjle
          · rw [if_neg hlt]
            let* ⟨ i5, i5_post ⟩ ← I64.add_spec
            have hxins : i5.val = insVal (subList s.val j1.val (j1.val + len.val - 1)) := by
              have hge : right.val ≤ left.val := by
                have hn : ¬ left.val < right.val := hlt
                omega
              have hBA : minIns (subList s.val j1.val («end».val - 1)) ≤
                  minIns (subList s.val (j1.val + 1) «end».val) := by
                have h2 : (minIns (subList s.val j1.val («end».val - 1)) : Int) ≤
                    (minIns (subList s.val (j1.val + 1) «end».val) : Int) := by
                  rw [hB2, hA2]
                  exact hge
                omega
              rw [i5_post, ← hend, insVal,
                minIns_subList_ne s.val (a := j1.val) (b := «end».val)
                  (by scalar_tac) (by rw [hsn]; scalar_tac) hne, hB, insVal,
                Nat.min_eq_right hBA]
              push_cast
              omega
            step* 40
            have hx : x = (dp1.val[j1.val], dp1.set j1) := Prod.ext x_post x_post1
            rw [hx]
            step* 60
            have hx2 : x = ((dp1.val[j1.val]).val[«end».val], (dp1.val[j1.val]).set «end») :=
              Prod.ext x_post x_post1
            rw [hx2]
            step* 40
            refine ⟨?_, by rw [start1_post]; scalar_tac⟩
            rw [start1_post, alloc.vec.Vec.set_val_eq, matVal_set, alloc.vec.Vec.set_val_eq,
              hend]
            exact DPInvS_step s.val ⟨hm, hrows, hs, hcells⟩
              (by rw [matVal_getElem?, List.getElem?_eq_getElem hb1]; rfl) hxins hlen hjle
      · rename_i hge
        obtain ⟨hm, hrows, hs, hcells⟩ := hinv1'
        have hge' : n.val < j1.val + len.val := by scalar_tac
        refine ⟨hm, hrows, ?_⟩
        intro a b hab hbn hcond
        apply hcells a b hab hbn
        rcases Nat.lt_or_ge (b + 1 - a) len.val with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by omega⟩
    · exact hinv

  /-- **S1 (main, functional).** When `min_insertions s` returns `r`, `r` is the least
  nonnegative `k` such that `s` can be extended to a palindrome by inserting `k` bytes. -/
  theorem spec_S1 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧
          hasPalindromicSupersequence s.val r.val.toNat ∧
            (∀ k, hasPalindromicSupersequence s.val k → r.val.toNat ≤ k) := by
    sorry

  /-- **S2 (no failure).** `min_insertions` never fails on a nonempty lowercase input. -/
  theorem spec_S2 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∃ r, Aegis.MinInsertions.min_insertions s = ok r := by
    sorry

  /-- **S3 (bounds).** The returned number of insertions lies in `[0, len(s) - 1]`. -/
  theorem spec_S3 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 := by
    sorry

  /-- **S4 (edge case).** The result is `0` exactly when `s` is already a palindrome. -/
  theorem spec_S4 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r → (r.val = 0 ↔ isPalindrome s.val) := by
    sorry

  /-- **S5 (relational, longest palindromic subsequence).** `r = len(s) - L` where `L` is the
  length of the longest palindromic subsequence of `s`. -/
  theorem spec_S5 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ L : Nat,
          isPalindromicSubseqSize s.val L ∧
            (∀ m, isPalindromicSubseqSize s.val m → m ≤ L) ∧
              r.val = (s.val.length : Int) - (L : Int) := by
    sorry

  /-- **S8 (invariance under reversal).** Reversing the input leaves the answer unchanged. -/
  theorem spec_S8 (s t : Slice U8)
      (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 500)
      (ht_lower : 1 ≤ t.val.length) (ht_upper : t.val.length ≤ 500)
      (hlen : t.val.length = s.val.length)
      (hlower_s : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlower_t : ∀ (i : Nat), (hi : i < t.val.length) → isLowerAscii (t.val[i]))
      (hrev : ∀ (i : Nat), (hi : i < s.val.length) →
        t.val[i] = s.val[s.val.length - 1 - i]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions t = ok q → r = q := by
    sorry

  /-! ### Correctness of the dynamic program (main work-horse) -/

  /-- The table after the initialization loop: `n` rows of `n` zeros. -/
  @[step]
  theorem loop1_spec (s : Slice U8) (n len : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hsn : s.val.length = n.val) (hn : n.val ≤ 500) (hlen2 : 2 ≤ len.val)
      (hlen : len.val ≤ n.val + 1)
      (hinv : DPInv s.val n.val len.val (matVal dp.val)) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp len ⦃
        (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        DPInv s.val n.val (n.val + 1) (matVal v.val) ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val + 1 - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        DPInv s.val n.val p.2.val (matVal p.1.val) ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1)
      (post := fun (v : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        DPInv s.val n.val (n.val + 1) (matVal v.val))
    · rintro ⟨dp1, len1⟩ ⟨hinv1, h2le, hle⟩
      simp only at hinv1 h2le hle
      unfold Aegis.MinInsertions.min_insertions_loop1.body
      step*
      obtain ⟨hm, hrows, hcells⟩ := hinv1
      refine ⟨hm, hrows, by scalar_tac, ?_⟩
      intro a b hab hbn hcond
      rcases hcond with h | ⟨h, h0⟩
      · exact hcells a b hab hbn h
      · exact absurd h0 (by simp)
    · exact ⟨hinv, hlen2, hlen⟩

  /-- The result of the program is the value computed by `minIns` on the input. -/
  @[step]
  theorem final_spec (s : Slice U8) (dp1 : alloc.vec.Vec (alloc.vec.Vec I64))
      (hsn : s.val.length = (Slice.len s).val) (hn2 : 2 ≤ (Slice.len s).val)
      (hinv : DPInv s.val (Slice.len s).val ((Slice.len s).val + 1) (matVal dp1.val)) :
      (do let v ← alloc.vec.Vec.index_usize dp1 0#usize
          let i ← Slice.len s - 1#usize
          alloc.vec.Vec.index_usize v i) ⦃ (r : I64) => r.val = insVal s.val ⦄ := by
    obtain ⟨hm, hrows, hcells⟩ := hinv
    have hlen : 0 < dp1.val.length := by
      have h1 : dp1.val.length = (Slice.len s).val := by rw [← matVal_length]; exact hm
      rw [h1]; omega
    let* ⟨ v, v_post ⟩ ← alloc.vec.Vec.index_usize_spec
    let* ⟨ i, i_post, _i_post1 ⟩ ← Usize.sub_spec
    have hget0 : (matVal dp1.val)[0]? = some v.val := by
      rw [matVal_getElem?, List.getElem?_eq_getElem hlen, v_post]
      rfl
    have hvlen : v.val.length = (Slice.len s).val :=
      hrows _ (List.mem_iff_getElem?.mpr ⟨0, hget0⟩)
    have hb1 : i.val < v.val.length := by rw [hvlen, i_post]; omega
    let* ⟨ r, r_post ⟩ ← alloc.vec.Vec.index_usize_spec
    have hcell := hcells 0 i.val (by omega) (by rw [← hvlen]; exact hb1)
      (by omega)
    have hev := cellOf_eq_of_getElem? _ _ _ _ hget0 _ hcell
    have hvi : v.val[i.val]? = some r := by
      rw [r_post, List.getElem?_eq_getElem hb1]
    rw [hvi] at hev
    have h1 : r.val = insVal (subList s.val 0 i.val) := Option.some.inj hev
    rw [h1]
    have hsub : subList s.val 0 i.val = s.val := by
      rw [i_post, ← hsn]
      exact subList_full (by omega)
    rw [hsub]

  /-- The result of the program is the value computed by `minIns` on the input. -/
  theorem min_insertions_spec (s : Slice U8) (hn : s.val.length ≤ 500) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r → r.val = insVal s.val := by
    intro r hr
    have hsn : s.val.length = (Slice.len s).val := (Aeneas.Std.Slice.len_val s).symm
    have hnl : (Slice.len s).val ≤ 500 := by rw [Aeneas.Std.Slice.len_val]; exact hn
    have hspec : Aegis.MinInsertions.min_insertions s ⦃ (r : I64) => r.val = insVal s.val ⦄ := by
      unfold Aegis.MinInsertions.min_insertions
      step* 3
      · rw [insVal, minIns.eq_def, dif_pos (by rw [hsn]; scalar_tac)]
        rfl
      · simpa [matVal] using hnl
      · have hdpv : matVal dp.val =
            List.replicate (Slice.len s).val (List.replicate (Slice.len s).val (0#i64)) := by
          rw [dp_post]
          simp [matVal]
        refine ⟨?_, ?_, ?_⟩
        · rw [hdpv]
          simp
        · intro r hr'
          rw [hdpv, List.mem_replicate] at hr'
          obtain ⟨-, rfl⟩ := hr'
          simp
        · intro a b hab hbn hcond
          have hab' : a = b := by scalar_tac
          subst hab'
          have ha : a < s.val.length := by rw [hsn]; exact hbn
          have hget1 : (List.replicate (Slice.len s).val
              (List.replicate (Slice.len s).val (0#i64)))[a]? =
              some (List.replicate (Slice.len s).val (0#i64)) := by
            rw [List.getElem?_replicate, if_pos hbn]
          have hget2 : (List.replicate (Slice.len s).val (0#i64))[a]? = some (0#i64) := by
            rw [List.getElem?_replicate, if_pos hbn]
          simp only [cellOf, hdpv, hget1, Option.bind_some, hget2, Option.map_some]
          rw [insVal, minIns_subList_self s.val (a := a) ha]
          rfl
      · exact final_spec s dp1 hsn (by scalar_tac) dp1_post
    rw [hr] at hspec
    simpa using hspec


  /-- **S10 (relational, trimming equal ends).** If the first and last bytes of `s` agree, then
  the answer for `s` equals the answer for the inner slice `u` of length `len(s) - 2` with
  `u[i] = s[i+1]`. -/
  theorem spec_7 (s u : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen3 : 3 ≤ s.val.length)
      (hends : s.val[0] = s.val[s.val.length - 1])
      (hu_len : u.val.length = s.val.length - 2)
      (hu_val : ∀ (i : Nat), (hi : i < u.val.length) → u.val[i] = s.val[i + 1]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions u = ok q → r = q := by
    intro r q hr hq
    have hu_le : u.val.length ≤ 500 := by rw [hu_len]; omega
    have hr' : r.val = insVal s.val := min_insertions_spec s hlen_upper r hr
    have hq' : q.val = insVal u.val := min_insertions_spec u hu_le q hq
    have hsub : subList s.val 1 (s.val.length - 2) = u.val := by
      apply List.ext_getElem?
      intro i
      rw [subList_getElem?]
      by_cases hi : i < s.val.length - 2
      · rw [if_pos (by omega)]
        have hu : i < u.val.length := by rw [hu_len]; omega
        rw [List.getElem?_eq_getElem hu,
          List.getElem?_eq_getElem (by omega : 1 + i < s.val.length), hu_val i hu]
        simp [Nat.add_comm]
      · rw [if_neg (by omega)]
        rw [List.getElem?_eq_none (by rw [hu_len]; omega)]
    have hmin : minIns s.val = minIns u.val := by
      rw [← subList_full (l := s.val) (by omega)]
      rw [minIns_subList_eq s.val (a := 0) (b := s.val.length - 1) (by omega) (by omega) hends]
      rw [show s.val.length - 1 - 1 = s.val.length - 2 by omega, hsub]
    exact IScalar.eq_of_val_eq (by rw [hr', hq', insVal, insVal, hmin])

  /-- **S11 (relational, unequal ends).** If the first and last bytes of `s` differ, then
  `r = 1 + min (answer for s[1..]) (answer for s[..len(s)-1])`, where `a` is the slice of length
  `len(s) - 1` with `a[i] = s[i+1]` and `b` is the slice of length `len(s) - 1` with
  `b[i] = s[i]`. -/
  theorem spec_S11 (s a b : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen2 : 2 ≤ s.val.length)
      (hne : s.val[0] ≠ s.val[s.val.length - 1])
      (ha_len : a.val.length = s.val.length - 1)
      (ha_val : ∀ (i : Nat), (hi : i < a.val.length) → a.val[i] = s.val[i + 1])
      (hb_len : b.val.length = s.val.length - 1)
      (hb_val : ∀ (i : Nat), (hi : i < b.val.length) → b.val[i] = s.val[i]) :
      ∀ r ra rb, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions a = ok ra →
          Aegis.MinInsertions.min_insertions b = ok rb → r.val = 1 + min ra.val rb.val := by
    sorry

  /-- **S12 (relational, longest common subsequence with the reversal).**
  `r = len(s) - C` where `C` is the largest `m` for which there are increasing index sequences
  `i_0 < … < i_(m-1)` and `j_0 < … < j_(m-1)` with `s[i_a] = s[len(s)-1-j_a]`. -/
  theorem spec_S12 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ C : Nat,
          isCommonSubseqSize s.val C ∧
            (∀ m, isCommonSubseqSize s.val m → m ≤ C) ∧
              r.val = (s.val.length : Int) - (C : Int) := by
    sorry

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry


  /-! ### Sanity checks for the helper notions (not part of the specification) -/

  example : isPalindrome [97#u8, 98#u8, 97#u8] := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega

  example : ¬ isPalindrome [97#u8, 98#u8] := by
    intro h
    have h0 := h 0 (by simp)
    simp at h0

  end AegisSpec.MinInsertions
