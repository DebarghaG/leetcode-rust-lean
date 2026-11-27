import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_6` (minimum-insertion-steps-to-make-a-string-palindrome).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

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

  /-! ### Auxiliary development: the interval DP computed by `min_insertions` -/

  /-- `dpVal l i j` is the value of the interval DP cell `(i, j)`: the minimum number of
  insertions needed to turn `l[i..j]` into a palindrome. -/
  def dpVal (l : List U8) (i j : Nat) : Nat :=
    if h : i < j then
      (if l[i]? = l[j]? then dpVal l (i + 1) (j - 1)
       else 1 + min (dpVal l (i + 1) j) (dpVal l i (j - 1)))
    else 0
  termination_by j - i
  decreasing_by all_goals omega

  theorem dpVal_of_lt {l : List U8} {i j : Nat} (h : i < j) :
      dpVal l i j =
        (if l[i]? = l[j]? then dpVal l (i + 1) (j - 1)
         else 1 + min (dpVal l (i + 1) j) (dpVal l i (j - 1))) := by
    rw [dpVal]
    simp only [dite_eq_left h]

  theorem dpVal_of_not_lt {l : List U8} {i j : Nat} (h : ¬ i < j) : dpVal l i j = 0 := by
    rw [dpVal]
    simp only [dite_eq_right h]

  /-- Reversal symmetry of the interval DP: mirroring the interval mirrors the value. -/
  theorem dpVal_rev (l m : List U8) (hL : m.length = l.length)
      (hmir : ∀ a, a < m.length → m[a]? = l[l.length - 1 - a]?)
      (i j : Nat) (hj : j < l.length) :
      dpVal m i j = dpVal l (l.length - 1 - j) (l.length - 1 - i) := by
    have hlen : l.length = m.length := hL.symm
    suffices h : ∀ k, ∀ i j : Nat, j - i ≤ k → j < l.length →
        dpVal m i j = dpVal l (l.length - 1 - j) (l.length - 1 - i) from h _ i j (le_refl _) hj
    intro k
    induction k with
    | zero =>
      intro i j hk hj
      have hji : j ≤ i := by omega
      rw [dpVal_of_not_lt (by omega : ¬ i < j),
        dpVal_of_not_lt (l := l) (i := l.length - 1 - j) (j := l.length - 1 - i) (by omega)]
    | succ k ih =>
      intro i j hk hj
      by_cases hij : i < j
      · have him : i < m.length := by omega
        have hjm : j < m.length := by omega
        rw [dpVal_of_lt hij, dpVal_of_lt (by omega : l.length - 1 - j < l.length - 1 - i)]
        rw [hmir i him, hmir j hjm]
        by_cases heq : l[l.length - 1 - i]? = l[l.length - 1 - j]?
        · rw [if_pos heq, if_pos heq.symm]
          have h1 : l.length - 1 - (j - 1) = l.length - 1 - j + 1 := by omega
          have h2 : l.length - 1 - (i + 1) = l.length - 1 - i - 1 := by omega
          rw [ih (i + 1) (j - 1) (by omega) (by omega), h1, h2]
        · rw [if_neg heq, if_neg (Ne.symm heq)]
          have h1 : l.length - 1 - j = l.length - 1 - j := rfl
          have h2 : l.length - 1 - (i + 1) = l.length - 1 - i - 1 := by omega
          have h3 : l.length - 1 - (j - 1) = l.length - 1 - j + 1 := by omega
          have h4 : l.length - 1 - i = l.length - 1 - i := rfl
          rw [ih (i + 1) j (by omega) hj, ih i (j - 1) (by omega) (by omega), h1, h2, h3, h4,
            Nat.min_comm]
      · have hji : j ≤ i := by omega
        rw [dpVal_of_not_lt hij,
          dpVal_of_not_lt (l := l) (i := l.length - 1 - j) (j := l.length - 1 - i) (by omega)]

  /-! #### Representing the DP table of the extracted program -/

  /-- The row-initialisation loop fills a row with `n` zeroes. -/
  theorem loop0_loop0_spec (n : Usize) (row : alloc.vec.Vec I64) (j : Usize)
      (hjn : j.val ≤ n.val) (hn : n.val ≤ 500) (hrowlen : row.val.length = j.val) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ row' =>
        row'.val = row.val ++ List.replicate (n.val - j.val) 0#i64 ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0
    apply loop.spec_decr_nat (measure := fun p : alloc.vec.Vec I64 × Usize => n.val - p.2.val)
      (inv := fun p => p.2.val ≤ n.val ∧
        p.1.val = row.val ++ List.replicate (p.2.val - j.val) 0#i64 ∧
        p.1.val.length = p.2.val)
    · intro p hp
      obtain ⟨hpn, hpr, hplen⟩ := hp
      simp only [Aegis.MinInsertions.min_insertions_loop0_loop0.body]
      split
      · rename_i hlt
        have hlt' : p.2.val < n.val := by simpa using hlt
        have hjk : j.val ≤ p.2.val := by
          have h1 : p.1.val.length = row.val.length + (p.2.val - j.val) := by
            rw [hpr, List.length_append, List.length_replicate]
          omega
        step as ⟨row1, hrow1⟩
        step as ⟨j1, hj1⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hj1]; omega
        · have hrep : List.replicate (j1.val - j.val) 0#i64
              = List.replicate (p.2.val - j.val) 0#i64 ++ [0#i64] := by
            have e : p.2.val + 1 - j.val = (p.2.val - j.val) + 1 := by omega
            rw [hj1, e, List.replicate_succ']
          rw [hrow1, hpr, hrep, List.append_assoc]
        · rw [hrow1, hj1]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [hj1]; omega
      · rename_i hlt
        have hle : n.val ≤ p.2.val := by simpa using hlt
        have he : p.2.val = n.val := by omega
        simp only [WP.spec_ok]
        rw [hpr, he]
    · exact ⟨hjn, by simp, hrowlen⟩

  /-- Value of the entry `j` of a DP row. -/
  def rowCell (r : alloc.vec.Vec I64) (j : Nat) : Int := ((r.val[j]?).map (fun x => x.val)).getD 0

  /-- Value of the cell `(i, j)` of the DP table. -/
  def dpCell (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    ((dp.val[i]?).map (fun r => rowCell r j)).getD 0

  /-- Number of entries of a DP row. -/
  def rowLen (r : alloc.vec.Vec I64) : Nat := r.val.length

  theorem dpCell_row {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i : Nat}
      {r : alloc.vec.Vec I64} (h : dp.val[i]? = some r) (j : Nat) :
      dpCell dp i j = rowCell r j := by
    simp [dpCell, h]

  theorem rowCell_set (r : alloc.vec.Vec I64) (b : Usize) (x : I64)
      (hb : b.val < r.val.length) (j : Nat) :
      rowCell (r.set b x) j = if j = b.val then x.val else rowCell r j := by
    simp only [rowCell]
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases hjb : j = b.val
    · subst hjb
      rw [if_pos rfl, if_pos hb]
      simp
    · rw [if_neg (by omega : b.val ≠ j), if_neg hjb]

  theorem dpCell_set (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (a : Usize)
      (r : alloc.vec.Vec I64) (ha : a.val < dp.val.length) (i j : Nat) :
      dpCell (dp.set a r) i j = if i = a.val then rowCell r j else dpCell dp i j := by
    simp only [dpCell]
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases hia : i = a.val
    · subst hia
      rw [if_pos rfl, if_pos ha]
      simp
    · rw [if_neg (by omega : a.val ≠ i), if_neg hia]

  /-- The outer initialisation loop creates the `n × n` table of zeroes. -/
  theorem loop0_spec (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Usize)
      (hn : n.val ≤ 500) (hi : i.val ≤ n.val) (hdplen : dp.val.length = i.val) :
      Aegis.MinInsertions.min_insertions_loop0 n dp i ⦃ dp' =>
        dp'.val.map (fun r => r.val) = dp.val.map (fun r => r.val) ++
            List.replicate (n.val - i.val) (List.replicate n.val 0#i64) ∧
        dp'.val.length = n.val ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val - p.2.val)
      (inv := fun p => p.2.val ≤ n.val ∧
        p.1.val.map (fun r => r.val) = dp.val.map (fun r => r.val) ++
          List.replicate (p.2.val - i.val) (List.replicate n.val 0#i64) ∧
        p.1.val.length = p.2.val)
    · intro p hp
      obtain ⟨hpn, hpmap, hplen⟩ := hp
      simp only [Aegis.MinInsertions.min_insertions_loop0.body]
      split
      · rename_i hlt
        have hlt' : p.2.val < n.val := by simpa using hlt
        have hik : i.val ≤ p.2.val := by
          have h1 := congrArg List.length hpmap
          simp only [List.length_map, List.length_append, List.length_replicate] at h1
          omega
        step with loop0_loop0_spec as ⟨row, hrow⟩
        step as ⟨dp1, hdp1⟩
        step as ⟨i1, hi1⟩
        have hrow' : row.val = List.replicate n.val 0#i64 := by rw [hrow]; simp
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hi1]; omega
        · rw [hdp1, hi1]
          simp only [List.map_append, List.map_cons, List.map_nil, hpmap, hrow']
          have e : p.2.val + 1 - i.val = (p.2.val - i.val) + 1 := by omega
          rw [e, List.replicate_succ', List.append_assoc]
        · rw [hdp1, hi1]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [hi1]; omega
      · rename_i hlt
        have hle : n.val ≤ p.2.val := by simpa using hlt
        have he : p.2.val = n.val := by omega
        simp only [WP.spec_ok]
        refine ⟨?_, ?_⟩
        · rw [hpmap, he]
        · rw [hplen, he]
    · exact ⟨hi, by simp, hdplen⟩

  /-! #### Invariants of the filling loops -/

  /-- Every row of the table has `n` entries. -/
  def RowsOK (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) : Prop :=
    ∀ i, i < n → ∃ r, dp.val[i]? = some r ∧ rowLen r = n

  /-- Base invariant of the DP loops: the table has `n` rows with `n` entries each, and every
  interval of length `< len` has been filled with the value of the interval DP. -/
  def DpBase (l : List U8) (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (len : Nat) : Prop :=
    dp.val.length = n ∧ RowsOK n dp ∧
      ∀ s' len', 1 ≤ len' → len' < len → s' + len' ≤ n →
        dpCell dp s' (s' + len' - 1) = (dpVal l s' (s' + len' - 1) : Int)

  /-- Invariant of the inner loop over the start index. -/
  def DpInner (l : List U8) (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (len start : Nat) : Prop :=
    DpBase l n dp len ∧
      ∀ s', s' < start → s' + len ≤ n →
        dpCell dp s' (s' + len - 1) = (dpVal l s' (s' + len - 1) : Int)

  theorem RowsOK_set {n : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {a : Usize}
      {r : alloc.vec.Vec I64} (h : RowsOK n dp) (ha : a.val < dp.val.length) (hr : rowLen r = n) :
      RowsOK n (dp.set a r) := by
    intro i hi
    obtain ⟨r0, hr0, hr0len⟩ := h i hi
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases hia : a.val = i
    · rw [if_pos hia, if_pos ha]
      exact ⟨r, rfl, hr⟩
    · rw [if_neg hia]
      exact ⟨r0, hr0, hr0len⟩

  /-- The only cell modified by an update step, and its new value. -/
  theorem dpCell_update (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (a b : Usize)
      (x : I64) (row : alloc.vec.Vec I64) (ha : a.val < dp.val.length)
      (hrow : dp.val[a.val]? = some row) (hb : b.val < rowLen row) (i j : Nat) :
      dpCell (dp.set a (row.set b x)) i j =
        if i = a.val ∧ j = b.val then x.val else dpCell dp i j := by
    rw [dpCell_set dp a _ ha]
    by_cases hia : i = a.val
    · subst hia
      rw [if_pos rfl, dpCell_row hrow, rowCell_set row b x hb]
      by_cases hjb : j = b.val
      · subst hjb; rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hjb, if_neg (by tauto)]
    · rw [if_neg hia, if_neg (by tauto)]

  theorem dpCell_update_len {n : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {a b : Usize}
      {x : I64} {row : alloc.vec.Vec I64} (hrows : RowsOK n dp) (hn : a.val < n)
      (ha : a.val < dp.val.length) (hrow : dp.val[a.val]? = some row)
      (hb : b.val < rowLen row) :
      dp.val.length = ((dp.set a (row.set b x)).val.length) ∧
        RowsOK n (dp.set a (row.set b x)) := by
    have hr : rowLen (row.set b x) = rowLen row := by simp [rowLen]
    obtain ⟨r, hr1, hr2⟩ := hrows a.val hn
    have hrow_eq : r = row := by rw [hr1] at hrow; exact Option.some.inj hrow
    subst hrow_eq
    refine ⟨by simp, RowsOK_set hrows ha (by rw [hr, hr2])⟩

  /-- The recurrence of the DP, in the "equal ends" case. -/
  theorem dpVal_eq_mid {l : List U8} {i j : Nat} (hij : i < j) (_hmid : i + 1 < j)
      (h : l[i]? = l[j]?) : dpVal l i j = dpVal l (i + 1) (j - 1) := by
    rw [dpVal_of_lt hij, if_pos h]

  /-- The recurrence of the DP, in the "different ends" case. -/
  theorem dpVal_ne_mid {l : List U8} {i j : Nat} (hij : i < j) (h : ¬ l[i]? = l[j]?) :
      dpVal l i j = 1 + min (dpVal l (i + 1) j) (dpVal l i (j - 1)) := by
    rw [dpVal_of_lt hij, if_neg h]

  /-- The recurrence of the DP, in the adjacent ("length two") case. -/
  theorem dpVal_adj {l : List U8} {i : Nat} (h : l[i]? = l[i + 1]?) : dpVal l i (i + 1) = 0 := by
    rw [dpVal_of_lt (by omega), if_pos h]
    exact dpVal_of_not_lt (by omega)

  theorem dpVal_le (l : List U8) (i j : Nat) : dpVal l i j ≤ j := by
    suffices h : ∀ k, ∀ i j : Nat, j - i ≤ k → dpVal l i j ≤ j from h _ i j (le_refl _)
    intro k
    induction k with
    | zero =>
      intro i j hk
      rw [dpVal_of_not_lt (by omega)]
      omega
    | succ k ih =>
      intro i j hk
      by_cases hij : i < j
      · rw [dpVal_of_lt hij]
        by_cases heq : l[i]? = l[j]?
        · rw [if_pos heq]
          have := ih (i + 1) (j - 1) (by omega)
          omega
        · rw [if_neg heq]
          have := ih i (j - 1) (by omega)
          omega
      · rw [dpVal_of_not_lt hij]
        omega

  /-- One step of the inner filling loop, at a start index where the interval `[start, start+len)`
  lies inside the table. -/
  theorem rowCell_eq {r : alloc.vec.Vec I64} {j : Nat} {x : I64} (h : r.val[j]? = some x) :
      rowCell r j = x.val := by simp [rowCell, h]

  theorem dpCell_eq {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i j : Nat}
      {r : alloc.vec.Vec I64} {x : I64} (hrow : dp.val[i]? = some r)
      (hx : r.val[j]? = some x) : dpCell dp i j = x.val := by
    rw [dpCell_row hrow, rowCell_eq hx]

  theorem RowsOK_rowLen {n : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : RowsOK n dp)
      {i : Nat} {r : alloc.vec.Vec I64} (hi : i < n) (hr : dp.val[i]? = some r) :
      rowLen r = n := by
    obtain ⟨r0, hr0, hr0len⟩ := h i hi
    rw [hr] at hr0
    rwa [Option.some.inj hr0]

  /-- Convert the `getElem` form of a row read into the `getElem?` form. -/
  theorem vecRow?_eq_some {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i : Usize}
      {v : alloc.vec.Vec I64} (hi : i.val < dp.val.length) (h : v = dp[i]) :
      dp.val[i.val]? = some v := by
    subst h
    rw [alloc.vec.Vec.getElem_Usize_eq dp i hi]
    exact List.getElem?_eq_getElem hi

  theorem DpInner_step {l : List U8} {n : Nat} {dp dp' : alloc.vec.Vec (alloc.vec.Vec I64)}
      {len start : Nat} {row : alloc.vec.Vec I64} {a b : Usize} {x : I64}
      (hlen : 2 ≤ len) (hstartn : start + len ≤ n)
      (hinv : DpInner l n dp len start)
      (ha : a.val = start) (hb : b.val = start + len - 1)
      (hdplen : a.val < dp.val.length) (hrow : dp.val[a.val]? = some row)
      (hrowb : b.val < rowLen row) (hnewval : x.val = (dpVal l start (start + len - 1) : Int))
      (hdp' : dp' = dp.set a (row.set b x)) :
      DpInner l n dp' len (start + 1) := by
    obtain ⟨⟨hdplen', hrows', hcells'⟩, hnew'⟩ := hinv
    have hcell := dpCell_update dp a b x row hdplen hrow hrowb
    obtain ⟨hL1, hL2⟩ :=
      dpCell_update_len (dp := dp) (x := x) (row := row) (a := a) (b := b)
        hrows' (by omega) hdplen hrow hrowb
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hdp', ← hL1]; exact hdplen'
    · rw [hdp']; exact hL2
    · intro s' len' h1 h2 h3
      rw [hdp', hcell, if_neg (by omega)]
      exact hcells' s' len' h1 h2 h3
    · intro s' hlt hle
      rw [hdp', hcell]
      by_cases hs : s' = a.val
      · have hs' : s' = start := by omega
        rw [if_pos ⟨hs, by omega⟩, hs']
        exact hnewval
      · rw [if_neg (by tauto)]
        exact hnew' s' (by omega) hle

  theorem loop1_loop0_body_spec (s : Slice U8) (n len start : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hnn : n.val = s.val.length) (hn500 : n.val ≤ 500)
      (hlen2 : 2 ≤ len.val) (hstart : start.val + len.val ≤ n.val)
      (hinv : DpInner s.val n.val dp len.val start.val) :
      Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len dp start ⦃ r =>
        match r with
        | .cont (dp', st') => st'.val = start.val + 1 ∧ DpInner s.val n.val dp' len.val st'.val
        | .done _ => False ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
    obtain ⟨⟨hdplen, hrows, hcells⟩, hnew⟩ := hinv
    have hn_lt : start.val < n.val := by omega
    have hslen : start.val < s.val.length := by omega
    step as ⟨i, hi⟩
    split
    · rename_i hle
      have hiend : 1 ≤ i.val := by omega
      step as ⟨e, he1, he2⟩
      have hes : e.val = i.val - 1 := he1
      have hes2 : e.val = start.val + len.val - 1 := by omega
      step as ⟨i1, hi1⟩
      have heslen : e.val < s.val.length := by omega
      step as ⟨i2, hi2⟩
      have hi1s : s.val[start.val]? = some i1 := by
        rw [hi1, List.getElem?_eq_getElem (by omega)]
      have hi2s : s.val[e.val]? = some i2 := by
        rw [hi2, List.getElem?_eq_getElem (by omega)]
      split
      · rename_i heq
        have heqS : s.val[start.val]? = s.val[start.val + len.val - 1]? := by
          have h1 : start.val + len.val - 1 = e.val := by omega
          rw [h1, hi1s, hi2s, heq]
        split
        · rename_i hlen2eq
          have hl2v : len.val = 2 := by
            have := congrArg (fun (x : Usize) => x.val) hlen2eq
            simpa using this
          step as ⟨pru, hpu1, hpu2⟩
          obtain ⟨v, back⟩ := pru
          try dsimp only
          have hrowv : dp.val[start.val]? = some v := vecRow?_eq_some (by omega) hpu1
          have hlenv : v.val.length = n.val := by
            have h := RowsOK_rowLen hrows hn_lt hrowv
            simpa [rowLen] using h
          have hbk : back = dp.set start := hpu2
          have helenv : e.val < v.val.length := by omega
          step as ⟨pr2, hpr3, hpr4⟩
          obtain ⟨ul, back1⟩ := pr2
          try dsimp only
          have hbk1 : back1 = v.set e := hpr4
          step as ⟨start1, hstart1⟩
          have heqS1 : s.val[start.val]? = s.val[start.val + 1]? := by
            have h2 : start.val + 1 = e.val := by omega
            rw [h2, hi1s, hi2s, heq]
          have hst : start1.val = start.val + 1 := by rw [hstart1]
          refine ⟨by rw [hst], ?_⟩
          have hdp' : back (back1 0#i64) = dp.set start (v.set e 0#i64) := by
            rw [hbk, hbk1]
          rw [hdp', hst]
          refine DpInner_step (l := s.val) (n := n.val) (len := len.val) (start := start.val)
            (dp := dp) (row := v) (a := start) (b := e) (x := 0#i64)
            (dp' := dp.set start (v.set e 0#i64))
            hlen2 hstart ⟨⟨hdplen, hrows, hcells⟩, hnew⟩ rfl (by omega) (by omega) hrowv ?_ ?_ rfl
          · show e.val < v.val.length
            omega
          · have hz : dpVal s.val start.val (start.val + len.val - 1) = 0 := by
              have h2 : start.val + len.val - 1 = start.val + 1 := by omega
              rw [h2]
              exact dpVal_adj heqS1
            rw [hz]
            simp
        · rename_i hlen2ne
          have hl2v : len.val ≠ 2 := by
            intro hc
            exact hlen2ne (UScalar.eq_imp len 2#usize (by simpa using hc))
          have hlen3 : 3 ≤ len.val := by omega
          have hb1 : start.val + 1 < dp.val.length := by omega
          step as ⟨i3, hi3⟩
          step as ⟨v, hv⟩
          have hi3v : i3.val = start.val + 1 := hi3
          have hv_row : dp.val[i3.val]? = some v := vecRow?_eq_some (by omega) hv
          have hlenv : rowLen v = n.val := RowsOK_rowLen hrows (by omega) hv_row
          have hes1 : e.val < v.val.length := by
            have h2 : rowLen v = v.val.length := rfl
            omega
          step as ⟨i4, hi4a, hi4b⟩
          have hi4v : i4.val = (start.val + len.val - 1) - 1 := by omega
          step as ⟨i5, hi5⟩
          have hi5x : v.val[i4.val]? = some i5 := by
            rw [hi5, List.getElem?_eq_getElem (by omega)]
          have hnewval : i5.val = (dpVal s.val start.val (start.val + len.val - 1) : Int) := by
            have hcell1 : dpCell dp i3.val i4.val = i5.val := dpCell_eq hv_row hi5x
            have hcell2 : dpCell dp i3.val i4.val = (dpVal s.val i3.val i4.val : Int) := by
              have h := hcells i3.val (len.val - 2) (by omega) (by omega) (by omega)
              rwa [show i3.val + (len.val - 2) - 1 = i4.val by omega] at h
            have hmid : dpVal s.val start.val (start.val + len.val - 1)
                = dpVal s.val i3.val i4.val := by
              have h := dpVal_eq_mid (l := s.val) (i := start.val) (j := start.val + len.val - 1)
                (by omega) (by omega) heqS
              rwa [show start.val + 1 = i3.val by omega,
                show start.val + len.val - 1 - 1 = i4.val by omega] at h
            rw [hmid, ← hcell2, hcell1]
          have hbb : start.val < dp.val.length := by omega
          step as ⟨pru, hpu1, hpu2⟩
          obtain ⟨v1, back⟩ := pru
          try dsimp only
          have hrowv1 : dp.val[start.val]? = some v1 := vecRow?_eq_some (by omega) hpu1
          have hlenv1 : v1.val.length = n.val := by
            have h := RowsOK_rowLen hrows hn_lt hrowv1
            simpa [rowLen] using h
          have hbk : back = dp.set start := hpu2
          have helenv1 : e.val < v1.val.length := by omega
          step as ⟨pr2, hpr3, hpr4⟩
          obtain ⟨ul, back1⟩ := pr2
          try dsimp only
          have hbk1 : back1 = v1.set e := hpr4
          step as ⟨start1, hstart1⟩
          have hst : start1.val = start.val + 1 := by rw [hstart1]
          refine ⟨by rw [hst], ?_⟩
          have hdp' : back (back1 i5) = dp.set start (v1.set e i5) := by rw [hbk, hbk1]
          rw [hdp', hst]
          refine DpInner_step (l := s.val) (n := n.val) (len := len.val) (start := start.val)
            (dp := dp) (row := v1) (a := start) (b := e) (x := i5)
            (dp' := dp.set start (v1.set e i5))
            hlen2 hstart ⟨⟨hdplen, hrows, hcells⟩, hnew⟩ rfl (by omega) (by omega) hrowv1 ?_ hnewval rfl
          · show e.val < v1.val.length
            omega
      · rename_i hne
        have hneS : ¬ s.val[start.val]? = s.val[start.val + len.val - 1]? := by
          have h1 : start.val + len.val - 1 = e.val := by omega
          rw [h1, hi1s, hi2s]
          simpa using hne
        have hb1 : start.val + 1 < dp.val.length := by omega
        step as ⟨i3, hi3⟩
        step as ⟨v, hv⟩
        have hi3v : i3.val = start.val + 1 := hi3
        have hv_row : dp.val[i3.val]? = some v := vecRow?_eq_some (by omega) hv
        have hlenv : rowLen v = n.val := RowsOK_rowLen hrows (by omega) hv_row
        have hes1 : e.val < v.val.length := by
          have h2 : rowLen v = v.val.length := rfl
          omega
        step as ⟨left, hleft⟩
        have hleftx : v.val[e.val]? = some left := by
          rw [hleft, List.getElem?_eq_getElem (by omega)]
        have hb2 : start.val < dp.val.length := by omega
        step as ⟨v1, hv1⟩
        have hv1_row : dp.val[start.val]? = some v1 := vecRow?_eq_some (by omega) hv1
        have hlenv1 : v1.val.length = n.val := by
          have h := RowsOK_rowLen hrows hn_lt hv1_row
          simpa [rowLen] using h
        step as ⟨i4, hi4a, hi4b⟩
        have hi4v : i4.val = (start.val + len.val - 1) - 1 := by omega
        have hive : i4.val < v1.val.length := by omega
        step as ⟨right, hright⟩
        have hrightx : v1.val[i4.val]? = some right := by
          rw [hright, List.getElem?_eq_getElem (by omega)]
        have hA : left.val = (dpVal s.val (start.val + 1) (start.val + len.val - 1) : Int) := by
          have h1 : dpCell dp i3.val e.val = left.val := dpCell_eq hv_row hleftx
          have h2 : dpCell dp i3.val e.val = (dpVal s.val i3.val e.val : Int) := by
            have h := hcells i3.val (len.val - 1) (by omega) (by omega) (by omega)
            rwa [show i3.val + (len.val - 1) - 1 = e.val by omega] at h
          rw [← h1, h2, hi3v, hes2]
        have hB : right.val
            = (dpVal s.val start.val (start.val + len.val - 1 - 1) : Int) := by
          have h1 : dpCell dp start.val i4.val = right.val := dpCell_eq hv1_row hrightx
          have h2 : dpCell dp start.val i4.val = (dpVal s.val start.val i4.val : Int) := by
            have h := hcells start.val (len.val - 1) (by omega) (by omega) (by omega)
            rwa [show start.val + (len.val - 1) - 1 = i4.val by omega] at h
          rw [← h1, h2, hi4v]
        have hbb : start.val < dp.val.length := by omega
        split
        · rename_i hlt
          have hnat : dpVal s.val (start.val + 1) (start.val + len.val - 1)
              < dpVal s.val start.val (start.val + len.val - 1 - 1) := by
            have h2 : left.val < right.val := by simpa using hlt
            rw [hA] at h2; rw [hB] at h2
            omega
          have hi5b : left.val + 1 ≤ I64.max := by
            have h3 := dpVal_le s.val (start.val + 1) (start.val + len.val - 1)
            rw [hA]
            scalar_tac
          step as ⟨i5, hi5⟩
          have hi5' : i5.val = (dpVal s.val (start.val + 1) (start.val + len.val - 1) : Int) + 1 := by
            rw [hi5, hA]
          have hnewval : i5.val = (dpVal s.val start.val (start.val + len.val - 1) : Int) := by
            have hmin : min (dpVal s.val (start.val + 1) (start.val + len.val - 1))
                (dpVal s.val start.val (start.val + len.val - 1 - 1))
                = dpVal s.val (start.val + 1) (start.val + len.val - 1) :=
              Nat.min_eq_left (le_of_lt hnat)
            rw [dpVal_ne_mid (l := s.val) (i := start.val) (j := start.val + len.val - 1)
              (by omega) hneS, hmin]
            omega
          have helenv1' : e.val < v1.val.length := by omega
          step as ⟨pru, hpu1, hpu2⟩
          obtain ⟨v2, back⟩ := pru
          try dsimp only
          have hrowv2 : dp.val[start.val]? = some v2 := vecRow?_eq_some (by omega) hpu1
          have hlenv2 : v2.val.length = n.val := by
            have h := RowsOK_rowLen hrows hn_lt hrowv2
            simpa [rowLen] using h
          have hbk : back = dp.set start := hpu2
          have helenv2 : e.val < v2.val.length := by omega
          step as ⟨pr2, hpr3, hpr4⟩
          obtain ⟨ul, back1⟩ := pr2
          try dsimp only
          have hbk1 : back1 = v2.set e := hpr4
          step as ⟨start1, hstart1⟩
          have hst : start1.val = start.val + 1 := by rw [hstart1]
          refine ⟨by rw [hst], ?_⟩
          have hdp' : back (back1 i5) = dp.set start (v2.set e i5) := by rw [hbk, hbk1]
          rw [hdp', hst]
          refine DpInner_step (l := s.val) (n := n.val) (len := len.val) (start := start.val)
            (dp := dp) (row := v2) (a := start) (b := e) (x := i5)
            (dp' := dp.set start (v2.set e i5))
            hlen2 hstart ⟨⟨hdplen, hrows, hcells⟩, hnew⟩ rfl (by omega) (by omega) hrowv2 ?_ hnewval rfl
          · show e.val < v2.val.length
            omega
        · rename_i hge
          have hBA : dpVal s.val start.val (start.val + len.val - 1 - 1)
              ≤ dpVal s.val (start.val + 1) (start.val + len.val - 1) := by
            have h2 : ¬ (left.val < right.val) := by simpa using hge
            have h3 : right.val ≤ left.val := by omega
            rw [hA] at h3; rw [hB] at h3
            omega
          have hi5b : right.val + 1 ≤ I64.max := by
            have h3 := dpVal_le s.val start.val (start.val + len.val - 1 - 1)
            rw [hB]
            scalar_tac
          step as ⟨i5, hi5⟩
          have hi5' : i5.val = (dpVal s.val start.val (start.val + len.val - 1 - 1) : Int) + 1 := by
            rw [hi5, hB]
          have hnewval : i5.val = (dpVal s.val start.val (start.val + len.val - 1) : Int) := by
            have hmin : min (dpVal s.val (start.val + 1) (start.val + len.val - 1))
                (dpVal s.val start.val (start.val + len.val - 1 - 1))
                = dpVal s.val start.val (start.val + len.val - 1 - 1) :=
              Nat.min_eq_right hBA
            rw [dpVal_ne_mid (l := s.val) (i := start.val) (j := start.val + len.val - 1)
              (by omega) hneS, hmin]
            omega
          have helenv1' : e.val < v1.val.length := by omega
          step as ⟨pru, hpu1, hpu2⟩
          obtain ⟨v2, back⟩ := pru
          try dsimp only
          have hrowv2 : dp.val[start.val]? = some v2 := vecRow?_eq_some (by omega) hpu1
          have hlenv2 : v2.val.length = n.val := by
            have h := RowsOK_rowLen hrows hn_lt hrowv2
            simpa [rowLen] using h
          have hbk : back = dp.set start := hpu2
          have helenv2 : e.val < v2.val.length := by omega
          step as ⟨pr2, hpr3, hpr4⟩
          obtain ⟨ul, back1⟩ := pr2
          try dsimp only
          have hbk1 : back1 = v2.set e := hpr4
          step as ⟨start1, hstart1⟩
          have hst : start1.val = start.val + 1 := by rw [hstart1]
          refine ⟨by rw [hst], ?_⟩
          have hdp' : back (back1 i5) = dp.set start (v2.set e i5) := by rw [hbk, hbk1]
          rw [hdp', hst]
          refine DpInner_step (l := s.val) (n := n.val) (len := len.val) (start := start.val)
            (dp := dp) (row := v2) (a := start) (b := e) (x := i5)
            (dp' := dp.set start (v2.set e i5))
            hlen2 hstart ⟨⟨hdplen, hrows, hcells⟩, hnew⟩ rfl (by omega) (by omega) hrowv2 ?_ hnewval rfl
          · show e.val < v2.val.length
            omega
    · rename_i hnle
      have h1 : i.val ≤ n.val := by omega
      exact absurd h1 (by simpa using hnle)

  /-- The inner filling loop: for a fixed interval length `len`, fill the cells of all intervals
  of that length. -/
  theorem loop1_loop0_spec (s : Slice U8) (n len start : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hnn : n.val = s.val.length) (hn500 : n.val ≤ 500)
      (hlen2 : 2 ≤ len.val) (hlen : len.val ≤ n.val) (hstart : start.val ≤ n.val)
      (hinv : DpInner s.val n.val dp len.val start.val) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start ⦃ dp' =>
        DpBase s.val n.val dp' (len.val + 1) ⦄ := by
    classical
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val - p.2.val)
      (inv := fun p => p.2.val ≤ n.val ∧ DpInner s.val n.val p.1 len.val p.2.val)
      (post := fun dp' => DpBase s.val n.val dp' (len.val + 1))
    · intro p hp
      obtain ⟨hpn, hinv'⟩ := hp
      obtain ⟨dp, st⟩ := p
      dsimp only at hpn hinv' ⊢
      have hcase : (st.val + len.val ≤ n.val) ∨ ¬ (st.val + len.val ≤ n.val) := em _
      rcases hcase with hcase | hcase
      · refine WP.spec_mono (loop1_loop0_body_spec s n len st dp hnn hn500 hlen2 hcase hinv') ?_
        intro r hr
        match r with
        | .done y => simp only [] at hr
        | .cont p' =>
          simp only [] at hr
          obtain ⟨h1, h2⟩ := hr
          exact ⟨⟨by omega, h2⟩, by omega⟩
      · obtain ⟨hdplen, hrows, hcells⟩ := hinv'.1
        obtain ⟨_, hnew⟩ := hinv'
        simp only [Aegis.MinInsertions.min_insertions_loop1_loop0.body]
        step as ⟨i, hi⟩
        rw [if_neg (by
          intro hc
          have h1 : i.val ≤ n.val := by simpa using hc
          omega)]
        simp only [WP.spec_ok]
        refine ⟨hdplen, hrows, ?_⟩
        intro s' len' h1 h2 h3
        rcases Nat.lt_or_ge len' len.val with hlt | hge
        · exact hcells s' len' h1 hlt h3
        · have hle : len' = len.val := by omega
          subst hle
          exact hnew s' (by omega) h3
    · exact ⟨hstart, hinv⟩

  /-- The outer filling loop. -/
  theorem loop1_spec (s : Slice U8) (n len : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hnn : n.val = s.val.length) (hn500 : n.val ≤ 500)
      (hlen2 : 2 ≤ len.val) (hlen : len.val ≤ n.val + 1)
      (hinv : DpBase s.val n.val dp len.val) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp len ⦃ dp' =>
        DpBase s.val n.val dp' (n.val + 1) ⦄ := by
    classical
    unfold Aegis.MinInsertions.min_insertions_loop1
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize => n.val + 1 - p.2.val)
      (inv := fun p => 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1 ∧ DpBase s.val n.val p.1 p.2.val)
      (post := fun dp' => DpBase s.val n.val dp' (n.val + 1))
    · intro p hp
      obtain ⟨hlen2', hpn, hbase⟩ := hp
      obtain ⟨dp, ln⟩ := p
      dsimp only at hlen2' hpn hbase ⊢
      simp only [Aegis.MinInsertions.min_insertions_loop1.body]
      split
      · rename_i hle
        have hle' : ln.val ≤ n.val := by simpa using hle
        have hinner : DpInner s.val n.val dp ln.val 0 :=
          ⟨hbase, by intro s' hs; omega⟩
        step with loop1_loop0_spec as ⟨dp1, hdp1⟩
        step as ⟨len1, hlen1⟩
        · rw [hlen1]
          exact ⟨by omega, by omega, hdp1, by omega⟩
      · rename_i hle
        have hle' : ¬ (ln.val ≤ n.val) := by simpa using hle
        simp only [WP.spec_ok]
        have : ln.val = n.val + 1 := by omega
        rw [← this]
        exact hbase
    · exact ⟨hlen2, hlen, hinv⟩

  /-- The matrix-initialising loops produce a table in which every interval of length `1` is
  already filled in (all cells are `0`). -/
  theorem init_spec (s : Slice U8) (n : Usize) (hnn : n.val = s.val.length) (hn500 : n.val ≤ 500)
      (hn2 : 2 ≤ n.val) :
      Aegis.MinInsertions.min_insertions_loop0 n
          (alloc.vec.Vec.new (alloc.vec.Vec I64)) 0#usize ⦃ dp =>
        DpBase s.val n.val dp 2 ⦄ := by
    refine WP.spec_mono (loop0_spec n (alloc.vec.Vec.new (alloc.vec.Vec I64)) 0#usize
      hn500 (by simp) (by simp)) ?_
    intro dp hdp
    obtain ⟨hdp1, hdp2⟩ := hdp
    have hnil : List.map (fun r : alloc.vec.Vec I64 => (↑r : List I64))
        (↑(alloc.vec.Vec.new (alloc.vec.Vec I64)) : List (alloc.vec.Vec I64)) = [] := by
      simp
    have hnf : n.val - (0#usize).val = n.val := by simp
    have hrow : ∀ (i : Nat), i < n.val → ∀ r : alloc.vec.Vec I64,
        dp.val[i]? = some r → r.val = List.replicate n.val 0#i64 := by
      intro i hi r hr
      have h := congrArg (fun l => l[i]?) hdp1
      rw [List.getElem?_map, hr] at h
      simp only [Option.map_some] at h
      rw [hnil, List.nil_append, hnf, List.getElem?_replicate_of_lt hi] at h
      simpa using Option.some.inj h
    refine ⟨hdp2, ?_, ?_⟩
    · intro i hi
      obtain ⟨r, hr⟩ : ∃ r, dp.val[i]? = some r := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact ⟨r, hr, by rw [rowLen, hrow i hi r hr, List.length_replicate]⟩
    · intro s' len' h1 h2 h3
      have h2' : len' = 1 := by omega
      subst h2'
      obtain ⟨r, hr⟩ : ∃ r, dp.val[s']? = some r := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hrval : r.val = List.replicate n.val 0#i64 := hrow s' (by omega) r hr
      have hx : r.val[s']? = some (0#i64) := by
        rw [hrval, List.getElem?_replicate_of_lt (by omega)]
      have hz : dpCell dp s' s' = 0 := by
        rw [dpCell_row hr, rowCell_eq hx]
        simp
      have hsub : s' + 1 - 1 = s' := by omega
      rw [hsub, hz, dpVal_of_not_lt (by omega)]
      simp

  /-- The extracted program computes the interval DP value of the whole string. -/
  theorem min_insertions_spec (s : Slice U8) (h2 : 2 ≤ s.val.length)
      (h500 : s.val.length ≤ 500) :
      Aegis.MinInsertions.min_insertions s ⦃ r =>
        r.val = (dpVal s.val 0 (s.val.length - 1) : Int) ⦄ := by
    have hn : (Slice.len s).val = s.val.length := by simp [Slice.len]
    unfold Aegis.MinInsertions.min_insertions
    dsimp only
    split
    · rename_i hle
      simp only [WP.spec_ok]
      have h1 : (Slice.len s).val ≤ 1 := by simpa using hle
      have h0 : (0#i64).val = 0 := by simp
      rw [h0]
      omega
    · rename_i hgt
      have hn2 : 2 ≤ (Slice.len s).val := by
        have : ¬ ((Slice.len s).val ≤ 1) := by simpa using hgt
        omega
      have hn500 : (Slice.len s).val ≤ 500 := by omega
      step with init_spec as ⟨dp, hdp⟩
      step with loop1_spec as ⟨dp1, hdp1⟩
      have hb1 : 0 < dp1.val.length := by
        have := hdp1.1
        omega
      have hb2 : (Slice.len s).val - 1 < (dp1.val[0]).val.length := by
        obtain ⟨r, hr, hrlen⟩ := hdp1.2.1 0 (by omega)
        have h0 : dp1.val[0]? = some (dp1.val[0]) := List.getElem?_eq_getElem (by omega)
        rw [h0] at hr
        have hrr : dp1.val[0] = r := Option.some.inj hr
        have hrlen' : r.val.length = (Slice.len s).val := hrlen
        rw [hrr]
        omega
      step as ⟨v, hv⟩
      step as ⟨i, hi⟩
      step as ⟨res, hres⟩
      have hbnd : i.val < v.val.length := by
        rw [hi, hv]
        exact hb2
      have hvrow : dp1.val[0]? = some v := by
        have h0 : dp1.val[0]? = some (dp1.val[0]) := List.getElem?_eq_getElem (by omega)
        rw [h0, hv]
      have hresval : v.val[i.val]? = some res := by
        have h0 : v.val[i.val]? = some (v.val[i.val]) := List.getElem?_eq_getElem hbnd
        rw [h0, hres]
      have hcell : dpCell dp1 0 i.val = res.val := by
        rw [dpCell_row hvrow, rowCell_eq hresval]
      have hstep1 : (res : Int) = dpCell dp1 0 ((Slice.len s).val - 1) := by
        rw [← hi, hcell]
      have hstep2 : dpCell dp1 0 ((Slice.len s).val - 1)
          = (dpVal s.val 0 ((Slice.len s).val - 1) : Int) := by
        have h := hdp1.2.2 0 (Slice.len s).val (by omega) (by omega) (by omega)
        simpa using h
      rw [hstep1, hstep2, hn]

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
  theorem spec_6 (s t : Slice U8)
      (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 500)
      (ht_lower : 1 ≤ t.val.length) (ht_upper : t.val.length ≤ 500)
      (hlen : t.val.length = s.val.length)
      (hlower_s : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlower_t : ∀ (i : Nat), (hi : i < t.val.length) → isLowerAscii (t.val[i]))
      (hrev : ∀ (i : Nat), (hi : i < s.val.length) →
        t.val[i] = s.val[s.val.length - 1 - i]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions t = ok q → r = q := by
    have hzero : ∀ (u : Slice U8), u.val.length = 1 →
        Aegis.MinInsertions.min_insertions u = ok 0#i64 := by
      intro u hu
      unfold Aegis.MinInsertions.min_insertions
      dsimp only
      rw [if_pos (by
        have h1 : (Slice.len u).val ≤ 1 := by simp [hu]
        simpa using h1)]
    intro r q hr hq
    rcases Nat.lt_or_ge s.val.length 2 with h2 | h2
    · have hs1 : s.val.length = 1 := by omega
      have ht1 : t.val.length = 1 := by omega
      rw [hzero s hs1] at hr
      rw [hzero t ht1] at hq
      rw [hr] at hq
      simpa [Result.ok.injEq] using hq
    · have hrv : r.val = (dpVal s.val 0 (s.val.length - 1) : Int) := by
        have h := min_insertions_spec s h2 hs_upper
        rw [hr] at h
        simpa using h
      have hqv : q.val = (dpVal t.val 0 (t.val.length - 1) : Int) := by
        have h := min_insertions_spec t (by omega) ht_upper
        rw [hq] at h
        simpa using h
      have hmir : ∀ a, a < t.val.length → t.val[a]? = s.val[s.val.length - 1 - a]? := by
        intro a ha
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
        exact congrArg some (hrev a (by omega))
      have hsymm := dpVal_rev s.val t.val hlen hmir 0 (t.val.length - 1) (by omega)
      rw [show s.val.length - 1 - (t.val.length - 1) = 0 from by omega,
        show s.val.length - 1 - 0 = s.val.length - 1 from by omega] at hsymm
      have hval : r.val = q.val := by rw [hrv, hqv, hsymm]
      exact IScalar.eq_imp r q hval

  /-- **S10 (relational, trimming equal ends).** If the first and last bytes of `s` agree, then
  the answer for `s` equals the answer for the inner slice `u` of length `len(s) - 2` with
  `u[i] = s[i+1]`. -/
  theorem spec_S10 (s u : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen3 : 3 ≤ s.val.length)
      (hends : s.val[0] = s.val[s.val.length - 1])
      (hu_len : u.val.length = s.val.length - 2)
      (hu_val : ∀ (i : Nat), (hi : i < u.val.length) → u.val[i] = s.val[i + 1]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions u = ok q → r = q := by
    sorry

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
