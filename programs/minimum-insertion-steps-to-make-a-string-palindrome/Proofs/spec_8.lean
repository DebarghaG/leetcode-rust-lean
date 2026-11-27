import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_8` (minimum-insertion-steps-to-make-a-string-palindrome).
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

  /-! ### Experiments -/

  /-- Minimum number of insertions needed to turn the sub-string `l[i..j]`
  (the bytes `l[i], …, l[j]`) into a palindrome.  Value `0` when `i ≥ j`. -/
  def MI (l : List U8) (i j : Nat) : Nat :=
    if i < j then
      if l[i]? = l[j]? then MI l (i + 1) (j - 1) else 1 + min (MI l (i + 1) j) (MI l i (j - 1))
    else 0
  termination_by j - i
  decreasing_by all_goals (simp_wf; omega)

  theorem MI_def_lt (l : List U8) (i j : Nat) (h : i < j) :
      MI l i j =
        (if l[i]? = l[j]? then MI l (i + 1) (j - 1)
          else 1 + min (MI l (i + 1) j) (MI l i (j - 1))) := by
    rw [MI]
    simp only [h, if_true]

  theorem MI_def_le (l : List U8) (i j : Nat) (h : ¬ i < j) : MI l i j = 0 := by
    rw [MI]
    simp only [h, if_false]

  theorem MI_self (l : List U8) (i j : Nat) (h : j ≤ i) : MI l i j = 0 :=
    MI_def_le l i j (by omega)

  theorem MI_le (l : List U8) : ∀ (i j : Nat), MI l i j ≤ j - i + 1 := by
    intro i j
    induction i, j using MI.induct l with
    | case1 i j hij heq _ =>
      rw [MI_def_lt l i j hij, if_pos heq]
      omega
    | case2 i j hij hne _ _ =>
      rw [MI_def_lt l i j hij, if_neg hne]
      omega
    | case3 i j h => rw [MI_def_le l i j h]; omega

  theorem MI_shift_aux (s t : List U8) (h : ∀ (k : Nat), t[k]? = s[k + 1]?) :
      ∀ d i j, j - i = d → MI t i j = MI s (i + 1) (j + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hd
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [MI_def_lt t i j hij, MI_def_lt s (i + 1) (j + 1) (by omega)]
        have hti : t[i]? = s[i + 1]? := h i
        have htj : t[j]? = s[j + 1]? := h j
        by_cases hc : t[i]? = t[j]?
        · rw [if_pos hc, if_pos (by rw [← hti, ← htj]; exact hc)]
          have key := ih (j - 1 - (i + 1)) (by omega) (i + 1) (j - 1) (by omega)
          have e1 : j - 1 + 1 = j := by omega
          have e2 : j + 1 - 1 = j := by omega
          rw [key, e1, e2]
        · rw [if_neg hc, if_neg (by rw [← hti, ← htj]; exact hc)]
          have k1 := ih (j - (i + 1)) (by omega) (i + 1) j (by omega)
          have k2 := ih (j - 1 - i) (by omega) i (j - 1) (by omega)
          have e1 : j - 1 + 1 = j := by omega
          have e2 : j + 1 - 1 = j := by omega
          rw [k1, k2, e1, e2]
      · rw [MI_def_le t i j (by omega), MI_def_le s (i + 1) (j + 1) (by omega)]

  theorem MI_shift (s t : List U8) (h : ∀ (k : Nat), t[k]? = s[k + 1]?) (i j : Nat) :
      MI t i j = MI s (i + 1) (j + 1) :=
    MI_shift_aux s t h (j - i) i j rfl

  theorem MI_same_aux (s t : List U8) (h : ∀ (k : Nat), t[k]? = s[k]?) :
      ∀ d i j, j - i = d → MI t i j = MI s i j := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hd
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [MI_def_lt t i j hij, MI_def_lt s i j hij]
        have hti : t[i]? = s[i]? := h i
        have htj : t[j]? = s[j]? := h j
        by_cases hc : t[i]? = t[j]?
        · rw [if_pos hc, if_pos (by rw [← hti, ← htj]; exact hc)]
          exact ih (j - 1 - (i + 1)) (by omega) (i + 1) (j - 1) (by omega)
        · rw [if_neg hc, if_neg (by rw [← hti, ← htj]; exact hc)]
          rw [ih (j - (i + 1)) (by omega) (i + 1) j (by omega),
            ih (j - 1 - i) (by omega) i (j - 1) (by omega)]
      · rw [MI_def_le t i j (by omega), MI_def_le s i j (by omega)]

  theorem MI_same (s t : List U8) (h : ∀ (k : Nat), t[k]? = s[k]?) (i j : Nat) :
      MI t i j = MI s i j :=
    MI_same_aux s t h (j - i) i j rfl

  /-- `MI` only depends on the entries of the string up to the right endpoint. -/
  theorem MI_same_le_aux (s t : List U8) (N : Nat)
      (h : ∀ (k : Nat), k < N → t[k]? = s[k]?) :
      ∀ d i j, j - i = d → j < N → MI t i j = MI s i j := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hd hjN
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [MI_def_lt t i j hij, MI_def_lt s i j hij]
        have hti : t[i]? = s[i]? := h i (by omega)
        have htj : t[j]? = s[j]? := h j (by omega)
        by_cases hc : t[i]? = t[j]?
        · rw [if_pos hc, if_pos (by rw [← hti, ← htj]; exact hc)]
          exact ih (j - 1 - (i + 1)) (by omega) (i + 1) (j - 1) (by omega) (by omega)
        · rw [if_neg hc, if_neg (by rw [← hti, ← htj]; exact hc)]
          rw [ih (j - (i + 1)) (by omega) (i + 1) j (by omega) (by omega),
            ih (j - 1 - i) (by omega) i (j - 1) (by omega) (by omega)]
      · rw [MI_def_le t i j (by omega), MI_def_le s i j (by omega)]

  theorem MI_same_le (s t : List U8) (N : Nat) (h : ∀ (k : Nat), k < N → t[k]? = s[k]?)
      (i j : Nat) (hjN : j < N) : MI t i j = MI s i j :=
    MI_same_le_aux s t N h (j - i) i j rfl hjN

  /-! ### The DP matrix -/

  /-- The `j`-th entry of a row, as an integer (`0` when out of bounds). -/
  def rcell (l : List I64) (j : Nat) : Int :=
    match l[j]? with
    | none => 0
    | some x => x.val

  /-- The `(i,j)` entry of a matrix `dp`, as an integer (`0` when out of bounds). -/
  def cell (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    match dp.val[i]? with
    | none => 0
    | some r => rcell r.val j

  theorem rcell_eq (l : List I64) (j : Nat) (x : I64) (h : l[j]? = some x) :
      rcell l j = x.val := by
    simp only [rcell, h]

  theorem rcell_set (l : List I64) (a j : Nat) (y : I64) (ha : a < l.length) :
      rcell (l.set a y) j = if a = j then y.val else rcell l j := by
    have hset : (l.set a y)[j]? = if a = j then (if a < l.length then some y else none) else l[j]? :=
      List.getElem?_set
    simp only [rcell, hset]
    by_cases h : a = j
    · subst h; simp [ha]
    · simp [h]

  theorem rcell_replicate (n j : Nat) : rcell (List.replicate n 0#i64) j = 0 := by
    by_cases h : j < n
    · simp only [rcell]
      rw [List.getElem?_eq_getElem (List.length_replicate ▸ h)]
      simp
    · have : (List.replicate n 0#i64)[j]? = none := by
        rw [List.getElem?_eq_none]
        simpa using Nat.le_of_not_lt h
      rw [rcell, this]

  theorem cell_eq_val {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i j : Nat} {r : alloc.vec.Vec I64}
      {x : I64} (hr : dp.val[i]? = some r) (hx : r.val[j]? = some x) : cell dp i j = x.val := by
    simp only [cell, hr]
    exact rcell_eq _ _ _ hx

  theorem cell_set (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (a : Usize)
      (w : alloc.vec.Vec I64) (ha : a.val < dp.val.length) (i j : Nat) :
      cell (dp.set a w) i j = if a.val = i then rcell w.val j else cell dp i j := by
    have hv : (dp.set a w).val = dp.val.set a.val w := by simp [alloc.vec.Vec.set]
    have hset : (dp.val.set a.val w)[i]? = if a.val = i then some w else dp.val[i]? := by
      rw [List.getElem?_set]
      simp [ha]
    simp only [cell, hv, hset]
    by_cases h : a.val = i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]

  theorem cell_set_row (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (a : Usize)
      (w : alloc.vec.Vec I64) (ha : a.val < dp.val.length) (b : Usize) (y : I64)
      (hb : b.val < w.val.length) (i j : Nat) :
      cell (dp.set a (w.set b y)) i j =
        if a.val = i then (if b.val = j then y.val else rcell w.val j) else cell dp i j := by
    have hrow : (w.set b y).val = w.val.set b.val y := by simp [alloc.vec.Vec.set]
    rw [cell_set dp a (w.set b y) ha i j, hrow, rcell_set w.val b.val j y hb]

  /-- `dp` has at least `n` rows, all of length `n`. -/
  def TableOk (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    ∀ (i : Nat), i < n → ∃ r : alloc.vec.Vec I64, dp.val[i]? = some r ∧ r.val.length = n

  /-! ### Filling the matrix with zeros -/

  theorem loop0_loop0_body_spec (n : Usize) (row : alloc.vec.Vec I64) (j : Usize)
      (hn : n.val ≤ 500) (hj : j.val ≤ n.val) (hrow : row.val.length = j.val) :
      Aegis.MinInsertions.min_insertions_loop0_loop0.body n row j ⦃ r =>
        match r with
        | .done y => y.val = row.val ++ List.replicate (n.val - j.val) 0#i64
        | .cont p => p.2.val ≤ n.val ∧ p.1.val.length = p.2.val ∧
            p.1.val = row.val ++ List.replicate (p.2.val - j.val) 0#i64 ∧
              n.val - p.2.val < n.val - j.val ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
    step*
    · refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · have h1 : row1.val.length = row.val.length + 1 := by rw [row1_post]; simp
        scalar_tac
      · have e : j1.val - j.val = 1 := by scalar_tac
        rw [e, List.replicate_one]
        simpa using row1_post
      · scalar_tac
    · have e : n.val - j.val = 0 := by scalar_tac
      rw [e]
      simp

  @[step]
  theorem loop0_loop0_spec (n : Usize) (row : alloc.vec.Vec I64) (j : Usize)
      (hn : n.val ≤ 500) (hj : j.val ≤ n.val) (hrow : row.val.length = j.val) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ (row' : alloc.vec.Vec I64) =>
        row'.val = row.val ++ List.replicate (n.val - j.val) 0#i64 ∧ row'.val.length = n.val ⦄ := by
    refine Aeneas.Std.loop.spec_decr_nat (α := alloc.vec.Vec I64 × Usize) (β := alloc.vec.Vec I64)
      (measure := fun p => n.val - p.2.val)
      (inv := fun p => p.2.val ≤ n.val ∧ j.val ≤ p.2.val ∧ p.1.val.length = p.2.val ∧
        p.1.val = row.val ++ List.replicate (p.2.val - j.val) 0#i64)
      (post := fun row' => row'.val = row.val ++ List.replicate (n.val - j.val) 0#i64 ∧
        row'.val.length = n.val)
      (body := fun p : alloc.vec.Vec I64 × Usize =>
        Aegis.MinInsertions.min_insertions_loop0_loop0.body n p.1 p.2)
      (x := (row, j)) ?_ ?_
    · rintro ⟨r, jj⟩ h
      have h1 : jj.val ≤ n.val := h.1
      have h2 : j.val ≤ jj.val := h.2.1
      have h3 : r.val.length = jj.val := h.2.2.1
      have h4 : r.val = row.val ++ List.replicate (jj.val - j.val) 0#i64 := h.2.2.2
      have hb := loop0_loop0_body_spec n r jj hn h1 h3
      refine WP.spec_mono hb ?_
      rintro (⟨r', jj'⟩ | _) h'
      · dsimp only at h' ⊢
        obtain ⟨hm1, hm2, hm3, hm4⟩ := h'
        refine ⟨⟨hm1, ?_, hm2, ?_⟩, hm4⟩
        · omega
        have e : jj.val - j.val + (jj'.val - jj.val) = jj'.val - j.val := by omega
        rw [hm3, h4, List.append_assoc, ← List.replicate_add, e]
      · dsimp only at h' ⊢
        refine ⟨?_, ?_⟩
        · have e : jj.val - j.val + (n.val - jj.val) = n.val - j.val := by scalar_tac
          rw [h', h4, List.append_assoc, ← List.replicate_add, e]
        · rw [h', List.length_append, h4, List.length_append, List.length_replicate,
            List.length_replicate]
          scalar_tac
    · exact ⟨hj, le_rfl, hrow, by simp⟩

  @[step]
  theorem zeros_row_spec (n : Usize) (hn : n.val ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n (alloc.vec.Vec.new I64) 0#usize
        ⦃ (row' : alloc.vec.Vec I64) => row'.val = List.replicate n.val 0#i64 ⦄ := by
    have h := loop0_loop0_spec n (alloc.vec.Vec.new I64) 0#usize hn (by simp) (by simp)
    refine WP.spec_mono h ?_
    rintro r ⟨h1, h2⟩
    simpa using h1

  theorem loop0_body_spec (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Usize)
      (hn : n.val ≤ 500) (hi : i.val ≤ n.val)
      (hl : dp.val.length = i.val)
      (hr : ∀ k, k < i.val → ∃ r : alloc.vec.Vec I64, dp.val[k]? = some r ∧
        r.val = List.replicate n.val 0#i64) :
      Aegis.MinInsertions.min_insertions_loop0.body n dp i ⦃ r =>
        match r with
        | .done y => y.val.length = n.val ∧ ∀ k, k < n.val → ∃ r : alloc.vec.Vec I64,
            y.val[k]? = some r ∧ r.val = List.replicate n.val 0#i64
        | .cont p => p.2.val ≤ n.val ∧ p.1.val.length = p.2.val ∧
            (∀ k, k < p.2.val → ∃ r : alloc.vec.Vec I64, p.1.val[k]? = some r ∧
              r.val = List.replicate n.val 0#i64) ∧ n.val - p.2.val < n.val - i.val ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0.body
    step*
    refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
    · rw [dp1_post, List.length_append, hl]
      simp only [List.length_singleton]
      omega
    · intro k hk
      by_cases hki : k < i.val
      · obtain ⟨r, hr1, hr2⟩ := hr k hki
        refine ⟨r, ?_, hr2⟩
        rw [dp1_post, List.getElem?_append_left (l₂ := [row]) (by omega)]
        exact hr1
      · have hki' : k = i.val := by omega
        subst hki'
        refine ⟨row, ?_, row_post⟩
        rw [dp1_post, List.getElem?_append_right (l₂ := [row]) (i := i.val) (by omega)]
        have e : i.val - dp.val.length = 0 := by omega
        rw [e]
        simp

  @[step]
  theorem loop0_spec (n : Usize) (hn : n.val ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n (alloc.vec.Vec.new (alloc.vec.Vec I64)) 0#usize
        ⦃ (dp : alloc.vec.Vec (alloc.vec.Vec I64)) =>
          dp.val.length = n.val ∧ ∀ k, k < n.val → ∃ r : alloc.vec.Vec I64,
            dp.val[k]? = some r ∧ r.val = List.replicate n.val 0#i64 ⦄ := by
    refine Aeneas.Std.loop.spec_decr_nat (α := alloc.vec.Vec (alloc.vec.Vec I64) × Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec I64))
      (measure := fun p => n.val - p.2.val)
      (inv := fun p => p.2.val ≤ n.val ∧ p.1.val.length = p.2.val ∧
        ∀ k, k < p.2.val → ∃ r : alloc.vec.Vec I64, p.1.val[k]? = some r ∧
          r.val = List.replicate n.val 0#i64)
      (post := fun dp => dp.val.length = n.val ∧ ∀ k, k < n.val → ∃ r : alloc.vec.Vec I64,
        dp.val[k]? = some r ∧ r.val = List.replicate n.val 0#i64)
      (body := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        Aegis.MinInsertions.min_insertions_loop0.body n p.1 p.2)
      (x := (alloc.vec.Vec.new (alloc.vec.Vec I64), 0#usize)) ?_ ?_
    · rintro ⟨dp, i⟩ h
      have hb := loop0_body_spec n dp i hn h.1 h.2.1 h.2.2
      refine WP.spec_mono hb ?_
      rintro (⟨dp', i'⟩ | y) h'
      · dsimp only at h' ⊢
        exact ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2⟩
      · dsimp only at h' ⊢
        exact h'
    · refine ⟨by simp, by simp, ?_⟩
      intro k hk
      simp at hk

  @[step]
  theorem zeros_spec (n : Usize) (hn : n.val ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n (alloc.vec.Vec.new (alloc.vec.Vec I64)) 0#usize
        ⦃ (dp : alloc.vec.Vec (alloc.vec.Vec I64)) => TableOk dp n.val ∧
          ∀ (i j : Nat), i < n.val → j < n.val → cell dp i j = 0 ⦄ := by
    have h := loop0_spec n hn
    refine WP.spec_mono h ?_
    rintro dp ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨r, hr1, hr2⟩ := h2 i hi
      exact ⟨r, hr1, by rw [hr2]; simp⟩
    · intro i j hi hj
      obtain ⟨r, hr1, hr2⟩ := h2 i hi
      have hx : r.val[j]? = some 0#i64 := by
        rw [hr2, List.getElem?_eq_getElem (List.length_replicate ▸ hj)]
        simp
      rw [cell_eq_val hr1 hx]
      simp

  /-! ### The main DP loops -/

  theorem TableOk.lt_length {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {n : Nat}
      (h : TableOk dp n) {i : Nat} (hi : i < n) : i < dp.val.length := by
    obtain ⟨r, hr, _⟩ := h i hi
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hr
    exact absurd hr (by simp)

  theorem TableOk.row_len {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {n : Nat}
      (h : TableOk dp n) {i : Nat} (hi : i < n) {r : alloc.vec.Vec I64}
      (hr : dp.val[i]? = some r) : r.val.length = n := by
    obtain ⟨r', hr', hrl⟩ := h i hi
    rw [hr] at hr'
    simp only [Option.some.injEq] at hr'
    subst hr'
    exact hrl

  theorem TableOk.row_len_get {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {n : Nat}
      (h : TableOk dp n) (i : Nat) (hi : i < n) {hb : i < dp.val.length} :
      (dp.val[i]'hb).length = n := by
    obtain ⟨r, hr, hrn⟩ := h i hi
    rw [List.getElem?_eq_getElem hb] at hr
    simp only [Option.some.injEq] at hr
    rw [hr]
    exact hrn

  /-- All cells of `dp` that correspond to sub-strings of length `< len` hold the value `MI`. -/
  def FilledUpTo (S : List U8) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (n len : Nat) : Prop :=
    ∀ (i j : Nat), i < n → j < n → j - i + 1 < len → cell dp i j = (MI S i j : Int)

  theorem cell_of_row {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i j : Nat}
      {r : alloc.vec.Vec I64} (h : dp.val[i]? = some r) : cell dp i j = rcell r.val j := by
    simp only [cell, h]

  /-- Overwriting the cell `(a, b)` of the matrix leaves all other cells unchanged. -/
  theorem cell_set_set (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (row : alloc.vec.Vec I64)
      (a b : Usize) (y : I64) (ha : dp.val[a.val]? = some row)
      (hb : b.val < row.val.length) (i j : Nat) :
      cell (dp.set a (row.set b y)) i j =
        if a.val = i ∧ b.val = j then y.val else cell dp i j := by
    have halen : a.val < dp.val.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at ha
      exact absurd ha (by simp)
    have hcell : cell (dp.set a (row.set b y)) i j =
        if a.val = i then (if b.val = j then y.val else rcell row.val j) else cell dp i j :=
      cell_set_row dp a row halen b y hb i j
    rw [hcell]
    by_cases hai : a.val = i
    · rw [if_pos hai]
      by_cases hbj : b.val = j
      · rw [if_pos hbj, if_pos ⟨hai, hbj⟩]
      · rw [if_neg hbj, if_neg (by omega)]
        rw [← hai, cell_of_row ha]
    · rw [if_neg hai, if_neg (by omega)]

  /-- Invariant of the inner loop that fills the diagonal of sub-strings of length `len`. -/
  def InvIn (S : List U8) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (n len start : Nat) : Prop :=
    TableOk dp n ∧ 2 ≤ len ∧ len ≤ n ∧ start ≤ n ∧ FilledUpTo S dp n len ∧
      (∀ st, st < start → st + len ≤ n →
        cell dp st (st + len - 1) = (MI S st (st + len - 1) : Int))

  theorem MI_eq_of_ne (S : List U8) (i j : Nat) (hij : i < j) (hne : S[i]? ≠ S[j]?) :
      MI S i j = 1 + min (MI S (i + 1) j) (MI S i (j - 1)) := by
    rw [MI_def_lt S i j hij, if_neg hne]

  theorem MI_eq_of_eq (S : List U8) (i j : Nat) (hij : i < j) (heq : S[i]? = S[j]?) :
      MI S i j = MI S (i + 1) (j - 1) := by
    rw [MI_def_lt S i j hij, if_pos heq]

  theorem one_add_min (a b : Int) : 1 + min a b = if a < b then a + 1 else b + 1 := by
    rcases lt_or_ge a b with h | h
    · rw [if_pos h, min_eq_left (le_of_lt h)]; omega
    · rw [if_neg (by omega), min_eq_right h]; omega

  /-- Overwriting the single cell `(start, end)` with the value `MI` keeps the invariant. -/
  theorem InvIn_step (S : List U8) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (n len start «end» : Usize) (v : I64) (row : alloc.vec.Vec I64)
      (hinv : InvIn S dp n.val len.val start.val)
      (hguard : start.val + len.val ≤ n.val)
      (hrow : dp.val[start.val]? = some row)
      (hb : «end».val < row.val.length)
      (hend : «end».val = start.val + len.val - 1)
      (hval : v.val = (MI S start.val «end».val : Int)) :
      InvIn S (dp.set start (row.set «end» v)) n.val len.val (start.val + 1) ∧
        n.val - (start.val + 1) < n.val - start.val := by
    obtain ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ := hinv
    have hstartn' : start.val < n.val := by omega
    have hrowlen : row.val.length = n.val := by
      obtain ⟨r, hr, hrn⟩ := htab start.val hstartn'
      rw [hr] at hrow
      simp only [Option.some.injEq] at hrow
      subst hrow
      exact hrn
    have hstartlen : start.val < dp.val.length := by
      obtain ⟨r, hr, _⟩ := htab start.val hstartn'
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hr
      exact absurd hr (by simp)
    have hcellunchanged : ∀ i j, ¬(start.val = i ∧ «end».val = j) →
        cell (dp.set start (row.set «end» v)) i j = cell dp i j := by
      intro i j hij
      rw [cell_set_set dp row start «end» v hrow hb i j, if_neg hij]
    have hnewcell : cell (dp.set start (row.set «end» v)) start.val «end».val = v.val := by
      rw [cell_set_set dp row start «end» v hrow hb start.val «end».val, if_pos ⟨rfl, rfl⟩]
    have hdp' : (dp.set start (row.set «end» v)).val = dp.val.set start.val (row.set «end» v) := by
      simp [alloc.vec.Vec.set]
    refine ⟨⟨?_, hlen2, hlenn, by omega, ?_, ?_⟩, by omega⟩
    · intro i hi
      by_cases hicase : start.val = i
      · refine ⟨row.set «end» v, ?_, ?_⟩
        · rw [hdp', List.getElem?_set, if_pos hicase, if_pos hstartlen]
        · rw [alloc.vec.Vec.set_val_eq, List.length_set, hrowlen]
      · obtain ⟨r, hr, hrn⟩ := htab i hi
        refine ⟨r, ?_, hrn⟩
        rw [hdp', List.getElem?_set, if_neg (by omega)]
        exact hr
    · intro i j hi hj hlt
      rw [hcellunchanged i j ?_]
      exact hfill i j hi hj hlt
      rintro ⟨h1, h2⟩
      subst h1; subst h2
      omega
    · intro st hst hstn
      by_cases hcase : st = start.val
      · subst hcase
        have he : start.val + len.val - 1 = «end».val := by omega
        rw [he, hnewcell]
        exact hval
      · rw [hcellunchanged st (st + len.val - 1) ?_]
        exact hdiag st (by omega) hstn
        rintro ⟨h1, h2⟩
        omega

  /-- Unfolding lemma for `Vec.index_mut_usize` applied to a continuation. -/
  theorem bind_index_mut_usize {β : Type} (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (start : Usize)
      (hbound : start.val < dp.val.length)
      (f : alloc.vec.Vec I64 → (alloc.vec.Vec I64 → alloc.vec.Vec (alloc.vec.Vec I64)) →
        Result β) :
      (do let (v, back) ← dp.index_mut_usize start; f v back) =
        f (dp.val[start.val]'hbound) (dp.set start) := by
    have key : (dp[start.val]? : Option (alloc.vec.Vec I64)) = some (dp.val[start.val]'hbound) := by
      show (dp.val[start.val]? : Option _) = _
      rw [List.getElem?_eq_getElem hbound]
    simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize]
    rw [key]
    simp only [Result.ok.injEq]
    simp

  /-- The "read a cell, write a cell" pattern of the DP update, as a rewrite rule:
  reading the cells `(start, end)` never triggers a failure and the mutated matrix is
  `dp.set start (row.set end v)` where `row` is the `start`-th row. -/
  theorem mut_set_eq (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (start «end» : Usize)
      (row : alloc.vec.Vec I64) (v : I64)
      (hrow : dp.val[start.val]? = some row) (hb : «end».val < row.val.length) :
      (do let (v1, back) ← dp.index_mut_usize start
          let (_, back1) ← v1.index_mut_usize «end»
          ok (back (back1 v))) = ok (dp.set start (row.set «end» v)) := by
    simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
      alloc.vec.Vec.getElem?_Nat_eq, hrow]
    simp [List.getElem?_eq_getElem hb]

  /-- Converting a `getElem`-form cell value into a `getElem?`-form fact. -/
  theorem getElem?_eq_of_val_eq {α : Type} {l : List α} {n : Nat} (hi : n < l.length) {x : α}
      (h : x = l[n]'hi) : l[n]? = some x := by
    rw [h, List.getElem?_eq_getElem hi]

  /-- Reading a cell of a row: the postcondition is in `Option` form. -/
  @[step]
  theorem alloc.vec.Vec.index_usize_val_spec (v : alloc.vec.Vec I64) (i : Usize)
      (hbound : i.val < v.val.length) :
      v.index_usize i ⦃ (x : I64) => v.val[i.val]? = some x ⦄ := by
    simp only [alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq]
    simp [List.getElem?_eq_getElem hbound]

  theorem loop1_loop0_body_spec (s : Slice U8) (n len start : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hs : s.val.length = n.val) (hn : n.val ≤ 500)
      (h : InvIn s.val dp n.val len.val start.val) :
      Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len dp start ⦃ r =>
        match r with
        | .done y => TableOk y n.val ∧ FilledUpTo s.val y n.val (len.val + 1)
        | .cont p => InvIn s.val p.1 n.val len.val p.2.val ∧
            n.val - p.2.val < n.val - start.val ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
    step*
    · simp only [InvIn] at h
      obtain ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ := h
      have hguard : i.val ≤ n.val := ‹i ≤ n›
      have hiv : i.val = start.val + len.val := i_post
      have henv : «end».val + 1 = i.val := by omega
      have hslen : start.val < s.val.length := by rw [hs]; omega
      have helen : «end».val < s.val.length := by rw [hs]; omega
      have hstartend : start.val < «end».val := by omega
      have hguard2 : start.val + len.val ≤ n.val := by omega
      have hstartn' : start.val < n.val := by omega
      have hstartlen : start.val < dp.val.length := htab.lt_length hstartn'
      have hrowlen : (dp.val[start.val]'hstartlen).val.length = n.val :=
        htab.row_len hstartn' (List.getElem?_eq_getElem hstartlen)
      have hbend : «end».val < (dp.val[start.val]'hstartlen).val.length := by
        rw [hrowlen]; omega
      have hsstart : s.val[start.val]? = some i1 := by
        rw [List.getElem?_eq_getElem hslen, ← i1_post]
      have hsend : s.val[«end».val]? = some i2 := by
        rw [List.getElem?_eq_getElem helen, ← i2_post]
      by_cases hc : i1 = i2
      · have hseq : s.val[start.val]? = s.val[«end».val]? := by rw [hsstart, hsend, hc]
        rw [ite_eq_left hc]
        by_cases hl2 : len = 2#usize
        · rw [ite_eq_left hl2]
          rw [bind_index_mut_usize dp start hstartlen]
          step*
          obtain ⟨w, back⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          rw [start1_post]
          have hlen1 : len.val = 2 := by rw [hl2]; simp
          have hval : (0#i64).val = (MI s.val start.val «end».val : Int) := by
            have hm : MI s.val start.val «end».val = 0 := by
              rw [MI_eq_of_eq _ _ _ hstartend hseq]
              have h1 : «end».val - 1 = start.val := by omega
              rw [h1]
              exact MI_self _ _ _ (by omega)
            rw [hm]; simp
          refine InvIn_step s.val dp n len start «end» 0#i64 (dp.val[start.val]'hstartlen)
            ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ hguard2 ?_ hbend (by omega) hval
          exact List.getElem?_eq_getElem hstartlen
        · rw [ite_eq_right hl2]
          simp only [step_simps]
          have hlt1 : start.val + 1 < dp.val.length := htab.lt_length (by omega)
          have hrow' : (dp.val[start.val + 1]'hlt1).length = n.val :=
            htab.row_len_get (start.val + 1) (by omega) (hb := hlt1)
          let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
          let* ⟨ v, v_post ⟩ ← alloc.vec.Vec.index_usize_spec
          let* ⟨ i4, i4_post, i4_post1 ⟩ ← Usize.sub_spec
          let* ⟨ i5, i5_post ⟩ ← alloc.vec.Vec.index_usize_spec
          have v_post' : dp.val[i3.val]? = some v :=
            getElem?_eq_of_val_eq (l := dp.val) (n := i3.val) (x := v) (by omega) v_post
          have hrow'' : v.val.length = n.val := htab.row_len (by omega) v_post'
          have i5_post' : v.val[i4.val]? = some i5 :=
            getElem?_eq_of_val_eq (l := v.val) (n := i4.val) (x := i5) (by omega) i5_post
          have hval : i5.val = (MI s.val start.val «end».val : Int) := by
            have hcellv : cell dp (start.val + 1) («end».val - 1) = i5.val := by
              have h1 := cell_eq_val v_post' i5_post'
              rw [i3_post, i4_post] at h1
              exact h1
            have hfill' : cell dp (start.val + 1) («end».val - 1) =
                (MI s.val (start.val + 1) («end».val - 1) : Int) :=
              hfill (start.val + 1) («end».val - 1) (by omega) (by omega) (by omega)
            have hMI : (MI s.val (start.val + 1) («end».val - 1) : Int) =
                (MI s.val start.val «end».val : Int) := by
              rw [MI_eq_of_eq s.val start.val «end».val hstartend hseq]
            rw [← hcellv, hfill', hMI]
          let* ⟨ x, x_post, x_post1 ⟩ ← alloc.vec.Vec.index_mut_usize_spec
          obtain ⟨w, back⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          obtain ⟨w2, back2⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          rw [start1_post]
          exact InvIn_step s.val dp n len start «end» i5 (dp.val[start.val]'hstartlen)
            ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ hguard2
            (List.getElem?_eq_getElem hstartlen) hbend (by omega) hval
      · rw [ite_eq_right hc]
        simp only [step_simps]
        have hlt1 : start.val + 1 < dp.val.length := htab.lt_length (by omega)
        have hrow' : (dp.val[start.val + 1]'hlt1).length = n.val :=
          htab.row_len_get (start.val + 1) (by omega) (hb := hlt1)
        let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
        let* ⟨ v, v_post ⟩ ← alloc.vec.Vec.index_usize_spec
        let* ⟨ left, left_post ⟩ ← alloc.vec.Vec.index_usize_spec
        let* ⟨ v1, v1_post ⟩ ← alloc.vec.Vec.index_usize_spec
        let* ⟨ i4, i4_post, i4_post1 ⟩ ← Usize.sub_spec
        let* ⟨ right, right_post ⟩ ← alloc.vec.Vec.index_usize_spec
        have hne : s.val[start.val]? ≠ s.val[«end».val]? := by
          rw [hsstart, hsend]
          simpa using hc
        have v_post' : dp.val[i3.val]? = some v :=
          getElem?_eq_of_val_eq (l := dp.val) (n := i3.val) (x := v) (by omega) v_post
        have v1_post' : dp.val[start.val]? = some v1 :=
          getElem?_eq_of_val_eq (l := dp.val) (n := start.val) (x := v1) (by omega) v1_post
        have hvlen : v.val.length = n.val := htab.row_len (by omega) v_post'
        have hv1len : v1.val.length = n.val := htab.row_len (by omega) v1_post'
        have left_post' : v.val[«end».val]? = some left :=
          getElem?_eq_of_val_eq (l := v.val) (n := «end».val) (x := left) (by omega) left_post
        have right_post' : v1.val[i4.val]? = some right :=
          getElem?_eq_of_val_eq (l := v1.val) (n := i4.val) (x := right) (by omega) right_post
        have hleft : left.val = (MI s.val (start.val + 1) «end».val : Int) := by
          have h1 := cell_eq_val v_post' left_post'
          rw [i3_post] at h1
          have hfill' : cell dp (start.val + 1) («end».val) =
              (MI s.val (start.val + 1) («end».val) : Int) :=
            hfill (start.val + 1) («end».val) (by omega) (by omega) (by omega)
          rw [hfill'] at h1
          exact h1.symm
        have hright : right.val = (MI s.val start.val («end».val - 1) : Int) := by
          have h1 := cell_eq_val v1_post' right_post'
          rw [i4_post] at h1
          have hfill' : cell dp start.val («end».val - 1) =
              (MI s.val start.val («end».val - 1) : Int) :=
            hfill start.val («end».val - 1) (by omega) (by omega) (by omega)
          rw [hfill'] at h1
          exact h1.symm
        have hMI : (MI s.val start.val «end».val : Int) =
            1 + min (MI s.val (start.val + 1) «end».val : Int)
              (MI s.val start.val («end».val - 1) : Int) := by
          rw [MI_eq_of_ne s.val start.val «end».val hstartend hne]
          push_cast
          simp
        by_cases hlt : left < right
        · rw [ite_eq_left hlt]
          let* ⟨ i5, i5_post ⟩ ← I64.add_spec
          let* ⟨ x, x_post, x_post1 ⟩ ← alloc.vec.Vec.index_mut_usize_spec
          obtain ⟨w, back⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          obtain ⟨w2, back2⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          rw [start1_post]
          have hlt' : (MI s.val (start.val + 1) «end».val : Int) <
              (MI s.val start.val («end».val - 1) : Int) := by
            rw [← hleft, ← hright]
            simpa using hlt
          have hval : i5.val = (MI s.val start.val «end».val : Int) := by
            rw [i5_post, hMI, one_add_min, if_pos hlt', hleft]
          exact InvIn_step s.val dp n len start «end» i5 (dp.val[start.val]'hstartlen)
            ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ hguard2
            (List.getElem?_eq_getElem hstartlen) hbend (by omega) hval
        · rw [ite_eq_right hlt]
          let* ⟨ i5, i5_post ⟩ ← I64.add_spec
          · rw [hright]
            have h2 : MI s.val start.val («end».val - 1) ≤ («end».val - 1) - start.val + 1 :=
              MI_le s.val start.val («end».val - 1)
            have hone : (1#i64).val = 1 := by simp
            have hmax : I64.max = 9223372036854775807 := Aeneas.Std.I64.max_eq
            rw [hone, hmax]
            omega
          let* ⟨ x, x_post, x_post1 ⟩ ← alloc.vec.Vec.index_mut_usize_spec
          obtain ⟨w, back⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          obtain ⟨w2, back2⟩ := x
          dsimp only at x_post x_post1
          subst x_post
          subst x_post1
          step*
          rw [start1_post]
          have hlt' : ¬ ((MI s.val (start.val + 1) «end».val : Int) <
              (MI s.val start.val («end».val - 1) : Int)) := by
            rw [← hleft, ← hright]
            simpa using hlt
          have hval : i5.val = (MI s.val start.val «end».val : Int) := by
            rw [i5_post, hMI, one_add_min, if_neg hlt', hright]
          exact InvIn_step s.val dp n len start «end» i5 (dp.val[start.val]'hstartlen)
            ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ hguard2
            (List.getElem?_eq_getElem hstartlen) hbend (by omega) hval
    · -- the loop is finished: extend the filled region by the last diagonal
      simp only [InvIn] at h
      obtain ⟨htab, hlen2, hlenn, hstartn, hfill, hdiag⟩ := h
      have hiv : i.val = start.val + len.val := i_post
      have hgt : n.val < start.val + len.val := by
        have h1 : ¬ (i.val ≤ n.val) := by
          have hg : ¬ (i ≤ n) := ‹¬ (i ≤ n)›
          simpa only [UScalar.le_equiv] using hg
        omega
      refine ⟨htab, ?_⟩
      intro a b ha hb hlt
      by_cases hlt' : b - a + 1 < len.val
      · exact hfill a b ha hb hlt'
      · have hbe : b = a + len.val - 1 := by omega
        subst hbe
        have hile : a + len.val ≤ n.val := by omega
        have histart : a < start.val := by omega
        exact hdiag a histart hile

  /-- `FilledUpTo` gets weaker when the length bound decreases. -/
  theorem FilledUpTo.anti {S : List U8} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {n len len' : Nat}
      (h : FilledUpTo S dp n len') (hl : len ≤ len') : FilledUpTo S dp n len :=
    fun i j hi hj hlt => h i j hi hj (by omega)

  /-- The inner loop of `min_insertions` fills the diagonal of sub-strings of length `len`. -/
  @[step]
  theorem loop1_loop0_spec (s : Slice U8) (n len : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hs : s.val.length = n.val) (hn : n.val ≤ 500)
      (hinv : InvIn s.val dp n.val len.val 0) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len 0#usize ⦃
        (dp' : alloc.vec.Vec (alloc.vec.Vec I64)) =>
          TableOk dp' n.val ∧ FilledUpTo s.val dp' n.val (len.val + 1) ⦄ := by
    refine Aeneas.Std.loop.spec_decr_nat (α := alloc.vec.Vec (alloc.vec.Vec I64) × Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec I64))
      (measure := fun p => n.val - p.2.val)
      (inv := fun p => InvIn s.val p.1 n.val len.val p.2.val)
      (post := fun dp' => TableOk dp' n.val ∧ FilledUpTo s.val dp' n.val (len.val + 1))
      (body := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len p.1 p.2)
      (x := (dp, 0#usize)) ?_ hinv
    rintro ⟨dp, st⟩ hinv
    refine WP.spec_mono (loop1_loop0_body_spec s n len st dp hs hn hinv) ?_
    rintro (⟨dp', st'⟩ | y) h'
    · exact ⟨h'.1, h'.2⟩
    · exact h'

  /-- One iteration of the outer loop of `min_insertions`. -/
  theorem loop1_body_spec (s : Slice U8) (n : Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (len : Usize)
      (hs : s.val.length = n.val) (hn : n.val ≤ 500)
      (hinv : TableOk dp n.val ∧ 2 ≤ len.val ∧ len.val ≤ n.val + 1 ∧
        FilledUpTo s.val dp n.val len.val) :
      Aegis.MinInsertions.min_insertions_loop1.body s n dp len ⦃ r =>
        match r with
        | .done y => TableOk y n.val ∧ FilledUpTo s.val y n.val (n.val + 1)
        | .cont p => (TableOk p.1 n.val ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1 ∧
            FilledUpTo s.val p.1 n.val p.2.val) ∧
              (n.val + 1) - p.2.val < (n.val + 1) - len.val ⦄ := by
    obtain ⟨htab, hlen2, hlenn, hfill⟩ := hinv
    unfold Aegis.MinInsertions.min_insertions_loop1.body
    simp only [step_simps]
    by_cases hle : len ≤ n
    · rw [ite_eq_left hle]
      have hlenv : len.val ≤ n.val := by simpa only [UScalar.le_equiv] using hle
      have hinv0 : InvIn s.val dp n.val len.val 0 :=
        ⟨htab, hlen2, hlenv, by simp, hfill, by intro st hst; omega⟩
      let* ⟨ dp1, hdp1a, hdp1b ⟩ ← loop1_loop0_spec s n len dp hs hn hinv0
      let* ⟨ len1, len1_post ⟩ ← Usize.add_spec
      rw [len1_post]
      exact ⟨hdp1a, by omega, by omega, hdp1b, by omega⟩
    · rw [ite_eq_right hle]
      have hgt : n.val < len.val := by
        have h' := hle
        simp only [UScalar.le_equiv] at h'
        omega
      have hlen : len.val = n.val + 1 := by omega
      simp only [WP.spec_ok]
      refine ⟨htab, ?_⟩
      rw [← hlen]
      exact hfill

  /-- The outer loop of `min_insertions` fills the whole matrix. -/
  @[step]
  theorem loop1_spec (s : Slice U8) (n : Usize) (hs : s.val.length = n.val)
      (hn : n.val ≤ 500) (hn2 : 2 ≤ n.val)
      (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (hinv0 : TableOk dp n.val ∧ ∀ i j, i < n.val → j < n.val → cell dp i j = 0) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp 2#usize ⦃
        (dp' : alloc.vec.Vec (alloc.vec.Vec I64)) =>
          TableOk dp' n.val ∧ FilledUpTo s.val dp' n.val (n.val + 1) ⦄ := by
    obtain ⟨htab, hzero⟩ := hinv0
    have hfill2 : FilledUpTo s.val dp n.val 2 := by
      intro i j hi hj hlt
      have hji : j ≤ i := by omega
      rw [hzero i j hi hj, MI_self s.val i j hji]
      simp
    refine Aeneas.Std.loop.spec_decr_nat (α := alloc.vec.Vec (alloc.vec.Vec I64) × Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec I64))
      (measure := fun p => (n.val + 1) - p.2.val)
      (inv := fun p => TableOk p.1 n.val ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1 ∧
        FilledUpTo s.val p.1 n.val p.2.val)
      (post := fun dp' => TableOk dp' n.val ∧ FilledUpTo s.val dp' n.val (n.val + 1))
      (body := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        Aegis.MinInsertions.min_insertions_loop1.body s n p.1 p.2)
      (x := (dp, 2#usize)) ?_ ?_
    · rintro ⟨dp, len⟩ hinv
      refine WP.spec_mono (loop1_body_spec s n dp len hs hn hinv) ?_
      rintro (⟨dp', len'⟩ | y) h'
      · simpa using h'
      · simpa using h'
    · have h2 : (2#usize).val = 2 := by simp
      rw [h2]
      exact ⟨htab, by omega, by omega, hfill2⟩

  /-- The entry `(i,j)` of the matrix, read through the two indexing operations of the code. -/
  theorem cell_of_index (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Usize)
      (hi : i.val < dp.val.length) (hj : j.val < (dp.val[i.val]'hi).val.length) :
      cell dp i.val j.val = ((dp.val[i.val]'hi).val[j.val]'hj).val :=
    cell_eq_val (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)

  /-- `min_insertions` computes `MI s 0 (len s - 1)`. -/
  theorem min_insertions_MI (s : Slice U8) (n : Usize)
      (hs : s.val.length = n.val) (hn : n.val ≤ 500) (hn1 : 1 ≤ n.val) :
      Aegis.MinInsertions.min_insertions s ⦃ (r : I64) =>
        r.val = (MI s.val 0 (n.val - 1) : Int) ⦄ := by
    have hnl : Slice.len s = n := UScalar.eq_of_val_eq (by simpa using hs)
    by_cases hn2 : 2 ≤ n.val
    · clear hn1
      unfold Aegis.MinInsertions.min_insertions
      simp only [step_simps]
      rw [hnl]
      have hge : ¬ (n ≤ 1#usize) := by
        rw [UScalar.le_equiv]
        have hone : (1#usize).val = 1 := by simp
        rw [hone]; omega
      rw [ite_eq_right hge]
      step*
      · have h0 : (0#usize).val = 0 := by simp
        rw [h0]
        exact dp1_post.lt_length (by omega)
      · rw [i_post]
        have hlen : v.val.length = n.val := by
          rw [v_post]
          exact dp1_post.row_len_get 0 (by omega) (hb := dp1_post.lt_length (by omega))
        rw [hlen]; omega
      · have hv0 : dp1.val[0]? = some v := by
          rw [v_post]
          exact List.getElem?_eq_getElem (h := dp1_post.lt_length (by omega))
        have hlen : v.val.length = n.val := by
          rw [v_post]
          exact dp1_post.row_len_get 0 (by omega) (hb := dp1_post.lt_length (by omega))
        have hi0 : v.val[i.val]? = some r := by
          rw [r_post]
        have hcell : cell dp1 0 i.val = r.val := cell_eq_val hv0 hi0
        have hMI : cell dp1 0 i.val = (MI s.val 0 i.val : Int) :=
          dp1_post1 0 i.val (by omega) (by omega) (by omega)
        rw [← hcell, hMI, i_post]
    · -- the input has length one
      have hn1' : n.val = 1 := by omega
      unfold Aegis.MinInsertions.min_insertions
      rw [hnl]
      have hle : n ≤ 1#usize := by
        rw [UScalar.le_equiv]
        have hone : (1#usize).val = 1 := by simp
        rw [hone]; omega
      rw [ite_eq_left hle]
      simp only [WP.spec_ok]
      have h0 : (0#i64).val = (0 : Int) := by simp
      rw [h0]
      have e : n.val - 1 = 0 := by omega
      rw [e]
      rw [MI_self s.val 0 0 (by omega)]
      simp

  /-! ### Specifications -/

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
  theorem spec_8 (s a b : Slice U8)
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
    intro r ra rb hr hra hrb
    have ha1 : 1 ≤ a.val.length := by rw [ha_len]; omega
    have hb1 : 1 ≤ b.val.length := by rw [hb_len]; omega
    have hMI_s := min_insertions_MI s (Slice.len s) (Slice.len_val s).symm
      (by rw [Slice.len_val, Slice.length]; exact hlen_upper)
      (by rw [Slice.len_val, Slice.length]; exact hlen_lower)
    rw [hr] at hMI_s
    simp only [WP.spec_ok] at hMI_s
    have hMI_a := min_insertions_MI a (Slice.len a) (Slice.len_val a).symm
      (by rw [Slice.len_val, Slice.length]; omega)
      (by rw [Slice.len_val, Slice.length]; exact ha1)
    rw [hra] at hMI_a
    simp only [WP.spec_ok] at hMI_a
    have hMI_b := min_insertions_MI b (Slice.len b) (Slice.len_val b).symm
      (by rw [Slice.len_val, Slice.length]; omega)
      (by rw [Slice.len_val, Slice.length]; exact hb1)
    rw [hrb] at hMI_b
    simp only [WP.spec_ok] at hMI_b
    simp only [Slice.len_val, Slice.length] at hMI_s hMI_a hMI_b
    have hne' : s.val[0]? ≠ s.val[s.val.length - 1]? := by
      intro h
      apply hne
      have h0 : s.val[0]? = some s.val[0] := List.getElem?_eq_getElem (by omega)
      have h1 : s.val[s.val.length - 1]? = some s.val[s.val.length - 1] :=
        List.getElem?_eq_getElem (by omega)
      rw [h0, h1] at h
      exact Option.some.inj h
    have ha_eq : ∀ (k : Nat), a.val[k]? = s.val[k + 1]? := by
      intro k
      by_cases hk : k < a.val.length
      · rw [List.getElem?_eq_getElem hk,
          List.getElem?_eq_getElem (show k + 1 < s.val.length by omega), ha_val k hk]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have hb_eq : ∀ (k : Nat), k < b.val.length → b.val[k]? = s.val[k]? := by
      intro k hk
      rw [List.getElem?_eq_getElem hk,
        List.getElem?_eq_getElem (show k < s.val.length by omega), hb_val k hk]
    have hA : MI a.val 0 (a.val.length - 1) = MI s.val 1 (s.val.length - 1) := by
      have h := MI_shift s.val a.val ha_eq 0 (a.val.length - 1)
      simp only [Nat.zero_add] at h
      rw [h]
      have e : (a.val.length - 1) + 1 = s.val.length - 1 := by omega
      rw [e]
    have hB : MI b.val 0 (b.val.length - 1) = MI s.val 0 (s.val.length - 2) := by
      have h := MI_same_le s.val b.val b.val.length hb_eq 0 (b.val.length - 1) (by omega)
      rw [h]
      have e : b.val.length - 1 = s.val.length - 2 := by omega
      rw [e]
    have hkey : MI s.val 0 (s.val.length - 1) =
        1 + min (MI s.val 1 (s.val.length - 1)) (MI s.val 0 (s.val.length - 2)) := by
      have h := MI_eq_of_ne s.val 0 (s.val.length - 1) (by omega) hne'
      have e : s.val.length - 1 - 1 = s.val.length - 2 := by omega
      rw [e] at h
      simpa using h
    rw [hMI_s, hMI_a, hMI_b, hA, hB, hkey]
    push_cast
    simp

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
