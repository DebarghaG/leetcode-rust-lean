import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_2` (minimum-insertion-steps-to-make-a-string-palindrome).
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

  /-! ### Auxiliary notions and lemmas for the no-failure proof (S2) -/

  /-- All the rows of `l` have length `n`. -/
  def RowsLen (n : Nat) (l : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ (k : Nat), k < l.length → (l[k]!).val.length = n

  /-- All the cells of the row list `l` are zero. -/
  def RowsZero (n : Nat) (l : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ (k j' : Nat), k < l.length → j' < n → ((l[k]!).val[j']!).val = 0

  /-- `dp` is an `n × n` matrix of `I64`. -/
  def MatInv (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dp.val.length = n ∧ RowsLen n dp.val

  /-- `dp` is an `n × n` matrix of zeros. -/
  def MatZeros (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    MatInv n dp ∧ RowsZero n dp.val

  /-- The value of cell `(i, j)` of the matrix `dp` (default value outside of the matrix). -/
  def cellVal (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((dp.val[i]!).val[j]!).val

  /-- All the cells of the matrix which are "finished" (of length `< len`, or of length exactly
  `len` and first index `< start`) are bounded by `length - 1`. -/
  def CellBnd (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (len start : Nat) : Prop :=
    ∀ (i j : Nat), i < n → j < n →
      (j - i + 1 < len ∨ (j - i + 1 = len ∧ i < start)) →
        cellVal dp i j ≤ ((j - i + 1 : Nat) : Int) - 1

  theorem getElem!_append_single {α : Type} [Inhabited α] (l : List α) (x : α) (k : Nat)
      (hk : k < (l ++ [x]).length) :
      (l ++ [x])[k]! = if k < l.length then l[k]! else x := by
    by_cases h : k < l.length
    · rw [List.getElem!_append_left l [x] k h, if_pos h]
    · rw [List.getElem!_append_right l [x] k (by omega), if_neg h]
      have hk' : k = l.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'; simp

  theorem RowsLen_append {n : Nat} {l : List (alloc.vec.Vec Std.I64)}
      {r : alloc.vec.Vec Std.I64} (h : RowsLen n l) (hr : r.val.length = n) :
      RowsLen n (l ++ [r]) := by
    intro k hk
    rw [getElem!_append_single l r k hk]
    by_cases hlt : k < l.length
    · rw [if_pos hlt]; exact h k hlt
    · rw [if_neg hlt]; exact hr

  theorem RowsZero_append {n : Nat} {l : List (alloc.vec.Vec Std.I64)}
      {r : alloc.vec.Vec Std.I64} (h : RowsZero n l)
      (hr : ∀ (j' : Nat), j' < n → (r.val[j']!).val = 0) :
      RowsZero n (l ++ [r]) := by
    intro k j' hk hj'
    rw [getElem!_append_single l r k hk]
    by_cases hlt : k < l.length
    · rw [if_pos hlt]; exact h k j' hlt hj'
    · rw [if_neg hlt]; exact hr j' hj'

  /-- The value of a cell after writing the cell `(s, e)`. -/
  theorem cellVal_set (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (s e : Std.Usize)
      (v : Std.I64) (i j : Nat)
      (hs : s.val < dp.val.length) (he : e.val < (dp.val[s.val]!).val.length) :
      cellVal (dp.set s ((dp.val[s.val]!).set e v)) i j =
        if i = s.val ∧ j = e.val then v.val else cellVal dp i j := by
    by_cases hc : i = s.val ∧ j = e.val
    · obtain ⟨rfl, rfl⟩ := hc
      rw [if_pos ⟨rfl, rfl⟩]
      unfold cellVal
      rw [alloc.vec.Vec.set_val_eq, List.set_getElem!_eq _ _ _ _ ⟨hs, rfl⟩,
        alloc.vec.Vec.set_val_eq, List.set_getElem!_eq _ _ _ _ ⟨he, rfl⟩]
    · rw [if_neg hc]
      by_cases hi : i = s.val
      · subst hi
        have hj : j ≠ e.val := fun h => hc ⟨rfl, h⟩
        unfold cellVal
        rw [alloc.vec.Vec.set_val_eq, List.set_getElem!_eq _ _ _ _ ⟨hs, rfl⟩,
          alloc.vec.Vec.set_val_eq, List.set_getElem!_ne _ _ _ _ (by omega)]
      · unfold cellVal
        rw [alloc.vec.Vec.set_val_eq, List.set_getElem!_ne _ _ _ _ (by omega)]

  /-- Writing a bounded cell to the matrix preserves the cell bound. -/
  theorem CellBnd_set {n len : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {s e : Std.Usize} {v : Std.I64}
      (hmat : MatInv n dp) (hbnd : CellBnd n dp len s.val)
      (hs : s.val < n) (he : e.val = s.val + len - 1) (hEn : e.val < n)
      (hlen2 : 2 ≤ len) (hv : v.val ≤ ((len : Nat) : Int) - 1) :
      CellBnd n (dp.set s ((dp.val[s.val]!).set e v)) len (s.val + 1) := by
    obtain ⟨hlen, hrows⟩ := hmat
    have hrow : (dp.val[s.val]!).val.length = n := hrows s.val (by omega)
    intro i j hi hj hproc
    rw [cellVal_set _ _ _ _ _ _ (by omega) (by rw [hrow]; exact hEn)]
    by_cases hc : i = s.val ∧ j = e.val
    · rw [if_pos hc]
      obtain ⟨rfl, rfl⟩ := hc
      rw [he]
      have : s.val + len - 1 - s.val + 1 = len := by omega
      rw [this]; exact hv
    · rw [if_neg hc]
      apply hbnd i j hi hj
      rcases hproc with h | ⟨h1, h2⟩
      · exact Or.inl h
      · right
        refine ⟨h1, ?_⟩
        rcases Nat.lt_or_ge i s.val with h' | h'
        · exact h'
        · exfalso
          apply hc
          have h3 : i = s.val := by omega
          refine ⟨h3, ?_⟩
          rw [he]; omega

  /-- `spec` implies that the computation returns a value. -/
  theorem spec_exists_ok {α : Type} {m : Result α} {p : α → Prop}
      (h : m ⦃ p ⦄) : ∃ r, m = ok r := by
    rcases Aeneas.Std.WP.spec_exists h with ⟨r, hr⟩
    induction m using Result.cases with
    | ret x => exact ⟨x, rfl⟩
    | vis e k =>
      simp only [Aeneas.Std.WP.spec_vis] at h
    | div =>
      simp only [Aeneas.Std.WP.spec_div] at h

  /-- The innermost loop of `min_insertions` (pushing `n` zeros into `row`) never fails and
  produces a row of length `n` filled with zeros. -/
  theorem loop0_loop0_spec (n : Std.Usize) (hn : n.val ≤ 500)
      (row : alloc.vec.Vec Std.I64) (j : Std.Usize)
      (hrow : row.val.length = j.val) (hj : j.val ≤ n.val)
      (hzero : ∀ (j' : Nat), j' < row.val.length → (row.val[j']!).val = 0) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ row' =>
        row'.val.length = n.val ∧
          ∀ (j' : Nat), j' < n.val → (row'.val[j']!).val = 0 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec Std.I64 × Std.Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec Std.I64 × Std.Usize =>
        p.1.val.length = p.2.val ∧ p.2.val ≤ n.val ∧
          ∀ (j' : Nat), j' < p.1.val.length → (p.1.val[j']!).val = 0)
    · rintro ⟨row, j⟩ ⟨hlen, hje, hz⟩
      dsimp only at hlen hje hz
      unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
      dsimp only
      spec_split as hc
      · -- `j < n`: push a zero
        step*
        have h2 := j1_post
        have hjn : j.val < n.val := by simpa using hc
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [row1_post, h2]; simp [hlen]
        · rw [h2]; omega
        · intro j' hj'
          rw [row1_post] at hj' ⊢
          by_cases h : j' < row.val.length
          · rw [List.getElem!_append_left _ _ _ h]; exact hz j' h
          · have hjj : j' = row.val.length := by
              simp only [List.length_append, List.length_singleton] at hj'
              omega
            subst hjj
            simp
        · rw [h2]; omega
      · -- `¬ j < n`: the row is full
        step*
    · -- the initial invariant
      exact ⟨hrow, hj, hzero⟩

  /-- The first loop of `min_insertions` (building the `n × n` matrix of zeros) never fails. -/
  theorem loop0_spec (n : Std.Usize) (hn : n.val ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n
        (alloc.vec.Vec.new (alloc.vec.Vec Std.I64)) 0#usize ⦃ dp' =>
        MatZeros n.val dp' ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize =>
        p.1.val.length = p.2.val ∧ p.2.val ≤ n.val ∧
          RowsLen n.val p.1.val ∧ RowsZero n.val p.1.val)
    · rintro ⟨dp, i⟩ ⟨h1, h2, h3, h4⟩
      dsimp only at h1 h2 h3 h4
      unfold Aegis.MinInsertions.min_insertions_loop0.body
      dsimp only
      spec_split as hc
      · -- `i < n`: push a new row of zeros
        have hsl : Aegis.MinInsertions.min_insertions_loop0_loop0 n
            (alloc.vec.Vec.new Std.I64) 0#usize ⦃ row =>
              row.val.length = n.val ∧
                ∀ (j' : Nat), j' < n.val → (row.val[j']!).val = 0 ⦄ :=
          loop0_loop0_spec n hn _ _ (by simp [alloc.vec.Vec.new]) (by simp)
            (by simp [alloc.vec.Vec.new])
        apply WP.spec_bind hsl
        rintro row ⟨hrowlen, hrowzero⟩
        step*
        have hdp := dp1_post
        have hi1 := i1_post
        have hcin : i.val < n.val := by simpa using hc
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hdp, hi1]; simp [h1]
        · rw [hi1]; omega
        · rw [hdp]; exact RowsLen_append h3 hrowlen
        · rw [hdp]; exact RowsZero_append h4 hrowzero
        · rw [hi1]; omega
      · -- `¬ i < n`: the matrix is complete
        step*
        have hge : ¬ (i.val < n.val) := by simpa using hc
        exact ⟨⟨by omega, h3⟩, h4⟩
    · -- the initial invariant
      refine ⟨by simp [alloc.vec.Vec.new], by simp, ?_, ?_⟩
      · intro k hk; simp [alloc.vec.Vec.new] at hk
      · intro k j' hk; simp [alloc.vec.Vec.new] at hk

  theorem RowsLen_set {n : Nat} {l : List (alloc.vec.Vec Std.I64)}
      {r : alloc.vec.Vec Std.I64} (h : RowsLen n l) (hr : r.val.length = n) (i : Nat) :
      RowsLen n (l.set i r) := by
    intro k hk
    rw [List.length_set] at hk
    by_cases hk' : k = i
    · subst hk'
      rw [List.set_getElem!_eq _ _ _ _ ⟨hk, rfl⟩]; exact hr
    · rw [List.set_getElem!_ne _ _ _ _ (by omega)]
      exact h k hk

  theorem MatInv_set {n : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      (s : Std.Usize) (r : alloc.vec.Vec Std.I64)
      (h : MatInv n dp) (hr : r.val.length = n) : MatInv n (dp.set s r) := by
    obtain ⟨hlen, hrows⟩ := h
    refine ⟨?_, ?_⟩
    · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen
    · intro k hk
      rw [alloc.vec.Vec.set_val_eq] at hk ⊢
      exact RowsLen_set hrows hr s.val k hk

  theorem getElem!_eq_getElem_of_lt {α : Type} [Inhabited α] {l : List α} {i : Nat}
      (h : i < l.length) : l[i]! = l[i]'h := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

  /-- The value of a cell read through two nested indexing operations. -/
  theorem cellVal_index {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} {i : Std.Usize}
      {row : alloc.vec.Vec Std.I64} {j : Std.Usize} {x : Std.I64}
      (hi : i.val < dp.val.length) (hrow : row = (↑dp)[i.val])
      (hj : j.val < row.val.length) (hx : x = (↑row)[j.val]) :
      x.val = cellVal dp i.val j.val := by
    subst hrow
    subst hx
    unfold cellVal
    have h1 := getElem!_eq_getElem_of_lt (i := i.val)
      (l := (↑dp : List (alloc.vec.Vec Std.I64))) hi
    have h2 := getElem!_eq_getElem_of_lt (i := j.val)
      (l := ↑((↑dp : List (alloc.vec.Vec Std.I64))[i.val]'hi)) (by simpa using hj)
    simp only [h1, h2]
    rfl

  /-- The invariant of the `cont` case of the inner loop. -/
  theorem cont_inv {n len : Nat} {dp' : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {start start1 : Std.Usize}
      (hmat' : MatInv n dp') (hbnd' : CellBnd n dp' len (start.val + 1))
      (hst : start.val + len ≤ n) (hs1 : start1.val = start.val + 1) :
      MatInv n dp' ∧ CellBnd n dp' len start1.val ∧ start1.val + len ≤ n + 1 ∧
        n + 1 - start1.val < n + 1 - start.val := by
    rw [hs1]
    refine ⟨hmat', hbnd', ?_, ?_⟩
    · omega
    · omega

  /-- The value of the cell read at `(start + 1, end)` is bounded. -/
  theorem rowLen_getElem {n : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {i : Std.Usize} (hi : i.val < dp.val.length)
      (h : (dp.val[i.val]!).val.length = n) :
      ((↑dp : List (alloc.vec.Vec Std.I64))[i.val]'hi).val.length = n := by
    rw [getElem!_eq_getElem_of_lt (h := hi)] at h
    exact h

  theorem CellBnd_lt {n len : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      (hbnd : CellBnd n dp len 0) (i j : Nat) (hi : i < n) (hj : j < n)
      (h : j - i + 1 < len) :
      cellVal dp i j ≤ ((j - i + 1 : Nat) : Int) - 1 :=
    hbnd i j hi hj (Or.inl h)

  /-- The inner loop of the second phase of `min_insertions`. -/
  theorem loop1_loop0_spec (s : Slice Std.U8) (n len : Std.Usize)
      (hn : n.val ≤ 500) (hsn : n.val = s.val.length)
      (hlen2 : 2 ≤ len.val) (hlenle : len.val ≤ n.val + 1)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (start : Std.Usize)
      (hmat : MatInv n.val dp) (hbnd : CellBnd n.val dp len.val start.val)
      (hst : start.val + len.val ≤ n.val + 1) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start ⦃ dp' =>
        MatInv n.val dp' ∧ CellBnd n.val dp' (len.val + 1) 0 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize =>
        n.val + 1 - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize =>
        MatInv n.val p.1 ∧ CellBnd n.val p.1 len.val p.2.val ∧
          p.2.val + len.val ≤ n.val + 1)
    · rintro ⟨dp, start⟩ ⟨hmat, hbnd, hst⟩
      dsimp only at hmat hbnd hst
      unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
      dsimp only
      step
      spec_split as hic
      · -- `i ≤ n`
        have hi1 : 1 ≤ i.val := by omega
        have hile : start.val + len.val ≤ n.val := by
          have h1 : i.val ≤ n.val := hic
          omega
        have hs : start.val < n.val := by omega
        have hs1n : start.val + 1 < n.val := by omega
        have hrowlen : (dp.val[start.val]!).val.length = n.val :=
          hmat.2 start.val (by have := hmat.1; omega)
        have hrowlen1 : (dp.val[start.val + 1]!).val.length = n.val :=
          hmat.2 _ (by have := hmat.1; omega)
        step
        have hend : «end».val = start.val + len.val - 1 := by
          have h1 : «end».val = i.val - 1 := end_post
          have h2 : i.val = start.val + len.val := i_post
          omega
        have hendn : «end».val < n.val := by omega
        have hend1 : 1 ≤ «end».val := by omega
        have hendm : «end».val - 1 < n.val := by omega
        step
        step
        by_cases h12 : i1 = i2
        · rw [if_pos h12]
          by_cases h2 : len = 2#usize
          · rw [if_pos h2]
            step*
            obtain ⟨v, back⟩ := x
            have hv_dp : v = (↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega) := x_post
            have hback : back = dp.set start := x_post1
            have hvlen : v.val.length = n.val := by
              rw [hv_dp]; exact rowLen_getElem (by have := hmat.1; omega) hrowlen
            step*
            obtain ⟨_, back1⟩ := x
            have hback1 : back1 = v.set «end» := x_post1
            step*
            rw [hback, hback1, hv_dp]
            have hconv : ((↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega)) = dp.val[start.val]! :=
              (getElem!_eq_getElem_of_lt (by have := hmat.1; omega)).symm
            rw [hconv]
            refine cont_inv ?_ ?_ hile start1_post
            · apply MatInv_set (h := hmat)
              rw [alloc.vec.Vec.set_val_eq, List.length_set]
              exact hrowlen
            · refine CellBnd_set (hmat := hmat) (hbnd := hbnd) (s := start) (e := «end»)
                (v := 0#i64) (by have := hmat.1; omega) hend hendn hlen2 ?_
              simp
              omega
          · rw [if_neg h2]
            step as ⟨i3, hi3p⟩
            have hi3 : i3.val = start.val + 1 := hi3p
            have hi3n : i3.val < dp.val.length := by
              rw [hi3]; have := hmat.1; omega
            step as ⟨v, hvp⟩
            have hv : v = (↑dp : List (alloc.vec.Vec Std.I64))[i3.val]'
                hi3n := hvp
            have hrowi3 : (dp.val[i3.val]!).val.length = n.val := by rw [hi3]; exact hrowlen1
            have hvlen : v.val.length = n.val := by
              rw [hv]; exact rowLen_getElem hi3n hrowi3
            step as ⟨i4, hi4p⟩
            have hi4 : i4.val = «end».val - 1 := hi4p
            have hi4n : i4.val < v.val.length := by rw [hi4, hvlen]; exact hendm
            step as ⟨i5, hi5p⟩
            have hi5 : i5.val = cellVal dp i3.val i4.val :=
              cellVal_index (dp := dp) (i := i3) (row := v) (j := i4) (x := i5)
                hi3n hv hi4n hi5p
            have hi5b : i5.val ≤ (len.val : Int) - 1 := by
              have hlt : i4.val - i3.val + 1 < len.val := by rw [hi3, hi4]; omega
              have hc := hbnd i3.val i4.val (by rw [hi3]; exact hs1n)
                (by rw [hi4]; exact hendm) (Or.inl hlt)
              rw [hi5]
              omega
            step*
            obtain ⟨v1, back⟩ := x
            have hv1 : v1 = (↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega) := x_post
            have hback : back = dp.set start := x_post1
            have hv1en : «end».val < v1.val.length := by
              rw [hv1]
              rw [rowLen_getElem (by have := hmat.1; omega) hrowlen]
              exact hendn
            step*
            obtain ⟨_, back1⟩ := x
            have hback1 : back1 = v1.set «end» := x_post1
            step*
            rw [hback, hback1, hv1]
            have hconv : ((↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega)) = dp.val[start.val]! :=
              (getElem!_eq_getElem_of_lt (by have := hmat.1; omega)).symm
            rw [hconv]
            refine cont_inv ?_ ?_ hile start1_post
            · apply MatInv_set (h := hmat)
              rw [alloc.vec.Vec.set_val_eq, List.length_set]
              exact hrowlen
            · refine CellBnd_set (hmat := hmat) (hbnd := hbnd) (s := start) (e := «end»)
                (v := i5) (by have := hmat.1; omega) hend hendn hlen2 hi5b
        · rw [if_neg h12]
          step as ⟨i3, hi3p⟩
          have hi3 : i3.val = start.val + 1 := hi3p
          have hi3n : i3.val < dp.val.length := by rw [hi3]; have := hmat.1; omega
          step as ⟨v, hvp⟩
          have hv : v = (↑dp : List (alloc.vec.Vec Std.I64))[i3.val]'hi3n := hvp
          have hrowi3 : (dp.val[i3.val]!).val.length = n.val := by rw [hi3]; exact hrowlen1
          have hvlen : v.val.length = n.val := by
            rw [hv]; exact rowLen_getElem hi3n hrowi3
          have hendv : «end».val < v.val.length := by rw [hvlen]; exact hendn
          step as ⟨left, hleftp⟩
          have hleft : left.val = cellVal dp i3.val «end».val :=
            cellVal_index (dp := dp) (i := i3) (row := v) (j := «end») (x := left)
              hi3n hv hendv hleftp
          step as ⟨v1, hv1p⟩
          have hv1 : v1 = (↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
              (by have := hmat.1; omega) := hv1p
          have hv1len : v1.val.length = n.val := by
            rw [hv1]; exact rowLen_getElem (by have := hmat.1; omega) hrowlen
          step as ⟨i4, hi4p⟩
          have hi4 : i4.val = «end».val - 1 := hi4p
          have hi4n : i4.val < v1.val.length := by rw [hi4, hv1len]; exact hendm
          step as ⟨right, hrightp⟩
          have hright : right.val = cellVal dp start.val i4.val :=
            cellVal_index (dp := dp) (i := start) (row := v1) (j := i4) (x := right)
              (by have := hmat.1; omega) hv1 hi4n hrightp
          have hleftb : left.val ≤ (len.val : Int) - 2 := by
            have hlt : «end».val - i3.val + 1 < len.val := by rw [hi3]; omega
            have hc := hbnd i3.val «end».val (by rw [hi3]; exact hs1n) hendn (Or.inl hlt)
            rw [hleft]
            omega
          have hrightb : right.val ≤ (len.val : Int) - 2 := by
            have hlt : i4.val - start.val + 1 < len.val := by rw [hi4]; omega
            have hc := hbnd start.val i4.val (by have := hmat.1; omega)
              (by rw [hi4]; exact hendm) (Or.inl hlt)
            rw [hright]
            omega
          have hconv : ((↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
              (by have := hmat.1; omega)) = dp.val[start.val]! :=
            (getElem!_eq_getElem_of_lt (by have := hmat.1; omega)).symm
          by_cases hcmp : left < right
          · rw [if_pos hcmp]
            step as ⟨i5, hi5p⟩
            have hi5b : i5.val ≤ (len.val : Int) - 1 := by rw [hi5p]; omega
            step*
            obtain ⟨v2, back⟩ := x
            have hv2 : v2 = (↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega) := x_post
            have hback : back = dp.set start := x_post1
            have hv2len : v2.val.length = n.val := by
              rw [hv2]; exact rowLen_getElem (by have := hmat.1; omega) hrowlen
            have hend2 : «end».val < v2.val.length := by rw [hv2len]; exact hendn
            step*
            obtain ⟨_, back1⟩ := x
            have hback1 : back1 = v2.set «end» := x_post1
            step*
            rw [hback, hback1, hv2, hconv]
            refine cont_inv ?_ ?_ hile start1_post
            · apply MatInv_set (h := hmat)
              rw [alloc.vec.Vec.set_val_eq, List.length_set]
              exact hrowlen
            · refine CellBnd_set (hmat := hmat) (hbnd := hbnd) (s := start) (e := «end»)
                (v := i5) (by have := hmat.1; omega) hend hendn hlen2 ?_
              exact hi5b
          · rw [if_neg hcmp]
            step as ⟨i5, hi5p⟩
            have hi5b : i5.val ≤ (len.val : Int) - 1 := by rw [hi5p]; omega
            step*
            obtain ⟨v2, back⟩ := x
            have hv2 : v2 = (↑dp : List (alloc.vec.Vec Std.I64))[start.val]'
                (by have := hmat.1; omega) := x_post
            have hback : back = dp.set start := x_post1
            have hv2len : v2.val.length = n.val := by
              rw [hv2]; exact rowLen_getElem (by have := hmat.1; omega) hrowlen
            have hend2 : «end».val < v2.val.length := by rw [hv2len]; exact hendn
            step*
            obtain ⟨_, back1⟩ := x
            have hback1 : back1 = v2.set «end» := x_post1
            step*
            rw [hback, hback1, hv2, hconv]
            refine cont_inv ?_ ?_ hile start1_post
            · apply MatInv_set (h := hmat)
              rw [alloc.vec.Vec.set_val_eq, List.length_set]
              exact hrowlen
            · refine CellBnd_set (hmat := hmat) (hbnd := hbnd) (s := start) (e := «end»)
                (v := i5) (by have := hmat.1; omega) hend hendn hlen2 ?_
              exact hi5b
      · -- `¬ i ≤ n`
        have hnle : n.val < i.val := by
          have h1 : ¬ (i.val ≤ n.val) := hic
          omega
        step*
        refine ⟨hmat, ?_⟩
        intro a b ha hb hproc
        rcases hproc with h | ⟨h1, h2⟩
        · rcases Nat.lt_or_ge (b - a + 1) len.val with h' | h'
          · exact hbnd a b ha hb (Or.inl h')
          · have h3 : b - a + 1 = len.val := by omega
            refine hbnd a b ha hb (Or.inr ⟨h3, ?_⟩)
            have h4 : i.val = start.val + len.val := i_post
            omega
        · omega
    · exact ⟨hmat, hbnd, hst⟩

  /-- The outer loop of the second phase of `min_insertions`: iterating over the lengths
  `2, …, n`, it never fails and preserves the `n × n` shape of the matrix. -/
  theorem loop1_spec (s : Slice Std.U8) (n : Std.Usize) (hn : n.val ≤ 500)
      (hsn : n.val = s.val.length) (hn1 : 1 ≤ n.val)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hmat : MatInv n.val dp)
      (hrows : RowsZero n.val dp.val) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp 2#usize ⦃ dp' =>
        MatInv n.val dp' ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize =>
        n.val + 1 - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize =>
        MatInv n.val p.1 ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1 ∧
          CellBnd n.val p.1 p.2.val 0)
    · rintro ⟨dp, len⟩ ⟨hmat, hlen2, hlenle, hbnd⟩
      dsimp only at hmat hlen2 hlenle hbnd
      unfold Aegis.MinInsertions.min_insertions_loop1.body
      dsimp only
      spec_split as hc
      · have hlen : len.val ≤ n.val := by simpa using hc
        have hsl : Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len 0#usize ⦃ dp' =>
            MatInv n.val dp' ∧ CellBnd n.val dp' (len.val + 1) 0 ⦄ :=
          loop1_loop0_spec s n len hn hsn hlen2 (by omega) dp 0#usize hmat hbnd
            (by simp; omega)
        apply WP.spec_bind hsl
        rintro dp1 ⟨hmat1, hbnd1⟩
        step*
      · -- `n < len`: the loop is over
        step*
    · -- the initial invariant
      have h2 : (2#usize).val = 2 := by simp
      show MatInv n.val dp ∧ 2 ≤ (2#usize).val ∧ (2#usize).val ≤ n.val + 1 ∧
        CellBnd n.val dp (2#usize).val 0
      refine ⟨hmat, by omega, by omega, ?_⟩
      intro i j hi hj hproc
      rcases hproc with h | ⟨h1, h2'⟩
      · have hji : j - i + 1 = 1 := by omega
        rw [hji]
        have hz : cellVal dp i j = 0 := hrows i j (by rw [hmat.1]; exact hi) hj
        rw [hz]
        simp
      · omega

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
  theorem spec_2 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∃ r, Aegis.MinInsertions.min_insertions s = ok r := by
    apply spec_exists_ok (p := fun _ => True)
    have hsn : (Slice.len s).val = s.val.length := by simp
    have hn500 : (Slice.len s).val ≤ 500 := by omega
    have hn1 : 1 ≤ (Slice.len s).val := by omega
    unfold Aegis.MinInsertions.min_insertions
    dsimp only
    spec_split as hle
    · step*
    · have hgt : ¬ (Slice.len s).val ≤ 1 := by simpa using hle
      have hn2 : 2 ≤ (Slice.len s).val := by omega
      apply WP.spec_bind (loop0_spec (Slice.len s) hn500)
      rintro dp ⟨⟨hdplen, hrows⟩, hzero⟩
      apply WP.spec_bind (loop1_spec s (Slice.len s) hn500 hsn hn1 dp ⟨hdplen, hrows⟩ hzero)
      rintro dp1 hmat1
      obtain ⟨hdplen1, hrows1⟩ := hmat1
      have h00 : (0#usize).val = 0 := by simp
      have h0 : (0#usize).val < dp1.val.length := by rw [hdplen1]; omega
      step as ⟨v, hv⟩
      have hvlen : v.val.length = (Slice.len s).val := by
        rw [hv]
        exact rowLen_getElem (i := 0#usize) h0
          (hrows1 (0#usize).val (by rw [hdplen1]; omega))
      step as ⟨i, hip⟩
      have hi : i.val = (Slice.len s).val - 1 := hip
      have hiv : i.val < v.val.length := by rw [hi, hvlen]; omega
      step*

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
