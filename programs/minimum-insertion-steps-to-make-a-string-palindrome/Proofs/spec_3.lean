import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_3` (minimum-insertion-steps-to-make-a-string-palindrome).
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

  /-! ### Auxiliary notions for the bounds proof of `spec_S3` -/

  /-- The `(i, j)` entry of the DP matrix `dp`, as an integer (garbage outside the matrix). -/
  def ent (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    ((dp.val[i]!).val[j]!).val

  /-- The `j`-th entry of a DP row, as an integer (garbage outside the row). -/
  def rowEnt (row : alloc.vec.Vec I64) (j : Nat) : Int := (row.val[j]!).val

  theorem ent_set_eq {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i : Usize}
      {x : alloc.vec.Vec I64} {j : Nat} (h : i.val < dp.val.length) :
      ent (dp.set i x) i.val j = rowEnt x j := by
    simp only [ent, rowEnt, Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨h, rfl⟩]

  theorem ent_set_ne {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i : Usize}
      {x : alloc.vec.Vec I64} {i' j : Nat} (h : i' ≠ i.val) :
      ent (dp.set i x) i' j = ent dp i' j := by
    simp only [ent, Aeneas.Std.alloc.vec.Vec.set_val_eq]
    have h' : Nat.not_eq i.val i' := by omega
    rw [List.set_getElem!_ne _ _ _ _ h']

  theorem rowEnt_set_eq (row : alloc.vec.Vec I64) (j : Usize) (v : I64)
      (h : j.val < row.val.length) : rowEnt (row.set j v) j.val = v.val := by
    simp only [rowEnt, Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨h, rfl⟩]

  theorem rowEnt_set_ne (row : alloc.vec.Vec I64) (j : Usize) (v : I64) (k : Nat)
      (h : k ≠ j.val) : rowEnt (row.set j v) k = rowEnt row k := by
    simp only [rowEnt, Aeneas.Std.alloc.vec.Vec.set_val_eq]
    have h' : Nat.not_eq j.val k := by omega
    rw [List.set_getElem!_ne _ _ _ _ h']

  /-- Invariant of the DP filling loops.  `Good n dp c d` says that `dp` is an `n × n` matrix of
  nonnegative integers, that every entry `(i, j)` with `j - i < c` is bounded by `j - i`, that
  the entries of the current diagonal (`j - i = c`) whose row index is `< d` are bounded too, and
  that the main diagonal is still zero. -/
  def Good (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (c d : Nat) : Prop :=
    dp.val.length = n ∧
      (∀ i, i < n → (dp.val[i]!).val.length = n) ∧
        (∀ i j, i < n → j < n → 0 ≤ ent dp i j) ∧
          (∀ i j, i < n → j < n → i < j →
            (j - i < c ∨ (j - i = c ∧ i < d)) → ent dp i j ≤ (j - i : Int)) ∧
            (∀ i, i < n → ent dp i i = 0)

  theorem Good.rows {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d) :
      dp.val.length = n := h.1

  theorem Good.row_len {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      {i : Nat} (hi : i < n) : (dp.val[i]!).val.length = n := h.2.1 i hi

  theorem Good.nonneg {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      {i j : Nat} (hi : i < n) (hj : j < n) : 0 ≤ ent dp i j := h.2.2.1 i j hi hj

  theorem Good.bound {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      {i j : Nat} (hi : i < n) (hj : j < n) (hij : i < j) (hc : j - i < c ∨ (j - i = c ∧ i < d)) :
      ent dp i j ≤ (j - i : Int) := h.2.2.2.1 i j hi hj hij hc

  theorem Good.diag {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      {i : Nat} (hi : i < n) : ent dp i i = 0 := h.2.2.2.2 i hi

  /-- Entries `(i, j)` with `i ≤ j` and `j - i < c` are bounded by `j - i`. -/
  theorem Good.diag_bound {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      {i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≤ j) (hc : j - i < c) :
      ent dp i j ≤ (j - i : Int) := by
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact h.bound hi hj hlt (Or.inl hc)
    · have hji : i = j := by omega
      subst hji
      rw [h.diag hi]
      simp

  theorem Good.mono_c {n c c' d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)}
      (h : Good n dp c d) (hc : c' ≤ c) : Good n dp c' d :=
    ⟨h.1, h.2.1, h.2.2.1, fun i j hi hj hij hb => h.2.2.2.1 i j hi hj hij (by
      rcases hb with hb | ⟨hb, hd⟩
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge c' c with hlt | hge
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, hd⟩), h.2.2.2.2⟩

  /-- Closing one diagonal: once the entries `(i, i + c)` with `i ≥ n - c` are done, the first `c + 1`
  diagonals are complete. -/
  theorem Good.next {n c d : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (h : Good n dp c d)
      (hd : n - c ≤ d) : Good n dp (c + 1) 0 :=
    ⟨h.1, h.2.1, h.2.2.1, fun i j hi hj hij hb => h.2.2.2.1 i j hi hj hij (by
      by_cases hc : j - i < c
      · exact Or.inl hc
      · exact Or.inr ⟨by omega, by omega⟩), h.2.2.2.2⟩

  /-- The invariant holds for the initial (zero) matrix. -/
  theorem Good.of_zero (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (h1 : dp.val.length = n) (h2 : ∀ i, i < n → (dp.val[i]!).val = List.replicate n 0#i64) :
      Good n dp 1 0 := by
    refine ⟨h1, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [h2 i hi]
      exact List.length_replicate ..
    · intro i j hi hj
      have hrow := h2 i hi
      have h0 : ent dp i j = ((List.replicate n 0#i64)[j]!).val := by simp only [ent, hrow]
      rw [h0, List.getElem!_replicate _ hj]
      simp
    · intro i j hi hj hij hb
      omega
    · intro i hi
      have hrow := h2 i hi
      have h0 : ent dp i i = ((List.replicate n 0#i64)[i]!).val := by simp only [ent, hrow]
      rw [h0, List.getElem!_replicate _ hi]
      simp

  /-- The entry written by one DP update, read back. -/
  theorem ent_set2_same {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {s e : Usize} {v : I64}
      (hs : s.val < dp.val.length) (he : e.val < (dp.val[s.val]!).val.length) :
      ent (dp.set s ((dp.val[s.val]!).set e v)) s.val e.val = v.val := by
    rw [ent_set_eq hs]
    exact rowEnt_set_eq _ e v (by simpa using he)

  /-- Reading back a DP entry in the updated row, at another column. -/
  theorem ent_set2_row {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {s e : Usize} {v : I64} {j : Nat}
      (hs : s.val < dp.val.length) (hj : j ≠ e.val) :
      ent (dp.set s ((dp.val[s.val]!).set e v)) s.val j = ent dp s.val j := by
    rw [ent_set_eq hs, rowEnt_set_ne _ e v j hj]
    rfl

  /-- Reading back a DP entry in another row. -/
  theorem ent_set2_col {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {s e : Usize} {v : I64} {i j : Nat}
      (hi : i ≠ s.val) :
      ent (dp.set s ((dp.val[s.val]!).set e v)) i j = ent dp i j :=
    ent_set_ne hi

  theorem row_len_set2 {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {s e : Usize} {v : I64}
      (hs : s.val < dp.val.length) :
      ((dp.set s ((dp.val[s.val]!).set e v)).val[s.val]!).val.length =
        ((dp.val[s.val]!).val.length) := by
    simp only [Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ ⟨hs, rfl⟩]
    simp

  theorem row_len_set_ne {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {s e : Usize} {v : I64} {i : Nat}
      (hi : i ≠ s.val) :
      ((dp.set s ((dp.val[s.val]!).set e v)).val[i]!).val.length =
        ((dp.val[i]!).val.length) := by
    simp only [Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]

  /-- One DP update preserves the invariant and advances the current diagonal. -/
  theorem Good.set_entry {n c : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec I64)} (s e : Usize) (v : I64)
      (h : Good n dp c s.val) (hs : s.val < n) (hslen : s.val < dp.val.length) (hse : s.val < e.val)
      (he : e.val < (dp.val[s.val]!).val.length) (hne : e.val - s.val = c)
      (hv0 : 0 ≤ v.val) (hv : v.val ≤ (e.val - s.val : Int)) :
      Good n (dp.set s ((dp.val[s.val]!).set e v)) c (s.val + 1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Aeneas.Std.alloc.vec.Vec.set_val_eq, List.length_set]
      exact h.1
    · intro i hi
      by_cases hcase : i = s.val
      · subst hcase
        rw [row_len_set2 hslen]
        exact h.row_len hs
      · rw [row_len_set_ne hcase]
        exact h.row_len hi
    · intro i j hi hj
      by_cases hi' : i = s.val
      · subst hi'
        by_cases hj' : j = e.val
        · subst hj'
          rw [ent_set2_same hslen he]
          exact hv0
        · rw [ent_set2_row hslen hj']
          exact h.nonneg hs hj
      · rw [ent_set2_col hi']
        exact h.nonneg hi hj
    · intro i j hi hj hij hb
      by_cases hi' : i = s.val
      · subst hi'
        by_cases hj' : j = e.val
        · subst hj'
          rw [ent_set2_same hslen he]
          exact hv
        · rw [ent_set2_row hslen hj']
          rcases hb with hb | ⟨hb, hd⟩
          · exact h.bound hs hj hij (Or.inl hb)
          · exact absurd (by omega : j = e.val) hj'
      · rw [ent_set2_col hi']
        rcases hb with hb | ⟨hb, hd⟩
        · exact h.bound hi hj hij (Or.inl hb)
        · exact h.bound hi hj hij (Or.inr ⟨hb, by omega⟩)
    · intro i hi
      by_cases hi' : i = s.val
      · subst hi'
        rw [ent_set2_row hslen (by omega)]
        exact h.diag hs
      · rw [ent_set2_col hi']
        exact h.diag hi

  /-- `Good.set_entry` with the updated matrix given by an equality. -/
  theorem Good.set_entry' {n c : Nat} {dp p : alloc.vec.Vec (alloc.vec.Vec I64)} (s e : Usize)
      (row : alloc.vec.Vec I64) (v : I64)
      (h : Good n dp c s.val) (hs : s.val < n) (hslen : s.val < dp.val.length) (hse : s.val < e.val)
      (hp : p = dp.set s (row.set e v)) (hrow : row = dp.val[s.val]!)
      (he : e.val < row.val.length) (hne : e.val - s.val = c)
      (hv0 : 0 ≤ v.val) (hv : v.val ≤ (e.val - s.val : Int)) :
      Good n p c (s.val + 1) := by
    rw [hrow] at he
    rw [hp, hrow]
    exact Good.set_entry s e v h hs hslen hse he hne hv0 hv

  /-- A two-level `index_usize` read, related to `ent`. -/
  theorem ent_eq_read {dp : alloc.vec.Vec (alloc.vec.Vec I64)} {i : Usize}
      (hi : i.val < dp.val.length) {v : alloc.vec.Vec I64} (hv : v = (↑dp)[↑i]) {j : Usize}
      (hj : j.val < v.val.length) {x : I64} (hx : x = (↑v)[↑j]) :
      x.val = ent dp i.val j.val := by
    have hrow : (↑dp)[↑i] = dp.val[i.val]! := List.Inhabited_getElem_eq_getElem! dp.val i.val hi
    have hv' : v = dp.val[i.val]! := hv.trans hrow
    subst hv'
    have hx' : x = ((dp.val[i.val]!).val[j.val]!) := by
      rw [hx]
      exact List.Inhabited_getElem_eq_getElem! _ j.val hj
    rw [hx']
    rfl

  /-- `min_insertions_loop0_loop0` builds a row of `n` zeros. -/
  @[step]
  theorem loop0_loop0_spec (n : Usize) (row : alloc.vec.Vec I64) (j : Usize)
      (hj : j.val ≤ n.val) (hn : n.val ≤ 500)
      (hrow : row.val = List.replicate j.val 0#i64) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ r =>
        r.val = List.replicate n.val 0#i64 ⦄ := by
    apply loop.spec_decr_nat (fun p : alloc.vec.Vec I64 × Usize => n.val - p.2.val)
      (fun p : alloc.vec.Vec I64 × Usize =>
        p.1.val = List.replicate p.2.val 0#i64 ∧ p.2.val ≤ n.val)
      (fun (r : alloc.vec.Vec I64) => r.val = List.replicate n.val 0#i64)
      (x := (row, j))
    · rintro ⟨row, j⟩ ⟨hrow, hj⟩
      simp only [uncurry]
      dsimp only at hrow hj
      unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
      split
      · rename_i hlt
        have hltj : j.val < n.val := by simpa using hlt
        step as ⟨ row1, hrow1 ⟩
        step as ⟨ j1, hj1 ⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hrow1, hrow, hj1, List.replicate_succ']
        · omega
        · omega
      · rename_i hge
        simp only [WP.spec_ok]
        have hge' : j.val = n.val := by
          have h : ¬ (j.val < n.val) := by simpa using hge
          omega
        rw [hrow, hge']
    · exact ⟨hrow, hj⟩

  /-- `min_insertions_loop1_loop0` fills one diagonal. -/
  @[step]
  theorem loop1_loop0_spec (s : Slice U8) (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (len start : Usize)
      (hsn : s.val.length = n.val) (hn : n.val ≤ 500) (hlen2 : 2 ≤ len.val)
      (hlen : len.val ≤ n.val) (hstart0 : start.val ≤ n.val)
      (hinv : Good n.val dp (len.val - 1) start.val) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start ⦃ r =>
        Good n.val r len.val 0 ⦄ := by
    apply loop.spec_decr_nat (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        Good n.val p.1 (len.val - 1) p.2.val ∧ p.2.val ≤ n.val)
      (post := fun (r : alloc.vec.Vec (alloc.vec.Vec I64)) => Good n.val r len.val 0)
      (x := (dp, start))
    · rintro ⟨dp, start⟩ ⟨hinv, hstart⟩
      simp only [uncurry]
      dsimp only at hinv hstart
      unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
      step as ⟨ i, hi ⟩
      split
      · rename_i hile
        have hilev : start.val + len.val ≤ n.val := by
          have h : i.val ≤ n.val := by simpa using hile
          omega
        have hs : start.val < n.val := by omega
        have hslen : start.val < dp.val.length := by rw [hinv.rows]; omega
        step as ⟨ e, he ⟩
        step as ⟨ i1, hi1 ⟩
        step as ⟨ i2, hi2 ⟩
        split
        · rename_i heq
          split
          · rename_i h2'
            have hne : e.val - start.val = len.val - 1 := by omega
            step as ⟨ p, hp1, hp2 ⟩
            obtain ⟨v, back⟩ := p
            dsimp only at hp1 hp2 ⊢
            have hv : v = dp.val[start.val]! :=
              hp1.trans (List.Inhabited_getElem_eq_getElem! dp.val start.val hslen)
            step as ⟨ q, hq1, hq2 ⟩ by (rw [hv, hinv.row_len hs]; omega)
            obtain ⟨x, back1⟩ := q
            dsimp only at hq1 hq2 ⊢
            step as ⟨ start1, hstart1 ⟩
            refine ⟨?_, ?_, ?_⟩
            · rw [hstart1]
              have hp : back (back1 0#i64) = dp.set start ((dp.val[start.val]!).set e 0#i64) := by
                rw [hp2, hq2]
                exact congrArg (fun r => dp.set start (r.set e 0#i64)) hv
              exact Good.set_entry' start e (dp.val[start.val]!) 0#i64 hinv hs hslen
                (by omega) hp rfl
                (by rw [hinv.row_len hs]; omega) hne (by simp) (by
                  have h0 : ((0#i64).val : Int) = 0 := by simp
                  rw [h0]
                  have h2 : start.val ≤ e.val := by omega
                  rw [← Nat.cast_sub h2, hne]
                  simp)
            · omega
            · omega
          · rename_i h2''
            have hlen3 : 3 ≤ len.val := by
              have h : ¬ (len.val = 2) := by simpa using h2''
              omega
            have hne : e.val - start.val = len.val - 1 := by omega
            step as ⟨ i3, hi3 ⟩
            step as ⟨ v2, hv2 ⟩ by (rw [hinv.rows]; omega)
            have hv2' : v2 = dp.val[i3.val]! :=
              hv2.trans (List.Inhabited_getElem_eq_getElem! dp.val i3.val (by rw [hinv.rows]; omega))
            step as ⟨ i4, hi4 ⟩
            step as ⟨ i5, hi5 ⟩ by (rw [hv2', hinv.row_len (by omega)]; omega)
            step as ⟨ p, hp1, hp2 ⟩
            obtain ⟨v1, back⟩ := p
            dsimp only at hp1 hp2 ⊢
            have hv1' : v1 = dp.val[start.val]! :=
              hp1.trans (List.Inhabited_getElem_eq_getElem! dp.val start.val hslen)
            step as ⟨ q, hq1, hq2 ⟩ by (rw [hv1', hinv.row_len hs]; omega)
            obtain ⟨x, back1⟩ := q
            dsimp only at hq1 hq2 ⊢
            step as ⟨ start1, hstart1 ⟩
            have hval : i5.val = ent dp (start.val + 1) (e.val - 1) := by
              have h := ent_eq_read (dp := dp) (i := i3) (hi := by rw [hinv.rows]; omega)
                (v := v2) (hv := hv2) (j := i4) (hj := by rw [hv2', hinv.row_len (by omega)]; omega)
                (x := i5) (hx := hi5)
              rw [hi3, hi4] at h
              exact h
            refine ⟨?_, ?_, ?_⟩
            · rw [hstart1]
              have hp : back (back1 i5) = dp.set start ((dp.val[start.val]!).set e i5) := by
                rw [hp2, hq2]
                exact congrArg (fun r => dp.set start (r.set e i5)) hv1'
              refine Good.set_entry' start e (dp.val[start.val]!) i5 hinv hs hslen (by omega) hp rfl
                (by rw [hinv.row_len hs]; omega) hne ?_ ?_
              · rw [hval]
                exact hinv.nonneg (by omega) (by omega)
              · rw [hval]
                have h3 := hinv.diag_bound (i := start.val + 1) (j := e.val - 1)
                  (by omega) (by omega) (by omega) (by omega)
                omega
            · omega
            · omega
        · rename_i hne
          have hne' : e.val - start.val = len.val - 1 := by omega
          step as ⟨ i3, hi3 ⟩
          step as ⟨ v2, hv2 ⟩ by (rw [hinv.rows]; omega)
          have hv2' : v2 = dp.val[i3.val]! :=
            hv2.trans (List.Inhabited_getElem_eq_getElem! dp.val i3.val (by rw [hinv.rows]; omega))
          step as ⟨ lf, hlf ⟩ by (rw [hv2', hinv.row_len (by omega)]; omega)
          step as ⟨ v1, hv1 ⟩
          step as ⟨ i4, hi4 ⟩
          have hv1' : v1 = dp.val[start.val]! :=
            hv1.trans (List.Inhabited_getElem_eq_getElem! dp.val start.val hslen)
          step as ⟨ rt, hrt ⟩ by (rw [hv1', hinv.row_len hs]; omega)
          have hlfv : lf.val = ent dp (start.val + 1) e.val := by
            have h := ent_eq_read (dp := dp) (i := i3) (hi := by rw [hinv.rows]; omega)
              (v := v2) (hv := hv2) (j := e) (hj := by rw [hv2', hinv.row_len (by omega)]; omega)
              (x := lf) (hx := hlf)
            rw [hi3] at h
            exact h
          have hrtv : rt.val = ent dp start.val (e.val - 1) := by
            have h := ent_eq_read (dp := dp) (i := start) (hi := hslen)
              (v := v1) (hv := hv1) (j := i4) (hj := by rw [hv1', hinv.row_len hs]; omega)
              (x := rt) (hx := hrt)
            rw [hi4] at h
            exact h
          split
          · rename_i hlt
            step as ⟨ i5, hi5 ⟩
            step as ⟨ p, hp1, hp2 ⟩
            obtain ⟨v3, back⟩ := p
            dsimp only at hp1 hp2 ⊢
            have hv3' : v3 = dp.val[start.val]! :=
              hp1.trans (List.Inhabited_getElem_eq_getElem! dp.val start.val hslen)
            step as ⟨ q, hq1, hq2 ⟩ by (rw [hv3', hinv.row_len hs]; omega)
            obtain ⟨x, back1⟩ := q
            dsimp only at hq1 hq2 ⊢
            step as ⟨ start1, hstart1 ⟩
            refine ⟨?_, ?_, ?_⟩
            · rw [hstart1]
              have hp : back (back1 i5) = dp.set start ((dp.val[start.val]!).set e i5) := by
                rw [hp2, hq2]
                exact congrArg (fun r => dp.set start (r.set e i5)) hv3'
              refine Good.set_entry' start e (dp.val[start.val]!) i5 hinv hs hslen (by omega) hp rfl
                (by rw [hinv.row_len hs]; omega) hne' ?_ ?_
              · have h0 : (0 : Int) ≤ lf.val := by
                  rw [hlfv]
                  exact hinv.nonneg (by omega) (by omega)
                omega
              · have h3 := hinv.diag_bound (i := start.val + 1) (j := e.val)
                  (by omega) (by omega) (by omega) (by omega)
                omega
            · omega
            · omega
          · rename_i hge
            step as ⟨ i5, hi5 ⟩
            step as ⟨ p, hp1, hp2 ⟩
            obtain ⟨v3, back⟩ := p
            dsimp only at hp1 hp2 ⊢
            have hv3' : v3 = dp.val[start.val]! :=
              hp1.trans (List.Inhabited_getElem_eq_getElem! dp.val start.val hslen)
            step as ⟨ q, hq1, hq2 ⟩ by (rw [hv3', hinv.row_len hs]; omega)
            obtain ⟨x, back1⟩ := q
            dsimp only at hq1 hq2 ⊢
            step as ⟨ start1, hstart1 ⟩
            refine ⟨?_, ?_, ?_⟩
            · rw [hstart1]
              have hp : back (back1 i5) = dp.set start ((dp.val[start.val]!).set e i5) := by
                rw [hp2, hq2]
                exact congrArg (fun r => dp.set start (r.set e i5)) hv3'
              refine Good.set_entry' start e (dp.val[start.val]!) i5 hinv hs hslen (by omega) hp rfl
                (by rw [hinv.row_len hs]; omega) hne' ?_ ?_
              · have h0 : (0 : Int) ≤ rt.val := by
                  rw [hrtv]
                  exact hinv.nonneg (by omega) (by omega)
                omega
              · have h3 := hinv.diag_bound (i := start.val) (j := e.val - 1)
                  (by omega) (by omega) (by omega) (by omega)
                omega
            · omega
            · omega
      · rename_i hgt
        simp only [WP.spec_ok]
        have hgt' : n.val < start.val + len.val := by
          have h : ¬ (i.val ≤ n.val) := by simpa using hgt
          omega
        have hd : n.val - (len.val - 1) ≤ start.val := by omega
        have hc : len.val - 1 + 1 = len.val := by omega
        rw [← hc]
        exact Good.next hinv hd
    · exact ⟨hinv, hstart0⟩

  /-- `min_insertions_loop1` fills the DP table diagonal by diagonal. -/
  theorem loop1_spec (s : Slice U8) (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64))
      (len : Usize)
      (hsn : s.val.length = n.val) (hn : n.val ≤ 500) (hlen2 : 2 ≤ len.val)
      (hlen : len.val ≤ n.val) (hinv : Good n.val dp (len.val - 1) 0) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp len ⦃ r => Good n.val r n.val 0 ⦄ := by
    apply loop.spec_decr_nat (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        n.val + 1 - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1 ∧ Good n.val p.1 (p.2.val - 1) 0)
      (post := fun (r : alloc.vec.Vec (alloc.vec.Vec I64)) => Good n.val r n.val 0)
      (x := (dp, len))
    · rintro ⟨dp, len⟩ ⟨h2, hle, hinv⟩
      simp only [uncurry]
      dsimp only at h2 hle hinv
      unfold Aegis.MinInsertions.min_insertions_loop1.body
      split
      · rename_i hlt
        have hlt' : len.val ≤ n.val := by simpa using hlt
        step as ⟨ dp1, hdp1 ⟩
        step as ⟨ len1, hlen1 ⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hlen1]
          have hsub : len.val + 1 - 1 = len.val := by omega
          rw [hsub]
          exact hdp1
        · omega
      · rename_i hge
        simp only [WP.spec_ok]
        have hge' : len.val = n.val + 1 := by
          have h : ¬ (len.val ≤ n.val) := by simpa using hge
          omega
        rw [hge'] at hinv
        rwa [Nat.add_sub_cancel] at hinv
    · exact ⟨hlen2, Nat.le_succ_of_le hlen, hinv⟩

  /-- `min_insertions_loop0` builds the `n × n` matrix of zeros. -/
  @[step]
  theorem loop0_spec (n : Usize) (dp : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Usize)
      (hn : n.val ≤ 500) (hi : i.val ≤ n.val)
      (hlen : dp.val.length = i.val)
      (hrows : ∀ k, k < i.val → (dp.val[k]!).val = List.replicate n.val 0#i64) :
      Aegis.MinInsertions.min_insertions_loop0 n dp i ⦃ r =>
        r.val.length = n.val ∧ ∀ k, k < n.val → (r.val[k]!).val = List.replicate n.val 0#i64 ⦄ := by
    apply loop.spec_decr_nat (measure := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec I64) × Usize =>
        p.1.val.length = p.2.val ∧
          (∀ k, k < p.2.val → (p.1.val[k]!).val = List.replicate n.val 0#i64) ∧
            p.2.val ≤ n.val)
      (post := fun (r : alloc.vec.Vec (alloc.vec.Vec I64)) =>
        r.val.length = n.val ∧ ∀ k, k < n.val → (r.val[k]!).val = List.replicate n.val 0#i64)
      (x := (dp, i))
    · rintro ⟨dp, i⟩ ⟨hlen, hrows, hi⟩
      simp only [uncurry]
      dsimp only at hlen hrows hi
      unfold Aegis.MinInsertions.min_insertions_loop0.body
      split
      · rename_i hlt
        have hlt' : i.val < n.val := by simpa using hlt
        step as ⟨ row, hrow ⟩
        · simp
        · step as ⟨ dp1, hpush ⟩
          step as ⟨ i1, hi1 ⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hpush]
            simp [hi1, hlen]
          · intro k hk
            rw [hpush]
            by_cases hk' : k < i.val
            · rw [List.getElem!_append_left _ _ _ (by rw [hlen]; exact hk'), hrows k hk']
            · have hk'' : k = i.val := by omega
              subst hk''
              rw [List.getElem!_append_right _ _ _ (by rw [hlen]), hlen, Nat.sub_self]
              simpa using hrow
          · rw [hi1]
            omega
          · rw [hi1]
            omega
      · rename_i hge
        simp only [WP.spec_ok]
        have hge' : i.val = n.val := by
          have h : ¬ (i.val < n.val) := by simpa using hge
          omega
        refine ⟨by rw [hlen, hge'], ?_⟩
        intro k hk
        exact hrows k (by omega)
    · exact ⟨hlen, hrows, hi⟩

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
  theorem spec_3 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 := by
    have key : Aegis.MinInsertions.min_insertions s ⦃ r =>
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 ⦄ := by
      unfold Aegis.MinInsertions.min_insertions
      dsimp only
      split
      · rename_i hsmall
        have hs1 : s.val.length = 1 := by
          have h : (Slice.len s).val ≤ 1 := by simpa using hsmall
          have h2 : (Slice.len s).val = s.val.length := Slice.len_val s
          omega
        simp only [WP.spec_ok]
        refine ⟨by simp, ?_⟩
        rw [hs1]
        simp
      · rename_i hbig
        have hn : 2 ≤ s.val.length := by
          have h : ¬ ((Slice.len s).val ≤ 1) := by simpa using hbig
          have h2 : (Slice.len s).val = s.val.length := Slice.len_val s
          omega
        have hsn : s.val.length = (Slice.len s).val := (Slice.len_val s).symm
        step as ⟨ dp, hlen, hrows ⟩
        have hgood : Good (Slice.len s).val dp 1 0 := Good.of_zero _ dp hlen hrows
        have hinit : Good (Slice.len s).val dp ((2#usize).val - 1) 0 := by
          simpa using hgood
        step with loop1_spec as ⟨ dp1, hdp1 ⟩
        step as ⟨ v, hv ⟩
        step as ⟨ i, hi ⟩
        have hv' : v = dp1.val[0]! :=
          hv.trans (List.Inhabited_getElem_eq_getElem! dp1.val 0 (by rw [hdp1.rows]; omega))
        step as ⟨ r, hr ⟩
        have hj0 : i.val < v.val.length := by
          have h1 : v.val.length = (Slice.len s).val := by
            rw [hv']
            exact hdp1.row_len (i := 0) (by omega)
          omega
        have hent : r.val = ent dp1 0 ((Slice.len s).val - 1) := by
          have hi0 : (0#usize).val < dp1.val.length := by
            rw [hdp1.rows]
            have h0 : (0#usize).val = 0 := by simp
            rw [h0]
            omega
          have h := ent_eq_read (dp := dp1) (i := (0#usize)) (hi := hi0)
            (v := v) (hv := hv) (j := i) (hj := hj0)
            (x := r) (hx := hr)
          rw [hi] at h
          exact h
        refine ⟨?_, ?_⟩
        · rw [hent]
          exact hdp1.nonneg (by omega) (by omega)
        · rw [hent]
          have hb := hdp1.bound (i := 0) (j := (Slice.len s).val - 1) (by omega) (by omega)
            (by omega) (Or.inl (by omega))
          omega
    intro r hr
    simpa [hr] using key

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
