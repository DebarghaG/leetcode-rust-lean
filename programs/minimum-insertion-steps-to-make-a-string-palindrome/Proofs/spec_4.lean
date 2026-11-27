import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_4` (minimum-insertion-steps-to-make-a-string-palindrome).
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

  /-! ### Auxiliary development for `spec_S4` -/

  open WP

  /-- `l[i..j]` (both ends included, `getElem?` style) is a palindrome. -/
  def palRange (l : List U8) (i j : Nat) : Prop :=
    ∀ k, k ≤ j - i → l[i + k]? = l[j - k]?

  theorem palRange_self (l : List U8) (i : Nat) : palRange l i i := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp

  theorem palRange_succ_iff {l : List U8} {i : Nat} :
      palRange l i (i + 1) ↔ l[i]? = l[i + 1]? := by
    constructor
    · intro h
      have := h 0 (by omega)
      simpa using this
    · intro h k hk
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simpa using h
      · simpa using h.symm

  theorem palRange_inner {l : List U8} {i j : Nat} (hij : i < j) (heq : l[i]? = l[j]?) :
      palRange l i j ↔ palRange l (i + 1) (j - 1) := by
    constructor
    · intro h k hk
      have hk' : k + 1 ≤ j - i := by omega
      have h' := h (k + 1) hk'
      rw [show i + (k + 1) = (i + 1) + k by omega,
        show j - (k + 1) = (j - 1) - k by omega] at h'
      exact h'
    · intro h k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using heq
      · by_cases hkmax : k = j - i
        · have h1 : i + k = j := by omega
          have h2 : j - k = i := by omega
          rw [h1, h2]
          exact heq.symm
        · have h' := h (k - 1) (by omega)
          rw [show (i + 1) + (k - 1) = i + k by omega,
            show (j - 1) - (k - 1) = j - k by omega] at h'
          exact h'

  theorem palRange_false {l : List U8} {i j : Nat} (hij : i < j) (hne : l[i]? ≠ l[j]?) :
      ¬ palRange l i j := by
    intro h
    apply hne
    have h' := h 0 (by omega)
    simpa using h'

  theorem isPalindrome_iff_palRange (l : List U8) (hne : 1 ≤ l.length) :
      isPalindrome l ↔ palRange l 0 (l.length - 1) := by
    constructor
    · intro h k hk
      have hk1 : k < l.length := by omega
      have h' : l[k] = l[l.length - 1 - k] := h k hk1
      simp only [Nat.zero_add]
      rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem (by omega)]
      simp only [Option.some.injEq]
      exact h'
    · intro h j hj
      have h' : l[0 + j]? = l[l.length - 1 - j]? := h j (by omega)
      simp only [Nat.zero_add] at h'
      rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by omega)] at h'
      simp only [Option.some.injEq] at h'
      exact h'

  theorem isPalindrome_of_length_le_one (l : List U8) (h : l.length ≤ 1) : isPalindrome l := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have h1 : l.length = 1 := by omega
    simp [h1]

  /-- The DP table type. -/
  abbrev DpT := alloc.vec.Vec (alloc.vec.Vec Std.I64)

  /-- Entry `j` of a DP row, `0` outside of the row. -/
  def entRow (row : alloc.vec.Vec Std.I64) (j : Nat) : Int :=
    ((row.val[j]?).map (fun x => x.val)).getD 0

  /-- Entry `(i, j)` of the DP table, `0` outside of the table. -/
  def ent (dp : DpT) (i j : Nat) : Int :=
    ((dp.val[i]?).map (fun row => entRow row j)).getD 0

  /-- A DP table with `n` rows of length `n`. -/
  def Tab (dp : DpT) (n : Nat) : Prop :=
    dp.val.length = n ∧ ∀ a, a < n → ∃ row, dp.val[a]? = some row ∧ row.val.length = n

  /-- Every entry of `s[i..j]` (with `j - i + 1 ≤ L`) of the table is non-negative and vanishes
  exactly when `s[i..j]` is a palindrome. -/
  def ValInv (s : Slice U8) (n L : Nat) (dp : DpT) : Prop :=
    ∀ i j, i ≤ j → j < n → j - i + 1 ≤ L →
      0 ≤ ent dp i j ∧ ent dp i j ≤ (j - i : Int) ∧
        (ent dp i j = 0 ↔ palRange s.val i j)

  theorem ent_of_getElem? (dp : DpT) {i : Nat} {row : alloc.vec.Vec Std.I64}
      (h : dp.val[i]? = some row) (j : Nat) : ent dp i j = entRow row j := by
    simp [ent, h]

  theorem entRow_of_some (row : alloc.vec.Vec Std.I64) {j : Nat} {x : Std.I64}
      (hx : row.val[j]? = some x) : entRow row j = x.val := by
    simp [entRow, hx]

  theorem ent_of_some (dp : DpT) {i j : Nat} {row : alloc.vec.Vec Std.I64} {x : Std.I64}
      (h : dp.val[i]? = some row) (hx : row.val[j]? = some x) : ent dp i j = x.val := by
    rw [ent_of_getElem? dp h j, entRow_of_some row hx]

  theorem ent_set (dp : DpT) (i : Usize) (row : alloc.vec.Vec Std.I64) (a b : Nat)
      (hlt : i.val < dp.val.length) :
      ent (dp.set i row) a b = if a = i.val then entRow row b else ent dp a b := by
    unfold ent
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases ha : a = i.val
    · subst ha
      simp [hlt]
    · rw [if_neg (by omega : i.val ≠ a), if_neg (by omega : a ≠ i.val)]

  theorem entRow_set (row : alloc.vec.Vec Std.I64) (j : Usize) (v : Std.I64) (b : Nat)
      (hb : j.val < row.val.length) :
      entRow (row.set j v) b = if b = j.val then v.val else entRow row b := by
    unfold entRow
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases hbj : b = j.val
    · subst hbj
      simp [hb]
    · simp [hbj, show j.val ≠ b by omega]

  /-- Reading entry `(i, j)` after writing `v` at `(a, b)`. -/
  theorem ent_set2 (dp : DpT) (a b : Usize) (v : Std.I64) (i j : Nat)
      {row : alloc.vec.Vec Std.I64}
      (hrow : dp.val[a.val]? = some row) (hb : b.val < row.val.length) :
      ent (dp.set a (row.set b v)) i j
        = if i = a.val then (if j = b.val then v.val else ent dp a.val j) else ent dp i j := by
    have hlt : a.val < dp.val.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hrow
      exact absurd hrow (by simp)
    rw [ent_set dp a (row.set b v) i j hlt]
    by_cases hi : i = a.val
    · subst hi
      simp only [if_true]
      rw [entRow_set row b v j hb]
      by_cases hj : j = b.val
      · simp [hj]
      · simp [hj, ent_of_getElem? dp hrow j]
    · simp [hi]

  /-- A row of `n` zeros. -/
  def zrow (n : Nat) : alloc.vec.Vec Std.I64 :=
    alloc.vec.Vec.from (List.replicate (min n Usize.max) 0#i64) (by simp)

  theorem zrow_val (n : Nat) (h : n ≤ Usize.max) : (zrow n).val = List.replicate n 0#i64 := by
    simp [zrow, Nat.min_eq_left h]

  @[step]
  theorem loop0_loop0_spec (n : Usize) (row : alloc.vec.Vec Std.I64) (j : Usize)
      (hj : j.val ≤ n.val) (hn : n.val ≤ 500) (hrow : row.val.length ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j ⦃ row' =>
        row'.val = row.val ++ List.replicate (n.val - j.val) 0#i64 ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0
    apply loop.spec_decr_nat
      (fun p : alloc.vec.Vec Std.I64 × Usize => n.val - p.2.val)
      (fun p : alloc.vec.Vec Std.I64 × Usize =>
        j.val ≤ p.2.val ∧ p.2.val ≤ n.val ∧
          p.1.val = row.val ++ List.replicate (p.2.val - j.val) 0#i64)
    · rintro ⟨r, k⟩ ⟨hjk, hkn, hval⟩
      dsimp only at hjk hkn hval
      dsimp only
      unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
      split
      · rename_i hlt
        step as ⟨r1, hr1⟩
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [hr1, hval, show k1.val - j.val = k.val - j.val + 1 by omega, List.replicate_succ']
        simp [List.append_assoc]
      · rename_i hlt
        simp only [WP.spec_ok]
        rw [hval]
        have hnk : n.val ≤ k.val := Nat.le_of_not_lt hlt
        have h1 : k.val = n.val := by omega
        rw [h1]
    · dsimp only
      refine ⟨by omega, hj, ?_⟩
      simp

  /-- After `loop0`, the table has `n` rows of `n` zeros. -/
  @[step]
  theorem loop0_spec (n : Usize) (dp : DpT) (i : Usize)
      (hi : i.val ≤ n.val) (hn : n.val ≤ 500) (hdp : dp.val.length ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n dp i ⦃ dp' =>
        dp'.val = dp.val ++ List.replicate (n.val - i.val) (zrow n.val) ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0
    apply loop.spec_decr_nat
      (fun p : DpT × Usize => n.val - p.2.val)
      (fun p : DpT × Usize =>
        i.val ≤ p.2.val ∧ p.2.val ≤ n.val ∧
          p.1.val = dp.val ++ List.replicate (p.2.val - i.val) (zrow n.val))
      (fun dp' : DpT => dp'.val = dp.val ++ List.replicate (n.val - i.val) (zrow n.val))
    · rintro ⟨d, k⟩ ⟨hik, hkn, hval⟩
      dsimp only at hik hkn hval
      dsimp only
      unfold Aegis.MinInsertions.min_insertions_loop0.body
      split
      · rename_i hlt
        step as ⟨row, hrow⟩
        step as ⟨d1, hd1⟩
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have hzrow : row = zrow n.val := by
          apply alloc.vec.Vec.ext
          rw [hrow, zrow_val n.val (by scalar_tac)]
          simp
        rw [hd1, hval, hzrow,
          show k1.val - i.val = k.val - i.val + 1 by scalar_tac, List.replicate_succ']
        simp [List.append_assoc]
      · rename_i hlt
        simp only [WP.spec_ok]
        rw [hval]
        have hnk : n.val ≤ k.val := Nat.le_of_not_lt hlt
        have h1 : k.val = n.val := by omega
        rw [h1]
    · dsimp only
      refine ⟨by omega, hi, ?_⟩
      simp

  /-- Loop invariant of the inner DP loop (over `start`) while computing length `ln`. -/
  def MidInv (s : Slice U8) (n ln st : Nat) (dp : DpT) : Prop :=
    Tab dp n ∧ ValInv s n (ln - 1) dp ∧
      ∀ i j, i ≤ j → j < n → j - i + 1 = ln → i < st →
        0 ≤ ent dp i j ∧ ent dp i j ≤ (j - i : Int) ∧
          (ent dp i j = 0 ↔ palRange s.val i j)

  /-- If the only entry that changed is `(st, en)` and it now carries a value which is non-negative
  and vanishes exactly when `s[st..en]` is a palindrome, then the loop invariant advances by one. -/
  theorem mid_step (s : Slice U8) {n ln st en : Nat} {dp dp' : DpT} {v : Int}
      (hTab' : Tab dp' n)
      (hent : ∀ i j, ent dp' i j = if i = st then (if j = en then v else ent dp st j) else ent dp i j)
      (hMid : MidInv s n ln st dp)
      (hstn : st + 1 ≤ n)
      (hen : en = st + ln - 1)
      (hln : 2 ≤ ln)
      (hval : 0 ≤ v ∧ v ≤ (en - st : Int) ∧ (v = 0 ↔ palRange s.val st en)) :
      MidInv s n ln (st + 1) dp' := by
    obtain ⟨hTab, hVal, hCalc⟩ := hMid
    have hent' : ∀ i j, i ≠ st ∨ j ≠ en → ent dp' i j = ent dp i j := by
      rintro i j (hi | hj)
      · rw [hent i j, if_neg hi]
      · rw [hent i j]
        by_cases hi : i = st
        · subst hi
          rw [if_pos rfl, if_neg hj]
        · rw [if_neg hi]
    refine ⟨hTab', ?_, ?_⟩
    · intro i j hij hjn hlen
      have hne : i ≠ st ∨ j ≠ en := by
        by_cases hi : i = st
        · right
          intro hje
          rw [hi, hje] at hlen
          omega
        · left; exact hi
      rw [hent' i j hne]
      exact hVal i j hij hjn hlen
    · intro i j hij hjn hlen hist
      by_cases hi : i = st
      · have hje : j = en := by omega
        rw [hi, hje]
        rw [hent st en]
        simp only [if_pos rfl, if_true]
        exact hval
      · rw [hent' i j (Or.inl hi)]
        exact hCalc i j hij hjn hlen (by omega)

  /-- The inner DP loop (over the starting index `start`) for a fixed length `ln`. -/
  theorem getElem_eq_of_getElem?_eq {α : Type} {l : List α} {i j : Nat}
      (hi : i < l.length) (hj : j < l.length) (h : l[i]? = l[j]?) :
      l[i]'hi = l[j]'hj := by
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
    exact Option.some.inj h

  theorem getElem?_eq_of_getElem_eq {α : Type} {l : List α} {i j : Nat}
      (hi : i < l.length) (hj : j < l.length) (h : l[i]'hi = l[j]'hj) :
      l[i]? = l[j]? := by
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, h]

  theorem vec_set_len (row : alloc.vec.Vec Std.I64) (j : Usize) (x : Std.I64) :
      (row.set j x).val.length = row.val.length := by
    rw [alloc.vec.Vec.set_val_eq, List.length_set]

  theorem Tab.row_len {dp : DpT} {n : Nat} (h : Tab dp n) {a : Nat} (ha : a < n)
      {row : alloc.vec.Vec Std.I64} (hrow : dp.val[a]? = some row) : row.val.length = n := by
    obtain ⟨row', hrow', hlen⟩ := h.2 a ha
    have : row = row' := by
      rw [hrow] at hrow'
      exact Option.some.inj hrow'
    rw [this]; exact hlen

  theorem Tab.set {dp : DpT} {n : Nat} (h : Tab dp n) (a : Usize)
      (row : alloc.vec.Vec Std.I64) (ha : a.val < n) (hrow : row.val.length = n) :
      Tab (dp.set a row) n := by
    obtain ⟨hlen, hrows⟩ := h
    refine ⟨?_, ?_⟩
    · rw [alloc.vec.Vec.set_val_eq, List.length_set, hlen]
    · intro b hb
      rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases hba : a.val = b
      · rw [if_pos hba]
        have hlt : a.val < dp.val.length := by omega
        rw [if_pos hlt]
        exact ⟨row, rfl, hrow⟩
      · rw [if_neg hba]
        exact hrows b hb

  theorem ent_of_read {dp : DpT} {i j : Nat} {row : alloc.vec.Vec Std.I64} {x : Std.I64}
      (hrow : dp.val[i]? = some row) (hb : j < row.val.length) (hx : row.val[j]'hb = x) :
      ent dp i j = x.val := by
    rw [ent_of_getElem? dp hrow j, entRow, ← hx, List.getElem?_eq_getElem hb]
    rfl

  theorem getElem?_eq_some_of_eq_getElem {α : Type} {l : List α} {i : Nat} {x : α}
      {h : i < l.length} (he : l[i]'h = x) : l[i]? = some x := by
    rw [← he, List.getElem?_eq_getElem h]

  @[step]
  theorem loop1_loop0_spec (s : Slice U8) (n : Usize) (hn : n.val = s.val.length)
      (hn500 : n.val ≤ 500) (dp : DpT) (ln : Usize) (st : Usize)
      (hln2 : 2 ≤ ln.val) (hlnle : ln.val ≤ n.val + 1) (hst : st.val ≤ n.val)
      (hinv : MidInv s n.val ln.val st.val dp) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp ln st ⦃ dp' =>
        Tab dp' n.val ∧ ValInv s n.val ln.val dp' ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0
    apply loop.spec_decr_nat
      (fun p : DpT × Usize => n.val - p.2.val)
      (fun p : DpT × Usize => MidInv s n.val ln.val p.2.val p.1 ∧ p.2.val ≤ n.val)
      (fun dp' : DpT => Tab dp' n.val ∧ ValInv s n.val ln.val dp')
    · rintro ⟨d, k⟩ ⟨hMid, hkn⟩
      dsimp only at hMid hkn
      dsimp only
      unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
      step as ⟨i, hi⟩
      split
      · rename_i hile
        step as ⟨e, he⟩
        step as ⟨s1, hs1⟩
        step as ⟨s2, hs2⟩
        -- `end = start + len - 1`
        have hen : e.val = k.val + ln.val - 1 := by rw [he, hi]
        have hks : k.val < s.val.length := by rw [← hn]; scalar_tac
        have hes : e.val < s.val.length := by rw [← hn]; scalar_tac
        have hken : k.val < e.val := by omega
        split
        · rename_i heq
          have hs : s.val[k.val]? = s.val[e.val]? := by
            exact getElem?_eq_of_getElem_eq (by omega) (by omega) (by rw [← hs1, ← hs2]; exact heq)
          split
          · -- `len = 2`: write `0`
            rename_i hln
            have hlnv : ln.val = 2 := by
              rw [hln]; simp
            have hek : e.val = k.val + 1 := by omega
            step as ⟨w, hw, hb1⟩
            obtain ⟨wv, wb⟩ := w
            have hrowk : d.val[k.val]? = some wv := getElem?_eq_some_of_eq_getElem hw.symm
            have hlenw : wv.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowk
            step as ⟨w2, _, h2b⟩
            obtain ⟨unn, b2⟩ := w2
            have hwb : wb = alloc.vec.Vec.set d k := hb1
            have hb2 : b2 = alloc.vec.Vec.set wv e := h2b
            step as ⟨k1, hk1⟩
            rw [hwb, hb2]
            have hzero : (0#i64).val = 0 := by simp
            refine ⟨?_, by scalar_tac, by scalar_tac⟩
            rw [show k1.val = k.val + 1 from hk1]
            refine mid_step s (v := (0#i64).val) ?_ ?_ hMid (by scalar_tac) hen hln2 ⟨?_, ?_, ?_⟩
            · -- table shape
              refine Tab.set hMid.1 k (wv.set e 0#i64) (by scalar_tac) ?_
              rw [vec_set_len, hlenw]
            · -- entries
              intro a b
              exact ent_set2 d k e 0#i64 a b hrowk (by rw [hlenw]; scalar_tac)
            · rw [hzero]
            · have hbnd : (0 : Int) ≤ (e.val - k.val : Int) := by omega
              rwa [hzero]
            · rw [hzero]
              constructor
              · intro _
                have hs' : s.val[k.val]? = s.val[k.val + 1]? := by rw [← hek]; exact hs
                rw [show e.val = k.val + 1 from hek]
                exact palRange_succ_iff.mpr hs'
              · intro _; rfl
          · -- `len ≠ 2`: copy `dp[start+1][end-1]`
            rename_i hln
            have hln3 : 3 ≤ ln.val := by
              have hne : ln.val ≠ 2 := by
                intro h2
                apply hln
                apply Aeneas.Std.UScalar.eq_of_val_eq
                simpa using h2
              omega
            step as ⟨i3, hi3⟩
            step as ⟨v, hv⟩
            have hrowv : d.val[i3.val]? = some v := getElem?_eq_some_of_eq_getElem hv.symm
            have hlenv : v.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowv
            step as ⟨i4, hi4⟩
            step as ⟨i5, hi5⟩
            step as ⟨w, hw, hb1⟩
            obtain ⟨wv, wb⟩ := w
            have hrowk : d.val[k.val]? = some wv := getElem?_eq_some_of_eq_getElem hw.symm
            have hlenw : wv.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowk
            step as ⟨w2, _, h2b⟩
            obtain ⟨unn, b2⟩ := w2
            have hwb : wb = alloc.vec.Vec.set d k := hb1
            have hb2 : b2 = alloc.vec.Vec.set wv e := h2b
            step as ⟨k1, hk1⟩
            rw [hwb, hb2]
            -- the read `i5` is the table entry `(start+1, end-1)`
            have hi3v : i3.val = k.val + 1 := hi3
            have hi4v : i4.val = e.val - 1 := hi4
            have hi5e : ent d (k.val + 1) (e.val - 1) = i5.val := by
              rw [← hi3v, ← hi4v]
              exact ent_of_read hrowv (by rw [hlenv]; scalar_tac) hi5.symm
            have hVal := hMid.2.1 (k.val + 1) (e.val - 1) (by scalar_tac) (by scalar_tac) (by scalar_tac)
            refine ⟨?_, by scalar_tac, by scalar_tac⟩
            rw [show k1.val = k.val + 1 from hk1]
            refine mid_step s (v := i5.val) ?_ ?_ hMid (by scalar_tac) hen hln2 ⟨?_, ?_, ?_⟩
            · refine Tab.set hMid.1 k (wv.set e i5) (by scalar_tac) ?_
              rw [vec_set_len, hlenw]
            · intro a b
              exact ent_set2 d k e i5 a b hrowk (by rw [hlenw]; scalar_tac)
            · rw [← hi5e]; exact hVal.1
            · rw [← hi5e]; have := hVal.2.1; omega
            · rw [← hi5e, hVal.2.2]
              exact (palRange_inner hken hs).symm
        · -- unequal ends: take the minimum plus one
          rename_i hne0
          have hne : s.val[k.val]? ≠ s.val[e.val]? := by
            intro h
            apply hne0
            rw [hs1, hs2]
            exact getElem_eq_of_getElem?_eq (by omega) (by omega) h
          step as ⟨i3, hi3⟩
          step as ⟨v1, hv1⟩
          have hrow1 : d.val[i3.val]? = some v1 := getElem?_eq_some_of_eq_getElem hv1.symm
          have hlen1 : v1.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrow1
          step as ⟨left, hleft⟩
          step as ⟨v2, hv2⟩
          have hrowk0 : d.val[k.val]? = some v2 := getElem?_eq_some_of_eq_getElem hv2.symm
          have hlen2 : v2.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowk0
          step as ⟨i4, hi4⟩
          step as ⟨right, hright⟩
          have hi3v : i3.val = k.val + 1 := hi3
          have hi4v : i4.val = e.val - 1 := hi4
          have hlefte : ent d (k.val + 1) e.val = left.val := by
            rw [← hi3v]
            exact ent_of_read hrow1 (by rw [hlen1]; scalar_tac) hleft.symm
          have hrighte : ent d k.val (e.val - 1) = right.val := by
            rw [← hi4v]
            exact ent_of_read hrowk0 (by rw [hlen2]; scalar_tac) hright.symm
          have hVall := hMid.2.1 (k.val + 1) e.val (by scalar_tac) (by scalar_tac) (by scalar_tac)
          have hValr := hMid.2.1 k.val (e.val - 1) (by scalar_tac) (by scalar_tac) (by scalar_tac)
          split
          · rename_i hlt
            clear hlt
            step as ⟨i5, hi5⟩
            step as ⟨w, hw, hb1⟩
            obtain ⟨wv, wb⟩ := w
            have hrowk : d.val[k.val]? = some wv := getElem?_eq_some_of_eq_getElem hw.symm
            have hlenw : wv.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowk
            step as ⟨w2, _, h2b⟩
            obtain ⟨unn, b2⟩ := w2
            have hwb : wb = alloc.vec.Vec.set d k := hb1
            have hb2 : b2 = alloc.vec.Vec.set wv e := h2b
            step as ⟨k1, hk1⟩
            rw [hwb, hb2]
            have hi5v : i5.val = left.val + 1 := hi5
            refine ⟨?_, by scalar_tac, by scalar_tac⟩
            rw [show k1.val = k.val + 1 from hk1]
            refine mid_step s (v := i5.val) ?_ ?_ hMid (by scalar_tac) hen hln2 ⟨?_, ?_, ?_⟩
            · refine Tab.set hMid.1 k (wv.set e i5) (by scalar_tac) ?_
              rw [vec_set_len, hlenw]
            · intro a b
              exact ent_set2 d k e i5 a b hrowk (by rw [hlenw]; scalar_tac)
            · rw [hi5v, ← hlefte]; omega
            · rw [hi5v, ← hlefte]; omega
            · rw [hi5v, ← hlefte]
              constructor
              · intro h; omega
              · intro hpr; exact absurd hpr (palRange_false hken hne)
          · rename_i hlt
            clear hlt
            step as ⟨i5, hi5⟩
            step as ⟨w, hw, hb1⟩
            obtain ⟨wv, wb⟩ := w
            have hrowk : d.val[k.val]? = some wv := getElem?_eq_some_of_eq_getElem hw.symm
            have hlenw : wv.val.length = n.val := Tab.row_len hMid.1 (by scalar_tac) hrowk
            step as ⟨w2, _, h2b⟩
            obtain ⟨unn, b2⟩ := w2
            have hwb : wb = alloc.vec.Vec.set d k := hb1
            have hb2 : b2 = alloc.vec.Vec.set wv e := h2b
            step as ⟨k1, hk1⟩
            rw [hwb, hb2]
            have hi5v : i5.val = right.val + 1 := hi5
            refine ⟨?_, by scalar_tac, by scalar_tac⟩
            rw [show k1.val = k.val + 1 from hk1]
            refine mid_step s (v := i5.val) ?_ ?_ hMid (by scalar_tac) hen hln2 ⟨?_, ?_, ?_⟩
            · refine Tab.set hMid.1 k (wv.set e i5) (by scalar_tac) ?_
              rw [vec_set_len, hlenw]
            · intro a b
              exact ent_set2 d k e i5 a b hrowk (by rw [hlenw]; scalar_tac)
            · rw [hi5v, ← hrighte]; omega
            · rw [hi5v, ← hrighte]; omega
            · rw [hi5v, ← hrighte]
              constructor
              · intro h; omega
              · intro hpr; exact absurd hpr (palRange_false hken hne)
      · rename_i hile
        simp only [WP.spec_ok]
        have h1 : ¬ (i.val ≤ n.val) := hile
        refine ⟨hMid.1, ?_⟩
        intro a b hab hbn hlen
        by_cases hcase : b - a + 1 ≤ ln.val - 1
        · exact hMid.2.1 a b hab hbn hcase
        · have heq : b - a + 1 = ln.val := by omega
          refine hMid.2.2 a b hab hbn heq ?_
          omega
    · exact ⟨hinv, hst⟩

  /-- The outer DP loop (over the length `len`). -/
  @[step]
  theorem loop1_spec (s : Slice U8) (n : Usize) (hn : n.val = s.val.length)
      (hn500 : n.val ≤ 500) (dp : DpT) (ln : Usize)
      (hln2 : 2 ≤ ln.val) (hlnle : ln.val ≤ n.val + 1)
      (hTab : Tab dp n.val) (hVal : ValInv s n.val (ln.val - 1) dp) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp ln ⦃ dp' =>
        Tab dp' n.val ∧ ValInv s n.val n.val dp' ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1
    apply loop.spec_decr_nat
      (fun p : DpT × Usize => n.val + 1 - p.2.val)
      (fun p : DpT × Usize =>
        Tab p.1 n.val ∧ ValInv s n.val (p.2.val - 1) p.1 ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1)
      (fun dp' : DpT => Tab dp' n.val ∧ ValInv s n.val n.val dp')
    · rintro ⟨d, k⟩ ⟨hTab', hVal', hk2, hkle⟩
      dsimp only at hTab' hVal' hk2 hkle
      dsimp only
      unfold Aegis.MinInsertions.min_insertions_loop1.body
      split
      · rename_i hle
        have hmid : MidInv s n.val k.val 0 d :=
          ⟨hTab', hVal', by
            intro i j _ _ _ hi
            exact absurd hi (by omega)⟩
        step as ⟨d1, hd1, hd2⟩
        step as ⟨k1, hk1⟩
        refine ⟨hd1, ?_, by scalar_tac, by scalar_tac⟩
        rw [show k1.val = k.val + 1 from hk1]
        simpa using hd2
      · rename_i hle
        simp only [WP.spec_ok]
        have hk : n.val ≤ k.val := by
          have h1 : ¬ (k.val ≤ n.val) := hle
          omega
        have hkle' : k.val ≤ n.val + 1 := hkle
        have hk1 : k.val = n.val + 1 :=
          le_antisymm hkle' (Nat.succ_le_of_lt (Nat.lt_of_not_le (show ¬ (k.val ≤ n.val) from hle)))
        refine ⟨hTab', ?_⟩
        rw [hk1] at hVal'
        simpa using hVal'
    · dsimp only
      exact ⟨hTab, hVal, hln2, hlnle⟩

  theorem Tab_zeros (n : Nat) (hn : n ≤ Usize.max) (dp : DpT)
      (h : dp.val = List.replicate n (zrow n)) : Tab dp n := by
    refine ⟨by rw [h]; simp, ?_⟩
    intro a ha
    refine ⟨zrow n, ?_, ?_⟩
    · rw [h]; simp [ha]
    · rw [zrow_val n hn, List.length_replicate]

  theorem ent_zeros (n : Nat) (hn : n ≤ Usize.max) (dp : DpT)
      (h : dp.val = List.replicate n (zrow n)) {a b : Nat} (ha : a < n) :
      ent dp a b = 0 := by
    have hz : (zrow n).val = List.replicate n 0#i64 := zrow_val n hn
    have hrow : dp.val[a]? = some (zrow n) := by
      rw [h]; exact List.getElem?_replicate_of_lt ha
    rw [ent_of_getElem? dp hrow b]
    unfold entRow
    rw [hz, List.getElem?_replicate]
    by_cases hb : b < n <;> simp [hb]

  theorem ValInv_zeros (s : Slice U8) (n : Nat) (hn : n ≤ Usize.max) (dp : DpT)
      (h : dp.val = List.replicate n (zrow n)) : ValInv s n 1 dp := by
    intro i j hij hjn hlen
    have hij' : i = j := by omega
    subst hij'
    have hz : ent dp i i = 0 := ent_zeros n hn dp h (by omega)
    refine ⟨by rw [hz], by rw [hz]; omega, ?_⟩
    rw [hz]
    exact ⟨fun _ => palRange_self s.val i, fun _ => rfl⟩

  theorem min_insertions_spec (s : Slice U8) (hlen1 : 1 ≤ s.val.length)
      (hlen500 : s.val.length ≤ 500) :
      Aegis.MinInsertions.min_insertions s ⦃ r => (r.val = 0 ↔ isPalindrome s.val) ⦄ := by
    have hn : (Slice.len s).val = s.val.length := by simp
    unfold Aegis.MinInsertions.min_insertions
    dsimp only
    split
    · rename_i hle
      simp only [WP.spec_ok]
      have h1 : s.val.length ≤ 1 := by
        have h2 : (Slice.len s).val ≤ 1 := hle
        omega
      constructor
      · intro _
        exact isPalindrome_of_length_le_one s.val h1
      · intro _; rfl
    · rename_i hle
      have hn2 : 2 ≤ (Slice.len s).val := by
        have h2 : ¬ ((Slice.len s).val ≤ 1) := hle
        omega
      have hn500' : (Slice.len s).val ≤ 500 := by omega
      have hnmax : (Slice.len s).val ≤ Usize.max := by scalar_tac
      step as ⟨dp, hdp⟩
      have hdp' : dp.val = List.replicate (Slice.len s).val (zrow (Slice.len s).val) := by
        rw [hdp]
        simp
      have hTab : Tab dp (Slice.len s).val := Tab_zeros _ hnmax dp hdp'
      have hVal : ValInv s (Slice.len s).val 1 dp := ValInv_zeros s _ hnmax dp hdp'
      step as ⟨dp1, hd1, hd2⟩
      step as ⟨v, hv⟩
      have hrow : dp1.val[0]? = some v := getElem?_eq_some_of_eq_getElem hv.symm
      have hlenv : v.val.length = (Slice.len s).val := hd1.row_len (by omega) hrow
      step as ⟨i, hi⟩
      have hiv : i.val < v.val.length := by rw [hi, hlenv]; omega
      step as ⟨rr, hr⟩
      rw [isPalindrome_iff_palRange s.val hlen1]
      have hrv : v.val[i.val]? = some rr := getElem?_eq_some_of_eq_getElem hr.symm
      have hent : ent dp1 0 i.val = rr.val := ent_of_some dp1 hrow hrv
      have hVI := hd2 0 i.val (by omega) (by omega) (by omega)
      have hiff : (rr.val = 0 ↔ palRange s.val 0 i.val) := by
        rw [← hent]; exact hVI.2.2
      rw [hi] at hiff
      rw [show (Slice.len s).val - 1 = s.val.length - 1 by omega] at hiff
      exact hiff

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
  theorem spec_4 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r → (r.val = 0 ↔ isPalindrome s.val) := by
    intro r hrun
    have h := min_insertions_spec s hlen_lower hlen_upper
    rw [hrun] at h
    simpa only [WP.spec_ok] using h

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
