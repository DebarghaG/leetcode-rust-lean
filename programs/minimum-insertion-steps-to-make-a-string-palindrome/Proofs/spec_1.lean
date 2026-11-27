import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_1` (minimum-insertion-steps-to-make-a-string-palindrome).
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

/-! ### Auxiliary material for the proof of `spec_S1` -/

/-- The sub-list of `l` of length `k` starting at index `i`. -/
def subList (l : List U8) (i k : Nat) : List U8 := (l.drop i).take k

theorem subList_length (l : List U8) (i k : Nat) :
    (subList l i k).length = min k (l.length - i) := by
  simp [subList, List.length_take, List.length_drop]

theorem subList_getElem? (l : List U8) (i k j : Nat) :
    (subList l i k)[j]? = if j < k then l[i + j]? else none := by
  simp [subList, List.getElem?_take, List.getElem?_drop]

theorem subList_zero (l : List U8) (k : Nat) (h : l.length ≤ k) : subList l 0 k = l := by
  simp [subList, List.take_of_length_le, h]

theorem subList_total (l : List U8) (i : Nat) : subList l i (l.length - i) = l.drop i := by
  simp [subList, List.take_of_length_le]

theorem subList_subList (l : List U8) (i j k k' : Nat) (h : k' ≤ k - j) :
    subList (subList l i k) j k' = subList l (i + j) k' := by
  unfold subList
  rw [List.drop_take, List.drop_drop, List.take_take, min_eq_left h]

theorem take_pred_append_last (u : List U8) (hu : 0 < u.length) :
    u.take (u.length - 1) ++ [u[u.length - 1]'(by omega)] = u := by
  have hne : u ≠ [] := by intro hc; simp [hc] at hu
  have h3 : u.getLast hne = u[u.length - 1]'(by omega) := List.getLast_eq_getElem hne
  have h2 : u.dropLast ++ [u.getLast hne] = u := List.dropLast_append_getLast hne
  calc u.take (u.length - 1) ++ [u[u.length - 1]'(by omega)]
      = u.dropLast ++ [u[u.length - 1]'(by omega)] := by rw [List.dropLast_eq_take]
    _ = u.dropLast ++ [u.getLast hne] := by rw [← h3]
    _ = u := h2

/-- The list `l` with its two ends removed. -/
theorem eq_cons_subList_last (l : List U8) (h : 2 ≤ l.length) :
    l = l[0]'(by omega) :: subList l 1 (l.length - 2) ++ [l[l.length - 1]'(by omega)] := by
  match l with
  | a :: rest =>
    have hrest : 1 ≤ rest.length := by simp at h; omega
    have hdrop : List.drop 1 (a :: rest) = rest := rfl
    have hsub : subList (a :: rest) 1 ((a :: rest).length - 2) = rest.take (rest.length - 1) := by
      have h1 : (a :: rest).length - 2 = rest.length - 1 := by simp
      simp only [subList, h1, hdrop]
    have hlast : (a :: rest)[(a :: rest).length - 1]'(by simp only [List.length_cons]; omega)
        = rest[rest.length - 1]'(by omega) := by
      have e2 : (a :: rest)[(a :: rest).length - 1]? = rest[rest.length - 1]? := by
        rw [show (a :: rest).length - 1 = rest.length - 1 + 1 by simp only [List.length_cons]; omega,
          List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem (by simp only [List.length_cons]; omega),
        List.getElem?_eq_getElem (by omega)] at e2
      exact Option.some.inj e2
    rw [hsub, hlast]
    exact congrArg (fun x => a :: x) (take_pred_append_last rest (by omega)).symm

/-- The minimum number of insertions needed to turn `l` into a palindrome. -/
def midp (l : List U8) : Nat :=
  if h : l.length ≤ 1 then 0
  else if l[0]? = l[l.length - 1]? then midp (subList l 1 (l.length - 2))
  else 1 + min (midp (subList l 1 (l.length - 1))) (midp (subList l 0 (l.length - 1)))
termination_by l.length
decreasing_by
  all_goals
    simp only [subList, List.length_take, List.length_drop]
    omega

theorem subList_mid (a : U8) (mid : List U8) (b : U8) :
    subList (a :: mid ++ [b]) 1 (mid.length) = mid := by
  simp [subList, List.take_left]

theorem subList_tail (a : U8) (mid : List U8) (b : U8) :
    subList (a :: mid ++ [b]) 1 (mid.length + 1) = mid ++ [b] := by
  simp [subList]

theorem subList_dropLast (a : U8) (mid : List U8) (b : U8) :
    subList (a :: mid ++ [b]) 0 (mid.length + 1) = a :: mid := by
  simp [subList]

theorem midp_nil : midp [] = 0 := by
  rw [midp]; simp

theorem midp_single (a : U8) : midp [a] = 0 := by
  rw [midp]; simp

theorem midp_cons_last (a : U8) (mid : List U8) (b : U8) :
    midp (a :: mid ++ [b]) =
      if a = b then midp mid else 1 + min (midp (mid ++ [b])) (midp (a :: mid)) := by
  have hlen : (a :: mid ++ [b]).length = mid.length + 2 := by simp
  have h0 : (a :: mid ++ [b])[0]? = some a := by simp
  have hlast : (a :: mid ++ [b])[mid.length + 2 - 1]? = some b := by
    rw [show mid.length + 2 - 1 = mid.length + 1 by omega]
    simp
  rw [midp]
  simp only [hlen]
  rw [dif_neg (by omega), h0, hlast]
  by_cases hab : a = b
  · rw [if_pos (show some a = some b from by rw [hab]), if_pos hab]
    rw [show mid.length + 2 - 2 = mid.length by omega, subList_mid]
  · rw [if_neg (show ¬ some a = some b from by simpa using hab), if_neg hab]
    rw [show mid.length + 2 - 1 = mid.length + 1 by omega, subList_tail, subList_dropLast]

theorem isPalindrome_iff_reverse (l : List U8) : isPalindrome l ↔ l.reverse = l := by
  constructor
  · intro h
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_reverse]
      exact (h i (by simpa using h1)).symm
  · intro h i hi
    have e1 : l[i]? = l[l.length - 1 - i]? := by
      rw [← List.getElem?_reverse (l := l) (i := i) hi, h]
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at e1
    exact Option.some.inj e1

theorem isPalindrome_of_reverse {l : List U8} (h : l.reverse = l) : isPalindrome l :=
  (isPalindrome_iff_reverse l).mpr h

theorem isPalindrome_reverse {l : List U8} (h : isPalindrome l) : l.reverse = l :=
  (isPalindrome_iff_reverse l).mp h

theorem isPalindrome_of_length_le_one {l : List U8} (h : l.length ≤ 1) : isPalindrome l := by
  rw [isPalindrome_iff_reverse]
  match l with
  | [] => rfl
  | [a] => rfl
  | a :: b :: r => simp at h

theorem isPalindrome_ends {t : List U8} (h : isPalindrome t) (h2 : 2 ≤ t.length) :
    isPalindrome (subList t 1 (t.length - 2)) := by
  obtain ⟨a, u, b, ht⟩ : ∃ a u b, t = a :: u ++ [b] :=
    ⟨t[0]'(by omega), subList t 1 (t.length - 2), t[t.length - 1]'(by omega),
      eq_cons_subList_last t h2⟩
  subst ht
  have hrev : b :: (u.reverse ++ [a]) = a :: (u ++ [b]) := by
    have h' : (a :: u ++ [b]).reverse = a :: u ++ [b] := isPalindrome_reverse h
    rwa [show (a :: u ++ [b]).reverse = b :: u.reverse ++ [a] by simp] at h'
  injection hrev with hba hrest
  subst hba
  have huu : u.reverse = u := List.append_cancel_right hrest
  rw [isPalindrome_iff_reverse, show (b :: u ++ [b]).length - 2 = u.length by simp,
    subList_mid, huu]

/-! ### Specifications -/

/-- An explicit increasing embedding of `l` into `t`. -/
def IsEmb (l t : List U8) (idx : Nat → Nat) : Prop :=
  (∀ (a : Nat), a < l.length → idx a < t.length) ∧
    (∀ (a b : Nat), a < b → b < l.length → idx a < idx b) ∧
      (∀ (a : Nat), a < l.length → t[idx a]? = l[a]?)

theorem isSubsequence_iff_emb {l t : List U8} :
    isSubsequence l t ↔ ∃ idx, IsEmb l t idx := Iff.rfl

theorem IsEmb.sub {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx)
    (i k : Nat) (hlo : ∀ a, a < l.length → i ≤ idx a)
    (hhi : ∀ a, a < l.length → idx a < i + k) :
    IsEmb l (subList t i k) (fun a => idx a - i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    dsimp only
    rw [subList_length]
    have h1 := hhi a ha
    have h2 := h.1 a ha
    have h3 := hlo a ha
    exact Nat.lt_min.mpr ⟨by omega, by omega⟩
  · intro a b ha hb
    dsimp only
    have h1 := h.2.1 a b ha hb
    have ha' : a < l.length := by omega
    have h2 := hlo a ha'
    omega
  · intro a ha
    dsimp only
    rw [subList_getElem?]
    have h1 := hlo a ha
    have h2 := hhi a ha
    rw [if_pos (by omega), show i + (idx a - i) = idx a by omega]
    exact h.2.2 a ha

theorem IsEmb.ofSubListLeft {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx)
    (i k : Nat) : IsEmb (subList l i k) t (fun a => idx (a + i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    dsimp only
    rw [subList_length] at ha
    have := h.1 (a + i) (by omega)
    exact this
  · intro a b ha hb
    dsimp only
    rw [subList_length] at hb
    have h1 := h.2.1 (a + i) (b + i) (by omega) (by omega)
    exact h1
  · intro a ha
    dsimp only
    rw [subList_length] at ha
    rw [subList_getElem?, if_pos (by omega)]
    have := h.2.2 (a + i) (by omega)
    simpa [Nat.add_comm] using this

theorem IsEmb.idx_ge {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx) :
    ∀ a, a < l.length → a ≤ idx a := by
  intro a
  induction a with
  | zero => intro _; omega
  | succ n ih =>
    intro ha
    have h1 : n < l.length := by omega
    have h2 := h.2.1 n (n + 1) (by omega) ha
    have h3 := ih h1
    omega

theorem IsEmb.length_le {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx) :
    l.length ≤ t.length := by
  rcases Nat.eq_zero_or_pos l.length with h0 | h0
  · omega
  · have h1 := h.idx_ge (l.length - 1) (by omega)
    have h2 := h.1 (l.length - 1) (by omega)
    omega

theorem IsEmb.inj {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx)
    {a b : Nat} (ha : a < l.length) (hb : b < l.length) (he : idx a = idx b) : a = b := by
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · have := h.2.1 a b h' hb; omega
  · exact h'
  · have := h.2.1 b a h' ha; omega

theorem IsEmb.prefix (l v : List U8) : IsEmb l (l ++ v) id := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    show a < (l ++ v).length
    simp
    omega
  · intro a b ha hb; exact ha
  · intro a ha
    show (l ++ v)[a]? = l[a]?
    rw [List.getElem?_append, if_pos ha]

theorem IsEmb.weaken {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx) (v : List U8) :
    IsEmb l (t ++ v) idx := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha; have := h.1 a ha; simp; omega
  · intro a b ha hb; exact h.2.1 a b ha hb
  · intro a ha
    have h1 := h.1 a ha
    rw [List.getElem?_append, if_pos h1]
    exact h.2.2 a ha

theorem IsEmb.cons {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx) (x : U8) :
    IsEmb (x :: l) (x :: t) (fun a => if a = 0 then 0 else idx (a - 1) + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    dsimp only
    by_cases h0 : a = 0
    · simp [h0]
    · rw [if_neg h0]
      have h1 := h.1 (a - 1) (by simp at ha; omega)
      simp
      omega
  · intro a b ha hb
    dsimp only
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl]
      by_cases hb0 : b = 0
      · omega
      · rw [if_neg hb0]; omega
    · by_cases hb0 : b = 0
      · omega
      · rw [if_neg ha0, if_neg hb0]
        have := h.2.1 (a - 1) (b - 1) (by omega) (by simp at hb; omega)
        omega
  · intro a ha
    dsimp only
    by_cases h0 : a = 0
    · subst h0
      simp
    · rw [if_neg h0]
      have h1 : a - 1 < l.length := by simp at ha; omega
      have e : a = a - 1 + 1 := by omega
      rw [e, List.getElem?_cons_succ, List.getElem?_cons_succ]
      exact h.2.2 (a - 1) h1

theorem IsEmb.snoc {l t : List U8} {idx : Nat → Nat} (h : IsEmb l t idx) (x : U8) :
    IsEmb (l ++ [x]) (t ++ [x]) (fun a => if a < l.length then idx a else t.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    dsimp only
    by_cases h0 : a < l.length
    · rw [if_pos h0]
      have := h.1 a h0
      simp
      omega
    · rw [if_neg h0]
      simp at ha
      simp
  · intro a b ha hb
    dsimp only
    by_cases hb0 : b < l.length
    · have ha0 : a < l.length := by omega
      rw [if_pos ha0, if_pos hb0]
      exact h.2.1 a b ha hb0
    · by_cases ha0 : a < l.length
      · rw [if_pos ha0, if_neg hb0]
        have := h.1 a ha0
        omega
      · rw [if_neg ha0, if_neg hb0]
        simp at ha hb
        omega
  · intro a ha
    dsimp only
    by_cases h0 : a < l.length
    · rw [if_pos h0]
      have h1 := h.1 a h0
      show (t ++ [x])[idx a]? = (l ++ [x])[a]?
      rw [List.getElem?_append, if_pos h1, List.getElem?_append, if_pos h0]
      exact h.2.2 a h0
    · rw [if_neg h0]
      simp at ha
      have ha' : a = l.length := by omega
      subst ha'
      simp

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

  /-! ### Auxiliary material for the `mA_*` results -/

  /-- An index function that is strictly increasing below `m` dominates the identity. -/
  theorem mA_mono_idx_ge {f : Nat → Nat} {m : Nat}
      (hmono : ∀ a b, a < b → b < m → f a < f b) : ∀ a, a < m → a ≤ f a := by
    intro a
    induction a with
    | zero => intro _; omega
    | succ n ih =>
      intro ha
      have h1 : n < m := by omega
      have h2 := hmono n (n + 1) (by omega) ha
      have h3 := ih h1
      omega

  /-- A strictly increasing family of `m` indices inside `[0, n)` forces `m ≤ n`. -/
  theorem mA_idx_le {f : Nat → Nat} {m n : Nat}
      (hbound : ∀ a, a < m → f a < n)
      (hmono : ∀ a b, a < b → b < m → f a < f b) : m ≤ n := by
    rcases Nat.eq_zero_or_pos m with h | h
    · omega
    · have h1 := mA_mono_idx_ge hmono (m - 1) (by omega)
      have h2 := hbound (m - 1) (by omega)
      omega

  /-- `midp` never exceeds the length of its argument. -/
  theorem mA_midp_le_length_aux : ∀ n, ∀ l : List U8, l.length = n → midp l ≤ l.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hl
      by_cases h1 : l.length ≤ 1
      · rw [midp, dif_pos h1]
        omega
      · have h2 : 2 ≤ l.length := by omega
        obtain ⟨a, mid, b, rfl⟩ : ∃ a mid b, l = a :: mid ++ [b] :=
          ⟨l[0]'(by omega), subList l 1 (l.length - 2), l[l.length - 1]'(by omega),
            eq_cons_subList_last l h2⟩
        have hl' : mid.length + 2 = n := by
          have hh : (a :: mid ++ [b]).length = mid.length + 2 := by simp
          omega
        rw [midp_cons_last]
        have hlen : (a :: mid ++ [b]).length = mid.length + 2 := by simp
        rw [hlen]
        by_cases hab : a = b
        · rw [if_pos hab]
          have hmid := ih mid.length (by omega) mid rfl
          omega
        · rw [if_neg hab]
          have hbl : (mid ++ [b]).length = mid.length + 1 := by simp
          have htail := ih (mid ++ [b]).length (by omega) (mid ++ [b]) rfl
          omega

  theorem mA_midp_le_length (l : List U8) : midp l ≤ l.length :=
    mA_midp_le_length_aux l.length l rfl

  /-- Reading a middle entry of `a :: mid ++ [b]`. -/
  theorem mA_getElem?_mid {a b : U8} {mid : List U8} {x : Nat}
      (h1 : 1 ≤ x) (h2 : x ≤ mid.length) : (a :: mid ++ [b])[x]? = mid[x - 1]? := by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    show ((a :: mid) ++ [b])[y + 1]? = mid[y + 1 - 1]?
    rw [List.getElem?_append, if_pos (by simp only [List.length_cons]; omega),
      List.getElem?_cons_succ, Nat.add_sub_cancel]

  /-- Reading an entry of `a :: mid ++ [b]` that still lies in `a :: mid`. -/
  theorem mA_getElem?_dropLast {a b : U8} {mid : List U8} {x : Nat}
      (h : x < mid.length + 1) : (a :: mid ++ [b])[x]? = (a :: mid)[x]? := by
    have e : a :: mid ++ [b] = (a :: mid) ++ [b] := rfl
    rw [e, List.getElem?_append, if_pos (by simp only [List.length_cons]; omega)]

  /-- The entry at the last position of `a :: mid ++ [b]`. -/
  theorem mA_getElem?_last {a b : U8} {mid : List U8} :
      (a :: mid ++ [b])[mid.length + 1]? = some b := by
    have e : a :: mid ++ [b] = (a :: mid) ++ [b] := rfl
    rw [e, show mid.length + 1 = (a :: mid).length from by simp]
    exact List.getElem?_concat_length

  /-- Trimming equal ends off a palindromic subsequence. -/
  theorem mA_pss_mid_of_ends {a b : U8} {mid : List U8} {m : Nat} {i : Nat → Nat}
      (h1 : ∀ c, c < m → i c < mid.length + 2)
      (h2 : ∀ c d, c < d → d < m → i c < i d)
      (h3 : ∀ c, c < m → (a :: mid ++ [b])[i c]? = (a :: mid ++ [b])[i (m - 1 - c)]?)
      (hm : 2 ≤ m) : isPalindromicSubseqSize mid (m - 2) := by
    refine ⟨fun c => i (c + 1) - 1, ?_, ?_, ?_⟩
    · intro c hc
      have hcin : c + 1 < m := by omega
      have hcm : m - 1 < m := by omega
      have hlt : i (c + 1) < i (m - 1) := h2 (c + 1) (m - 1) (by omega) hcm
      have hlast := h1 (m - 1) hcm
      have hpos : 0 < i (c + 1) := by
        have := h2 0 (c + 1) (by omega) hcin
        omega
      show i (c + 1) - 1 < mid.length
      omega
    · intro c d hc hd
      have hc' : c + 1 < m := by omega
      have hd' : d + 1 < m := by omega
      have hlt := h2 (c + 1) (d + 1) (by omega) hd'
      have hpc : 0 < i (c + 1) := by
        have := h2 0 (c + 1) (by omega) hc'
        omega
      have hpd : 0 < i (d + 1) := by
        have := h2 0 (d + 1) (by omega) hd'
        omega
      show i (c + 1) - 1 < i (d + 1) - 1
      omega
    · intro c hc
      have hcin : c + 1 < m := by omega
      have hcm : m - 1 < m := by omega
      have hlt : i (c + 1) < i (m - 1) := h2 (c + 1) (m - 1) (by omega) hcm
      have hlast := h1 (m - 1) hcm
      have hx1 : 1 ≤ i (c + 1) := by
        have := h2 0 (c + 1) (by omega) hcin
        omega
      have hxmid : i (c + 1) ≤ mid.length := by omega
      have hyidx : m - 2 - c < m := by omega
      have hy1 : 1 ≤ i (m - 2 - c) := by
        have := h2 0 (m - 2 - c) (by omega) hyidx
        omega
      have hylt : i (m - 2 - c) < i (m - 1) := h2 (m - 2 - c) (m - 1) (by omega) hcm
      have hymid : i (m - 2 - c) ≤ mid.length := by omega
      dsimp only
      rw [show m - 2 - 1 - c + 1 = m - 2 - c by omega]
      rw [← mA_getElem?_mid hx1 hxmid, ← mA_getElem?_mid hy1 hymid]
      rw [show m - 2 - c = m - 1 - (c + 1) by omega]
      exact h3 (c + 1) hcin

  /-- A palindromic subsequence survives dropping the first byte. -/
  theorem mA_pss_drop {a b : U8} {mid : List U8} {m : Nat} {i : Nat → Nat}
      (h1 : ∀ c, c < m → i c < mid.length + 2)
      (h2 : ∀ c d, c < d → d < m → i c < i d)
      (h3 : ∀ c, c < m → (a :: mid ++ [b])[i c]? = (a :: mid ++ [b])[i (m - 1 - c)]?)
      (hpos : ∀ c, c < m → 0 < i c) : isPalindromicSubseqSize (mid ++ [b]) m := by
    refine ⟨fun c => i c - 1, ?_, ?_, ?_⟩
    · intro c hc
      have hc' := h1 c hc
      have hp := hpos c hc
      show i c - 1 < (mid ++ [b]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · intro c d hc hd
      have hlt := h2 c d hc hd
      have hpc := hpos c (by omega)
      have hpd := hpos d hd
      show i c - 1 < i d - 1
      omega
    · intro c hc
      have hcm : m - 1 - c < m := by omega
      have e1 : (mid ++ [b])[i c - 1]? = (a :: mid ++ [b])[i c]? := by
        rw [show i c = (i c - 1) + 1 by have := hpos c hc; omega]
        exact (List.getElem?_cons_succ).symm
      have e2 : (mid ++ [b])[i (m - 1 - c) - 1]? = (a :: mid ++ [b])[i (m - 1 - c)]? := by
        rw [show i (m - 1 - c) = (i (m - 1 - c) - 1) + 1 by
          have := hpos (m - 1 - c) hcm; omega]
        exact (List.getElem?_cons_succ).symm
      rw [e1, e2]
      exact h3 c hc

  /-- A palindromic subsequence survives dropping the last byte. -/
  theorem mA_pss_take {a b : U8} {mid : List U8} {m : Nat} {i : Nat → Nat}
      (h2 : ∀ c d, c < d → d < m → i c < i d)
      (h3 : ∀ c, c < m → (a :: mid ++ [b])[i c]? = (a :: mid ++ [b])[i (m - 1 - c)]?)
      (hlt : ∀ c, c < m → i c < mid.length + 1) : isPalindromicSubseqSize (a :: mid) m := by
    refine ⟨i, ?_, ?_, ?_⟩
    · intro c hc
      have h := hlt c hc
      show i c < (a :: mid).length
      simp only [List.length_cons]
      omega
    · intro c d hc hd; exact h2 c d hc hd
    · intro c hc
      have hcm : m - 1 - c < m := by omega
      have e1 : (a :: mid)[i c]? = (a :: mid ++ [b])[i c]? :=
        (mA_getElem?_dropLast (hlt c hc)).symm
      have e2 : (a :: mid)[i (m - 1 - c)]? = (a :: mid ++ [b])[i (m - 1 - c)]? :=
        (mA_getElem?_dropLast (hlt (m - 1 - c) hcm)).symm
      rw [e1, e2]
      exact h3 c hc

  /-- Any palindromic subsequence has size at most `len - midp`. -/
  theorem mA_midp_add_pss_le_aux : ∀ n, ∀ l : List U8, l.length = n →
      ∀ m, isPalindromicSubseqSize l m → midp l + m ≤ l.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hl m hpss
      obtain ⟨i, h1, h2, h3⟩ := hpss
      by_cases hsmall : l.length ≤ 1
      · have hm : m ≤ l.length := mA_idx_le h1 h2
        have hmid : midp l = 0 := by rw [midp, dif_pos hsmall]
        omega
      · have h2len : 2 ≤ l.length := by omega
        obtain ⟨a, mid, b, rfl⟩ : ∃ a mid b, l = a :: mid ++ [b] :=
          ⟨l[0]'(by omega), subList l 1 (l.length - 2), l[l.length - 1]'(by omega),
            eq_cons_subList_last l h2len⟩
        have hl' : mid.length + 2 = n := by
          have hh : (a :: mid ++ [b]).length = mid.length + 2 := by simp
          omega
        have H1 : ∀ c, c < m → i c < mid.length + 2 := by
          intro c hc
          have hh : (a :: mid ++ [b]).length = mid.length + 2 := by simp
          have := h1 c hc
          omega
        rw [midp_cons_last]
        have hlen : (a :: mid ++ [b]).length = mid.length + 2 := by simp
        rw [hlen]
        by_cases hab : a = b
        · rw [if_pos hab]
          by_cases hm1 : m ≤ 1
          · have hle := mA_midp_le_length mid
            omega
          · have hm2 : 2 ≤ m := by omega
            have hpss_mid : isPalindromicSubseqSize mid (m - 2) :=
              mA_pss_mid_of_ends H1 h2 h3 hm2
            have hrec := ih mid.length (by omega) mid rfl (m - 2) hpss_mid
            omega
        · rw [if_neg hab]
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · have hu := mA_midp_le_length (mid ++ [b])
            have hbl : (mid ++ [b]).length = mid.length + 1 := by simp
            have hmin : min (midp (mid ++ [b])) (midp (a :: mid)) ≤ midp (mid ++ [b]) :=
              min_le_left _ _
            omega
          · by_cases hi0 : i 0 = 0
            · have hlt : ∀ c, c < m → i c < mid.length + 1 := by
                intro c hc
                rcases Nat.lt_or_ge c (m - 1) with hc' | hc'
                · have hlt1 := h2 c (m - 1) hc' (by omega)
                  have hb := H1 (m - 1) (by omega)
                  omega
                · have hce : c = m - 1 := by omega
                  subst hce
                  have hle := H1 (m - 1) (by omega)
                  by_contra hcon
                  have hieq : i (m - 1) = mid.length + 1 := by omega
                  have h3z := h3 0 (by omega)
                  rw [hi0, show m - 1 - 0 = m - 1 from by omega, hieq] at h3z
                  rw [show (a :: mid ++ [b])[0]? = some a from by simp,
                    mA_getElem?_last] at h3z
                  have hab' : a = b := by simpa using h3z
                  exact hab hab'
              have hpss_take : isPalindromicSubseqSize (a :: mid) m :=
                mA_pss_take h2 h3 hlt
              have hrec := ih (mid.length + 1) (by omega) (a :: mid) (by simp) m hpss_take
              have hal : (a :: mid).length = mid.length + 1 := by simp
              have hmin : min (midp (mid ++ [b])) (midp (a :: mid)) ≤ midp (a :: mid) :=
                min_le_right _ _
              omega
            · have hpos : ∀ c, c < m → 0 < i c := by
                intro c hc
                rcases Nat.eq_zero_or_pos c with hc0 | hc0
                · subst hc0; omega
                · have := h2 0 c hc0 hc
                  omega
              have hpss_drop : isPalindromicSubseqSize (mid ++ [b]) m :=
                mA_pss_drop H1 h2 h3 hpos
              have hrec := ih (mid.length + 1) (by omega) (mid ++ [b]) (by simp) m hpss_drop
              have hbl : (mid ++ [b]).length = mid.length + 1 := by simp
              have hmin : min (midp (mid ++ [b])) (midp (a :: mid)) ≤ midp (mid ++ [b]) :=
                min_le_left _ _
              omega

  theorem mA_midp_add_pss_le (l : List U8) (m : Nat) (h : isPalindromicSubseqSize l m) :
      midp l + m ≤ l.length :=
    mA_midp_add_pss_le_aux l.length l rfl m h

  theorem mA_IsEmb_id (l : List U8) : IsEmb l l id := by
    simpa using IsEmb.prefix l []

  /-- Shifting an embedding one position to the right. -/
  theorem mA_IsEmb_shift {p q : List U8} {k : Nat → Nat} (h : IsEmb p q k) (x : U8) :
      IsEmb p (x :: q) (fun a => k a + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      dsimp only
      have h1 := h.1 a ha
      simp only [List.length_cons]
      omega
    · intro a b ha hb
      dsimp only
      have h1 := h.2.1 a b ha hb
      omega
    · intro a ha
      dsimp only
      rw [List.getElem?_cons_succ]
      exact h.2.2 a ha

  /-- Sandwiching a palindrome between two copies of one byte. -/
  theorem mA_isPalindrome_cons_append {u : List U8} (h : isPalindrome u) (x : U8) :
      isPalindrome (x :: (u ++ [x])) := by
    rw [isPalindrome_iff_reverse, List.reverse_cons, List.reverse_append, List.reverse_singleton,
      isPalindrome_reverse h]
    simp

  theorem mA_hasPSS_midp_aux : ∀ n, ∀ l : List U8, l.length = n →
      hasPalindromicSupersequence l (midp l) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l hl
      by_cases hsmall : l.length ≤ 1
      · have hmid : midp l = 0 := by rw [midp, dif_pos hsmall]
        refine ⟨l, ?_, isPalindrome_of_length_le_one hsmall, ⟨id, mA_IsEmb_id l⟩⟩
        rw [hmid]
        omega
      · have h2len : 2 ≤ l.length := by omega
        obtain ⟨a, mid, b, rfl⟩ : ∃ a mid b, l = a :: mid ++ [b] :=
          ⟨l[0]'(by omega), subList l 1 (l.length - 2), l[l.length - 1]'(by omega),
            eq_cons_subList_last l h2len⟩
        have hl' : mid.length + 2 = n := by
          have hh : (a :: mid ++ [b]).length = mid.length + 2 := by simp
          omega
        rw [midp_cons_last]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl]
          obtain ⟨u, hulen, hupal, ⟨ju, huemb⟩⟩ := ih mid.length (by omega) mid rfl
          refine ⟨a :: (u ++ [a]), ?_, mA_isPalindrome_cons_append hupal a, ?_⟩
          · have h1 : (a :: (u ++ [a])).length = u.length + 2 := by simp
            have h2 : (a :: mid ++ [a]).length = mid.length + 2 := by simp
            omega
          · exact ⟨_, (IsEmb.cons huemb a).snoc a⟩
        · rw [if_neg hab]
          rcases Nat.le_total (midp (mid ++ [b])) (midp (a :: mid)) with huv | hvu
          · obtain ⟨w, hwlen, hwpal, ⟨jw, hwemb⟩⟩ :=
              ih (mid.length + 1) (by omega) (mid ++ [b]) (by simp)
            refine ⟨a :: (w ++ [a]), ?_, mA_isPalindrome_cons_append hwpal a, ?_⟩
            · have h1 : (a :: (w ++ [a])).length = w.length + 2 := by simp
              have h2 : (a :: mid ++ [b]).length = mid.length + 2 := by simp
              have h3 : (mid ++ [b]).length = mid.length + 1 := by simp
              rw [min_eq_left huv]
              omega
            · exact ⟨_, IsEmb.cons (IsEmb.weaken hwemb [a]) a⟩
          · obtain ⟨w, hwlen, hwpal, ⟨jw, hwemb⟩⟩ :=
              ih (mid.length + 1) (by omega) (a :: mid) (by simp)
            refine ⟨b :: (w ++ [b]), ?_, mA_isPalindrome_cons_append hwpal b, ?_⟩
            · have h1 : (b :: (w ++ [b])).length = w.length + 2 := by simp
              have h2 : (a :: mid ++ [b]).length = mid.length + 2 := by simp
              have h3 : (a :: mid).length = mid.length + 1 := by simp
              rw [min_eq_right hvu]
              omega
            · exact ⟨_, mA_IsEmb_shift (IsEmb.snoc hwemb b) b⟩

  theorem mA_hasPSS_midp (l : List U8) : hasPalindromicSupersequence l (midp l) :=
    mA_hasPSS_midp_aux l.length l rfl

  /-! ### Helpers `mB_` for the inequality `midp l ≤ k` -/

  /-- The identity is an embedding of a list into itself. -/
  theorem mB_IsEmb_id (l : List U8) : IsEmb l l id := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha; exact ha
    · intro a b ha hb; exact ha
    · intro a ha; rfl

  /-- Embeddings compose. -/
  theorem mB_IsEmb_trans {a b c : List U8} {i j : Nat → Nat} (h1 : IsEmb a b i)
      (h2 : IsEmb b c j) : IsEmb a c (fun x => j (i x)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; exact h2.1 (i x) (h1.1 x hx)
    · intro x y hx hy
      exact h2.2.1 (i x) (i y) (h1.2.1 x y hx hy) (h1.1 y hy)
    · intro x hx
      dsimp only
      rw [h2.2.2 (i x) (h1.1 x hx)]
      exact h1.2.2 x hx

  /-- A sub-list sits inside its host list with a shifted identity embedding. -/
  theorem mB_IsEmb_self_sublist (l : List U8) (i k : Nat) :
      IsEmb (subList l i k) l (fun a => a + i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [subList_length] at ha
      show a + i < l.length
      omega
    · intro a b ha hb
      show a + i < b + i
      rw [subList_length] at hb
      omega
    · intro a ha
      show l[a + i]? = (subList l i k)[a]?
      rw [subList_getElem?, if_pos (by rw [subList_length] at ha; omega), Nat.add_comm]

  /-- Adding the same byte `x` at both ends of an embedding. -/
  theorem mB_IsEmb_cons_snoc {w mid : List U8} {j : Nat → Nat} (h : IsEmb w mid j) (x : U8) :
      ∃ j' : Nat → Nat, IsEmb (x :: w ++ [x]) (x :: mid ++ [x]) j' := by
    exact ⟨_, (h.cons x).snoc x⟩

  /-- Two equal entries of a list at two in-range indices are equal. -/
  theorem mB_getElem_of_getElem? {l : List U8} {a b : Nat} (h : l[a]? = l[b]?)
      (ha : a < l.length) (hb : b < l.length) : l[a] = l[b] := by
    rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at h
    exact Option.some.inj h

  /-- Lists that are equal are related by the identity embedding. -/
  theorem mB_IsEmb_of_eq {a b : List U8} (h : b = a) : IsEmb a b id := by
    cases h
    exact mB_IsEmb_id _

  /-- A palindromic subsequence gives a palindromic subsequence size. -/
  theorem mB_isPalindromicSubseqSize_of_isEmb_pal {w l : List U8} {j : Nat → Nat}
      (hemb : IsEmb w l j) (hpal : isPalindrome w) : isPalindromicSubseqSize l w.length := by
    refine ⟨j, hemb.1, hemb.2.1, ?_⟩
    intro a ha
    rw [hemb.2.2 a ha, hemb.2.2 (w.length - 1 - a) (by omega)]
    rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem (by omega)]
    rw [hpal a ha]

  /-- Combinatorial core: a palindromic host `t` containing `l` as a subsequence yields a
  palindromic subsequence of `l` of length at least `2 * len l - len t`. -/
  theorem mB_isEmb_pal_subseq_aux (n : Nat) :
      ∀ (t l : List U8) (i : Nat → Nat), t.length = n → IsEmb l t i → isPalindrome t →
        ∃ (w : List U8) (j : Nat → Nat),
          IsEmb w l j ∧ isPalindrome w ∧ 2 * l.length - t.length ≤ w.length := by
    refine Nat.strong_induction_on n ?_
    intro n ih t l i hlen hemb hpal
    subst hlen
    by_cases hsmall : l.length ≤ 1
    · exact ⟨l, id, mB_IsEmb_id l, isPalindrome_of_length_le_one hsmall,
        by have := hemb.length_le; omega⟩
    · have hn2 : 2 ≤ l.length := by omega
      have hr2 : 2 ≤ t.length := by have := hemb.length_le; omega
      have htp : isPalindrome (subList t 1 (t.length - 2)) := isPalindrome_ends hpal hr2
      have htplen : (subList t 1 (t.length - 2)).length = t.length - 2 := by
        rw [subList_length]; omega
      by_cases hlast : i (l.length - 1) = t.length - 1
      · by_cases hfirst : i 0 = 0
        · -- both ends of `t` are taken by the two ends of `l`
          have h0l : l[0]? = t[0]? := by rw [← hemb.2.2 0 (by omega), hfirst]
          have hnl : l[l.length - 1]? = t[t.length - 1]? := by
            rw [← hemb.2.2 (l.length - 1) (by omega), hlast]
          have htends : t[0]? = t[t.length - 1]? := by
            rw [List.getElem?_eq_getElem (show 0 < t.length by omega),
              List.getElem?_eq_getElem (show t.length - 1 < t.length by omega)]
            have h := hpal 0 (show 0 < t.length by omega)
            exact congrArg some h
          have hxe : l[0]'(by omega) = l[l.length - 1]'(by omega) :=
            mB_getElem_of_getElem? (by rw [h0l, htends, ← hnl]) (by omega) (by omega)
          have hl : l = l[0]'(by omega) :: subList l 1 (l.length - 2) ++ [l[0]'(by omega)] :=
            (eq_cons_subList_last l hn2).trans (by rw [hxe])
          have hmidlen : (subList l 1 (l.length - 2)).length = l.length - 2 := by
            rw [subList_length]; omega
          have hmidemb : IsEmb (subList l 1 (l.length - 2)) (subList t 1 (t.length - 2))
              (fun a => i (a + 1) - 1) := by
            have h1 : IsEmb (subList l 1 (l.length - 2)) t (fun a => i (a + 1)) :=
              hemb.ofSubListLeft 1 (l.length - 2)
            refine h1.sub 1 (t.length - 2) (fun a ha => ?_) (fun a ha => ?_)
            · show 1 ≤ i (a + 1)
              rw [subList_length] at ha
              have hmono := hemb.2.1 0 (a + 1) (by omega) (by omega)
              omega
            · show i (a + 1) < 1 + (t.length - 2)
              rw [subList_length] at ha
              have hmono := hemb.2.1 (a + 1) (l.length - 1) (by omega) (by omega)
              omega
          obtain ⟨w', jw, hw'emb, hw'pal, hw'len⟩ :=
            ih (subList t 1 (t.length - 2)).length (by rw [subList_length]; omega)
              (subList t 1 (t.length - 2)) (subList l 1 (l.length - 2))
              (fun a => i (a + 1) - 1) rfl hmidemb htp
          have hw'len' : 2 * (l.length - 2) - (t.length - 2) ≤ w'.length := by
            have h := hw'len
            rw [hmidlen, htplen] at h
            exact h
          have hpalW : isPalindrome (l[0]'(by omega) :: w' ++ [l[0]'(by omega)]) := by
            rw [isPalindrome_iff_reverse]
            simp [List.reverse_append, isPalindrome_reverse hw'pal]
          obtain ⟨j', hj'⟩ := mB_IsEmb_cons_snoc hw'emb (l[0]'(by omega))
          have hembW : IsEmb (l[0]'(by omega) :: w' ++ [l[0]'(by omega)]) l
              (fun y => id (j' y)) :=
            mB_IsEmb_trans (a := l[0]'(by omega) :: w' ++ [l[0]'(by omega)])
              (b := l[0]'(by omega) :: subList l 1 (l.length - 2) ++ [l[0]'(by omega)])
              (c := l) (i := j') (j := id) hj' (mB_IsEmb_of_eq hl)
          refine ⟨_, fun y => id (j' y), hembW, hpalW, ?_⟩
          show 2 * l.length - t.length ≤ (l[0]'(by omega) :: w' ++ [l[0]'(by omega)]).length
          simp only [List.length_cons, List.length_append, List.length_nil]
          omega
        · -- the first byte of `l` skips position `0`; drop the last byte of `l`
          have hp0 : 0 < i 0 := Nat.pos_of_ne_zero hfirst
          have hmidlen : (subList l 0 (l.length - 1)).length = l.length - 1 := by
            rw [subList_length]; omega
          have hmidemb : IsEmb (subList l 0 (l.length - 1)) (subList t 1 (t.length - 2))
              (fun a => i a - 1) := by
            have h1 : IsEmb (subList l 0 (l.length - 1)) t (fun a => i (a + 0)) :=
              hemb.ofSubListLeft 0 (l.length - 1)
            have h1' : IsEmb (subList l 0 (l.length - 1)) t i := h1
            refine h1'.sub 1 (t.length - 2) (fun a ha => ?_) (fun a ha => ?_)
            · show 1 ≤ i a
              rcases Nat.eq_zero_or_pos a with h0 | hpos
              · subst h0; omega
              · have hmono := hemb.2.1 0 a hpos (by rw [subList_length] at ha; omega)
                omega
            · show i a < 1 + (t.length - 2)
              rw [subList_length] at ha
              have hmono := hemb.2.1 a (l.length - 1) (by omega) (by omega)
              omega
          obtain ⟨w', jw, hw'emb, hw'pal, hw'len⟩ :=
            ih (subList t 1 (t.length - 2)).length (by rw [subList_length]; omega)
              (subList t 1 (t.length - 2)) (subList l 0 (l.length - 1))
              (fun a => i a - 1) rfl hmidemb htp
          have hw'len' : 2 * (l.length - 1) - (t.length - 2) ≤ w'.length := by
            have h := hw'len
            rw [hmidlen, htplen] at h
            exact h
          have hembW : IsEmb w' l (fun x => (fun a => a + 0) (jw x)) :=
            mB_IsEmb_trans (a := w') (b := subList l 0 (l.length - 1)) (c := l)
              (i := jw) (j := fun a => a + 0) hw'emb (mB_IsEmb_self_sublist l 0 (l.length - 1))
          exact ⟨w', _, hembW, hw'pal, by omega⟩
      · have hlt_last : i (l.length - 1) < t.length - 1 := by
          have := hemb.1 (l.length - 1) (by omega)
          omega
        by_cases hfirst : i 0 = 0
        · -- the first byte of `l` takes position `0`; drop the first byte of `l`
          have hmidlen : (subList l 1 (l.length - 1)).length = l.length - 1 := by
            rw [subList_length]; omega
          have hmidemb : IsEmb (subList l 1 (l.length - 1)) (subList t 1 (t.length - 2))
              (fun a => i (a + 1) - 1) := by
            have h1 : IsEmb (subList l 1 (l.length - 1)) t (fun a => i (a + 1)) :=
              hemb.ofSubListLeft 1 (l.length - 1)
            refine h1.sub 1 (t.length - 2) (fun a ha => ?_) (fun a ha => ?_)
            · show 1 ≤ i (a + 1)
              rw [subList_length] at ha
              have hmono := hemb.2.1 0 (a + 1) (by omega) (by omega)
              omega
            · show i (a + 1) < 1 + (t.length - 2)
              rw [subList_length] at ha
              rcases Nat.lt_or_eq_of_le (show a + 1 ≤ l.length - 1 by omega) with h | h
              · have hmono := hemb.2.1 (a + 1) (l.length - 1) h (by omega)
                omega
              · rw [h]; omega
          obtain ⟨w', jw, hw'emb, hw'pal, hw'len⟩ :=
            ih (subList t 1 (t.length - 2)).length (by rw [subList_length]; omega)
              (subList t 1 (t.length - 2)) (subList l 1 (l.length - 1))
              (fun a => i (a + 1) - 1) rfl hmidemb htp
          have hw'len' : 2 * (l.length - 1) - (t.length - 2) ≤ w'.length := by
            have h := hw'len
            rw [hmidlen, htplen] at h
            exact h
          have hembW : IsEmb w' l (fun x => (fun a => a + 1) (jw x)) :=
            mB_IsEmb_trans hw'emb (mB_IsEmb_self_sublist l 1 (l.length - 1))
          exact ⟨w', _, hembW, hw'pal, by omega⟩
        · -- skip position `0`, keep all of `l`
          have hp0 : 0 < i 0 := Nat.pos_of_ne_zero hfirst
          have hmidemb : IsEmb l (subList t 1 (t.length - 2)) (fun a => i a - 1) := by
            refine hemb.sub 1 (t.length - 2) (fun a ha => ?_) (fun a ha => ?_)
            · show 1 ≤ i a
              rcases Nat.eq_zero_or_pos a with h0 | hpos
              · subst h0; omega
              · have hmono := hemb.2.1 0 a hpos ha
                omega
            · show i a < 1 + (t.length - 2)
              rcases Nat.lt_or_eq_of_le (show a ≤ l.length - 1 by omega) with h | h
              · have hmono := hemb.2.1 a (l.length - 1) h (by omega)
                omega
              · rw [h]; omega
          obtain ⟨w', jw, hw'emb, hw'pal, hw'len⟩ :=
            ih (subList t 1 (t.length - 2)).length (by rw [subList_length]; omega)
              (subList t 1 (t.length - 2)) l (fun a => i a - 1) rfl hmidemb htp
          have hw'len' : 2 * l.length - (t.length - 2) ≤ w'.length := by
            have h := hw'len
            rw [htplen] at h
            exact h
          exact ⟨w', jw, hw'emb, hw'pal, by omega⟩

  /-- Step 1: a palindrome containing `l` as a subsequence yields a palindromic subsequence of
  `l` of length at least `2 * len l - len t`. -/
  theorem mB_isEmb_pal_subseq {l t : List U8} {i : Nat → Nat} (hemb : IsEmb l t i)
      (hpal : isPalindrome t) :
      ∃ (w : List U8) (j : Nat → Nat),
        IsEmb w l j ∧ isPalindrome w ∧ 2 * l.length - t.length ≤ w.length :=
    mB_isEmb_pal_subseq_aux t.length t l i rfl hemb hpal

  /-- **Any palindromic supersequence with `k` extra bytes forces `midp l ≤ k`.** -/
  theorem mB_hasPSS_le_midp (l : List U8) (k : Nat) (h : hasPalindromicSupersequence l k) :
      midp l ≤ k := by
    obtain ⟨t, htlen, htpal, ⟨idx, hemb⟩⟩ := h
    obtain ⟨w, j, hwemb, hwpal, hwlen⟩ := mB_isEmb_pal_subseq hemb htpal
    have hps : isPalindromicSubseqSize l w.length :=
      mB_isPalindromicSubseqSize_of_isEmb_pal hwemb hwpal
    have hmA : midp l + w.length ≤ l.length := mA_midp_add_pss_le l w.length hps
    have hle : w.length ≤ l.length := hwemb.length_le
    omega

  /-! ### Verified functional correctness of the extracted DP (`dp_min_insertions_val`) -/

  /-- Splitting step for the DP recurrence: `midp` of a sub-list is obtained from the `midp`'s of
  the two sub-lists obtained by dropping one of the two ends. -/
  theorem dp_midp_subList_step (l : List U8) (i len : Nat) (hle : i + len ≤ l.length)
      (h2 : 2 ≤ len) :
      midp (subList l i len) =
        (if l[i]? = l[i + len - 1]? then midp (subList l (i+1) (len-2))
         else 1 + min (midp (subList l (i+1) (len-1))) (midp (subList l i (len-1)))) := by
    have hlen : (subList l i len).length = len := by rw [subList_length]; omega
    have e0 : (subList l i len)[0]? = l[i]? := by
      rw [subList_getElem?, if_pos (by omega), Nat.add_zero]
    have elast : (subList l i len)[len - 1]? = l[i + len - 1]? := by
      rw [subList_getElem?, if_pos (by omega)]
      congr 1
      omega
    rw [midp]
    rw [dif_neg (by omega)]
    simp only [hlen]
    rw [e0, elast]
    rw [show subList (subList l i len) 1 (len - 2) = subList l (i + 1) (len - 2) from
      subList_subList l i 1 len (len-2) (by omega)]
    rw [show subList (subList l i len) 1 (len - 1) = subList l (i + 1) (len - 1) from
      subList_subList l i 1 len (len-1) (by omega)]
    rw [show subList (subList l i len) 0 (len - 1) = subList l i (len - 1) from
      subList_subList l i 0 len (len-1) (by omega)]

  /-- `midp` is at most the length of the list. -/
  theorem dp_midp_le_length (l : List U8) : midp l ≤ l.length := by
    suffices H : ∀ (n : Nat) (l : List U8), l.length ≤ n → midp l ≤ l.length from H _ l le_rfl
    intro n
    induction n with
    | zero =>
      intro l hl
      have h0 : l.length = 0 := by omega
      rw [midp]
      simp [h0]
    | succ n ih =>
      intro l hl
      rw [midp]
      split
      · omega
      · rename_i h1
        split
        · rename_i h2
          have ih1 := ih (subList l 1 (l.length - 2)) (by rw [subList_length]; omega)
          rw [subList_length] at ih1
          omega
        · rename_i h2
          have ih1 := ih (subList l 1 (l.length - 1)) (by rw [subList_length]; omega)
          have ih2 := ih (subList l 0 (l.length - 1)) (by rw [subList_length]; omega)
          rw [subList_length] at ih1 ih2
          omega

  /-- The `(a,b)` entry of a DP table, as an option. -/
  def dp_cell (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat) : Option Std.I64 :=
    (dp.val[a]?).bind (fun r => r.val[b]?)

  theorem dp_cell_eq_some_iff (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat) (x : Std.I64) :
      dp_cell dp a b = some x ↔
        ∃ r : alloc.vec.Vec Std.I64, dp.val[a]? = some r ∧ r.val[b]? = some x := by
    unfold dp_cell
    constructor
    · intro h
      cases h1 : dp.val[a]? with
      | none => rw [h1] at h; simp at h
      | some r =>
        refine ⟨r, rfl, ?_⟩
        rw [h1, Option.bind_some] at h
        exact h
    · rintro ⟨r, h1, h2⟩
      rw [h1, Option.bind_some]
      exact h2

  theorem dp_cell_of_getElem (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat) (x : Std.I64)
      (ha : a < dp.val.length) (hb : b < (dp.val[a]).val.length) (h : (dp.val[a]).val[b] = x) :
      dp_cell dp a b = some x := by
    rw [dp_cell_eq_some_iff]
    exact ⟨dp.val[a], List.getElem?_eq_getElem ha, by rw [List.getElem?_eq_getElem hb, h]⟩

  theorem dp_cell_of_rows (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat)
      (v : alloc.vec.Vec Std.I64) (y : Std.I64) (h1 : dp.val[a]? = some v)
      (h2 : v.val[b]? = some y) : dp_cell dp a b = some y :=
    (dp_cell_eq_some_iff dp a b y).mpr ⟨v, h1, h2⟩

  theorem dp_cell_val_of (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat) (x : Std.I64)
      (ha : a < dp.val.length) (hb : b < (dp.val[a]).val.length)
      (h : dp_cell dp a b = some x) : (dp.val[a]).val[b] = x := by
    rw [dp_cell_eq_some_iff] at h
    obtain ⟨r, h1, h2⟩ := h
    rw [List.getElem?_eq_getElem ha, Option.some.injEq] at h1
    rw [← h1, List.getElem?_eq_getElem hb, Option.some.injEq] at h2
    exact h2

  /-- After `Vec.set` at row `i` the entry `(i,b)` is read from the new row. -/
  theorem dp_cell_set_self (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) (b : Nat) (hi : i.val < dp.val.length) :
      dp_cell (dp.set i r') i.val b = r'.val[b]? := by
    unfold dp_cell
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos (by omega)]
    rw [if_pos hi, Option.bind_some]

  /-- `Vec.set` at row `i` leaves all other rows untouched. -/
  theorem dp_cell_set_ne (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) (a b : Nat) (ha : a ≠ i.val) :
      dp_cell (dp.set i r') a b = dp_cell dp a b := by
    unfold dp_cell
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_neg (by omega)]

  /-- Filling the entry `(i,j)` of the table: the new entry, and all other entries unchanged. -/
  theorem dp_cell_set_set (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) (x : Std.I64) (a b : Nat) (hi : i.val < dp.val.length)
      (hj : j.val < r'.val.length) :
      dp_cell (dp.set i (r'.set j x)) a b =
        (if a = i.val then (if j.val = b then some x else r'.val[b]?) else dp_cell dp a b) := by
    by_cases h : a = i.val
    · subst h
      rw [dp_cell_set_self dp i _ b hi, if_pos rfl, alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases h2 : j.val = b
      · rw [if_pos h2, if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg h2]
    · rw [dp_cell_set_ne dp i _ a b h, if_neg h]

  /-- All rows of the table have length `n`. -/
  def dp_rows (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dp.val.length = n ∧ ∀ r ∈ dp.val, r.val.length = n

  theorem dp_rows_set (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) (h : dp_rows n dp) (hr : r'.val.length = n) :
      dp_rows n (dp.set i r') := by
    obtain ⟨h1, h2⟩ := h
    refine ⟨by simp only [alloc.vec.Vec.set_length]; exact h1, ?_⟩
    intro r hr'
    rw [alloc.vec.Vec.set_val_eq] at hr'
    rcases List.mem_or_eq_of_mem_set hr' with hmem | rfl
    · exact h2 r hmem
    · exact hr

  /-- Every cell `(a,b)` with `a ≤ b < n` and `b - a + 1 ≤ L` holds `midp` of the corresponding
  sub-list. -/
  def dp_ok (l : List U8) (n L : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ (a b : Nat), a ≤ b → b < n → b - a + 1 ≤ L →
      ∃ x : Std.I64, dp_cell dp a b = some x ∧ x.val = (midp (subList l a (b - a + 1)) : Int)

  /-- The cells of length `L` whose start index is below `start` are already filled in. -/
  def dp_stage (l : List U8) (n L start : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ (a : Nat), a < start → a + L ≤ n →
      ∃ x : Std.I64, dp_cell dp a (a + L - 1) = some x ∧ x.val = (midp (subList l a L) : Int)

  theorem dp_ok_mono (l : List U8) (n : Nat) {L L' : Nat} (h : L ≤ L')
      {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} (hd : dp_ok l n L' dp) : dp_ok l n L dp :=
    fun a b h1 h2 h3 => hd a b h1 h2 (by omega)

  theorem dp_ok_of_agree (l : List U8) (n L : Nat) {dp dp' : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      (h : dp_ok l n L dp)
      (hagree : ∀ (a b : Nat), a ≤ b → b < n → b - a + 1 ≤ L → dp_cell dp' a b = dp_cell dp a b) :
      dp_ok l n L dp' := by
    intro a b h1 h2 h3
    obtain ⟨x, hx, hv⟩ := h a b h1 h2 h3
    exact ⟨x, by rw [hagree a b h1 h2 h3]; exact hx, hv⟩

  theorem dp_stage_mono (l : List U8) (n L : Nat) {s s' : Nat}
      {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} (h : s ≤ s') (hd : dp_stage l n L s' dp) :
      dp_stage l n L s dp :=
    fun a ha => hd a (by omega)

  theorem dp_stage_of_agree (l : List U8) (n L s : Nat)
      {dp dp' : alloc.vec.Vec (alloc.vec.Vec Std.I64)} (h : dp_stage l n L s dp)
      (hagree : ∀ (a : Nat), a < s → a + L ≤ n →
        dp_cell dp' a (a + L - 1) = dp_cell dp a (a + L - 1)) :
      dp_stage l n L s dp' := by
    intro a ha hb
    obtain ⟨x, hx, hv⟩ := h a ha hb
    exact ⟨x, by rw [hagree a ha hb]; exact hx, hv⟩
  /-- `dp_spec f p`: every successful outcome of `f` satisfies `p`.  In contrast with the Aeneas
  Hoare triple `f ⦃ p ⦄` this does not demand that `f` avoids failing, which is essential here:
  the extracted program uses checked 64-bit arithmetic and therefore fails on astronomically long
  inputs, while the specifications we need only concern the successful runs. -/
  def dp_spec {α : Type} (f : Result α) (p : α → Prop) : Prop := ∀ r, f = ok r → p r

  theorem dp_spec_ok {α : Type} (x : α) (p : α → Prop) : dp_spec (ok x) p ↔ p x := by
    refine ⟨fun h => h x rfl, fun h r hr => ?_⟩
    rw [Result.ok.injEq] at hr
    rw [← hr]
    exact h

  theorem dp_spec_ok_mpr {α : Type} {x : α} {p : α → Prop} (h : p x) : dp_spec (ok x) p :=
    dp_spec_ok x p |>.mpr h

  theorem dp_spec_of_match {α : Type} (f : Result α) (p : α → Prop)
      (h : ∀ (z : α), f.match = .ok z → p z) : dp_spec f p := by
    intro r hr
    rw [hr] at h
    exact h r Result.match.ok

  theorem dp_spec_bind {α β : Type} {m : Result α} {k : α → Result β}
      {pm : α → Prop} {pk : β → Prop}
      (hm : dp_spec m pm) (hk : ∀ x, pm x → dp_spec (k x) pk) :
      dp_spec (Std.bind m k) pk := by
    intro r h
    match hmm : m.match with
    | .ok x =>
      have h1 : m = ok x := Result.match.isOk.mp hmm
      rw [h1, bind_ok] at h
      exact hk x (hm x h1) r h
    | .vis e k' =>
      have h1 : m = Result.vis e k' := Result.match.isVis.mp hmm
      rw [h1] at h
      rw [show Std.bind (Result.vis e k') k = Result.vis e (fun y => Std.bind (k' y) k)
        from bind_vis e k' k] at h
      exact absurd h vis_not_ok
    | .div =>
      have h1 : m = Result.div := Result.match.isDiv.mp hmm
      rw [h1] at h
      rw [show Std.bind (Result.div) k = Result.div from bind_div k] at h
      exact absurd h div_not_ok

  theorem dp_spec_ofOption {α : Type} (o : Option α) (e : Error) :
      dp_spec (Result.ofOption o e) (fun x => o = some x) := by
    intro r h
    cases o with
    | none => simp [Result.ofOption] at h
    | some y =>
      simp only [Result.ofOption, Result.ok.injEq] at h
      rw [h]

  theorem dp_spec_vec_index {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
      dp_spec (v.index_usize i) (fun x => v.val[i.val]? = some x) := by
    intro r h
    simp only [alloc.vec.Vec.index_usize] at h
    split at h
    · simp at h
    · rename_i y hy
      simp only [Result.ok.injEq] at h
      rw [h] at hy
      exact hy

  theorem dp_spec_slice_index {α : Type} (s : Slice α) (i : Std.Usize) :
      dp_spec (Slice.index_usize s i) (fun x => s.val[i.val]? = some x) := by
    intro r h
    simp only [Slice.index_usize] at h
    split at h
    · simp at h
    · rename_i y hy
      simp only [Result.ok.injEq] at h
      rw [h] at hy
      exact hy

  theorem dp_spec_vec_index_mut_usize {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
      dp_spec (v.index_mut_usize i) (fun p => v.val[i.val]? = some p.1 ∧ p.2 = v.set i) := by
    refine dp_spec_bind (dp_spec_vec_index v i) ?_
    intro x hx
    exact dp_spec_ok_mpr ⟨hx, rfl⟩

  theorem dp_spec_vec_index_mut {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
      dp_spec (alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i)
        (fun p => v.val[i.val]? = some p.1 ∧ p.2 = v.set i) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact dp_spec_vec_index_mut_usize v i

  theorem dp_spec_vec_push {α : Type} (v : alloc.vec.Vec α) (x : α) :
      dp_spec (v.push x) (fun v' => v'.val = v.val ++ [x]) := by
    intro r h
    unfold alloc.vec.Vec.push at h
    dsimp only at h
    split at h
    · rename_i hh
      simp only [Result.ok.injEq] at h
      rw [← h, alloc.vec.Vec.from_val]
      simp [List.concat_eq_append]
    · simp at h

  theorem dp_spec_bind_elim {α β : Type} {m : Result α} {k : α → Result β} {r : β}
      (h : Std.bind m k = ok r) : ∃ x, m = ok x ∧ k x = ok r := by
    match hmm : m.match with
    | .ok x =>
      refine ⟨x, Result.match.isOk.mp hmm, ?_⟩
      rw [Result.match.isOk.mp hmm, bind_ok] at h
      exact h
    | .vis e k' =>
      exfalso
      have h1 : m = Result.vis e k' := Result.match.isVis.mp hmm
      rw [h1] at h
      rw [show Std.bind (Result.vis e k') k = Result.vis e (fun y => Std.bind (k' y) k)
        from bind_vis e k' k] at h
      exact absurd h vis_not_ok
    | .div =>
      exfalso
      have h1 : m = Result.div := Result.match.isDiv.mp hmm
      rw [h1] at h
      rw [show Std.bind (Result.div) k = Result.div from bind_div k] at h
      exact absurd h div_not_ok

  theorem dp_spec_i64_add (x y : Std.I64) :
      dp_spec (x + y) (fun z => z.val = x.val + y.val) := by
    apply dp_spec_of_match
    intro z hz
    have := IScalar.add_equiv (ty := IScalarTy.I64) x y
    rw [hz] at this
    exact this.2.1

  theorem dp_spec_usize_add (x y : Std.Usize) :
      dp_spec (x + y) (fun z => z.val = x.val + y.val) := by
    apply dp_spec_of_match
    intro z hz
    have := UScalar.add_equiv (ty := UScalarTy.Usize) x y
    rw [hz] at this
    exact this.2.1

  theorem dp_spec_usize_sub (x y : Std.Usize) :
      dp_spec (x - y) (fun z => z.val = x.val - y.val) := by
    apply dp_spec_of_match
    intro z hz
    have := UScalar.sub_equiv (ty := UScalarTy.Usize) x y
    rw [hz] at this
    omega

  /-- Case analysis for the result of a loop body: `done` gives the loop post-condition, `cont`
  gives the loop invariant together with the decrease of the measure. -/
  def dp_cf {α β : Type} (kd : β → Prop) (kc : α → Prop) : ControlFlow α β → Prop
    | .done y => kd y
    | .cont x' => kc x'

  /-- Loop rule for `dp_spec`: partial correctness of a `loop` with a decreasing measure. -/
  theorem dp_loop_ok {α : Type} {β : Type} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
      (body : α → Result (ControlFlow α β))
      (hBody : ∀ x, inv x →
        dp_spec (body x) (dp_cf post (fun x' => inv x' ∧ measure x' < measure x)))
      (x : α) (hInv : inv x) : dp_spec (loop body x) post := by
    suffices H : ∀ (n : Nat) (x : α), measure x = n → inv x → dp_spec (loop body x) post from
      H _ x rfl hInv
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hm hx
      have hcomp : dp_spec (loop body x) post := by
        unfold loop
        refine dp_spec_bind (hBody x hx) ?_
        intro c hc
        cases c with
        | cont x' =>
          simp only [dp_cf] at hc
          exact ih (measure x') (by omega) x' rfl hc.1
        | done y =>
          simp only [dp_cf] at hc
          exact dp_spec_ok_mpr hc
      exact hcomp

  /-! #### The zero-filling loops -/

  /-- Loop state invariant of `min_insertions_loop0_loop0`: the row under construction has `j`
  zeros. -/
  def dp_inv0 (n : Std.Usize) (st : alloc.vec.Vec Std.I64 × Std.Usize) : Prop :=
    st.1.val.length = st.2.val ∧ st.2.val ≤ n.val ∧ ∀ x ∈ st.1.val, x = 0#i64

  theorem dp_loop0_loop0_body (n : Std.Usize) (row : alloc.vec.Vec Std.I64) (j : Std.Usize)
      (hinv : dp_inv0 n (row, j)) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop0_loop0.body n row j)
        (dp_cf (fun y => y.val.length = n.val ∧ ∀ x ∈ y.val, x = 0#i64)
          (fun x' => dp_inv0 n x' ∧ n.val - x'.2.val < n.val - j.val)) := by
    unfold dp_inv0 at hinv
    dsimp only at hinv
    obtain ⟨h1, h2, h3⟩ := hinv
    intro r h
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body at h
    split at h
    · rename_i hb
      obtain ⟨row1, hpush, h⟩ := dp_spec_bind_elim h
      obtain ⟨j1, hj1, h⟩ := dp_spec_bind_elim h
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      have hv : row1.val = row.val ++ [0#i64] := dp_spec_vec_push row 0#i64 row1 hpush
      have hj : j1.val = j.val + 1 := dp_spec_usize_add j 1#usize j1 hj1
      have hb' : j.val < n.val := hb
      refine ⟨?_, ?_⟩
      · unfold dp_inv0
        exact ⟨by rw [hv, hj]; simp; omega, by rw [hj]; omega, by
          rw [hv]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact h3 x hx
          · simp at hx; rw [hx]⟩
      · rw [hj]; omega
    · rename_i hb
      have hb' : ¬ (j.val < n.val) := hb
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      exact ⟨by omega, h3⟩

  theorem dp_loop0_loop0_spec (n : Std.Usize) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop0_loop0 n (alloc.vec.Vec.new Std.I64) 0#usize)
        (fun row => row.val.length = n.val ∧ ∀ x ∈ row.val, x = 0#i64) := by
    refine dp_loop_ok (α := alloc.vec.Vec Std.I64 × Std.Usize) (β := alloc.vec.Vec Std.I64)
      (measure := fun st => n.val - st.2.val) (inv := dp_inv0 n)
      (post := fun row => row.val.length = n.val ∧ ∀ x ∈ row.val, x = 0#i64)
      (body := fun st => Aegis.MinInsertions.min_insertions_loop0_loop0.body n st.1 st.2)
      ?_ (alloc.vec.Vec.new Std.I64, 0#usize) ?_
    · rintro ⟨row, j⟩ hinv
      dsimp only
      exact dp_loop0_loop0_body n row j hinv
    · unfold dp_inv0
      refine ⟨?_, ?_, ?_⟩
      · simp [alloc.vec.Vec.new]
      · simp
      · intro x hx
        simp [alloc.vec.Vec.new] at hx

  /-! #### The outer zero-filling loop -/

  /-- All rows of the table have length `n`. -/
  def dp_all_rows (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ r ∈ dp.val, r.val.length = n

  theorem dp_rows_iff (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      dp_rows n dp ↔ dp.val.length = n ∧ dp_all_rows n dp := Iff.rfl

  /-- Loop state invariant of `min_insertions_loop0`: `i` rows of zeros have been pushed. -/
  def dp_inv1 (n : Std.Usize) (st : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize) : Prop :=
    st.1.val.length = st.2.val ∧ dp_all_rows n.val st.1 ∧ st.2.val ≤ n.val ∧
      ∀ r ∈ st.1.val, ∀ x ∈ r.val, x = 0#i64

  theorem dp_loop0_body (n : Std.Usize) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (i : Std.Usize) (hinv : dp_inv1 n (dp, i)) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop0.body n dp i)
        (dp_cf (fun y => dp_rows n.val y ∧ ∀ r ∈ y.val, ∀ x ∈ r.val, x = 0#i64)
          (fun x' => dp_inv1 n x' ∧ n.val - x'.2.val < n.val - i.val)) := by
    unfold dp_inv1 at hinv
    dsimp only at hinv
    obtain ⟨h1, h2, h3, h4⟩ := hinv
    intro r h
    unfold Aegis.MinInsertions.min_insertions_loop0.body at h
    split at h
    · rename_i hb
      obtain ⟨row, hrow, h⟩ := dp_spec_bind_elim h
      obtain ⟨dp1, hpush, h⟩ := dp_spec_bind_elim h
      obtain ⟨i1, hi1, h⟩ := dp_spec_bind_elim h
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      have hrow' : row.val.length = n.val ∧ ∀ x ∈ row.val, x = 0#i64 :=
        dp_loop0_loop0_spec n row hrow
      have hpush' : dp1.val = dp.val ++ [row] := dp_spec_vec_push dp row dp1 hpush
      have hi1' : i1.val = i.val + 1 := dp_spec_usize_add i 1#usize i1 hi1
      have hb' : i.val < n.val := hb
      refine ⟨?_, ?_⟩
      · unfold dp_inv1
        dsimp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hpush']; simp; omega
        · intro q hq
          rw [hpush'] at hq
          rcases List.mem_append.mp hq with hq | hq
          · exact h2 q hq
          · simp at hq; rw [hq]; exact hrow'.1
        · rw [hi1']; omega
        · intro q hq
          rw [hpush'] at hq
          rcases List.mem_append.mp hq with hq | hq
          · exact h4 q hq
          · simp at hq; rw [hq]; exact hrow'.2
      · rw [hi1']; omega
    · rename_i hb
      have hb' : ¬ (i.val < n.val) := hb
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      exact ⟨⟨by omega, h2⟩, h4⟩

  theorem dp_loop0_spec (n : Std.Usize) :
      dp_spec
        (Aegis.MinInsertions.min_insertions_loop0 n
          (alloc.vec.Vec.new (alloc.vec.Vec Std.I64)) 0#usize)
        (fun dp => dp_rows n.val dp ∧ ∀ r ∈ dp.val, ∀ x ∈ r.val, x = 0#i64) := by
    refine dp_loop_ok (α := alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (measure := fun st => n.val - st.2.val) (inv := dp_inv1 n)
      (post := fun dp => dp_rows n.val dp ∧ ∀ r ∈ dp.val, ∀ x ∈ r.val, x = 0#i64)
      (body := fun st => Aegis.MinInsertions.min_insertions_loop0.body n st.1 st.2)
      ?_ (alloc.vec.Vec.new (alloc.vec.Vec Std.I64), 0#usize) ?_
    · rintro ⟨dp, i⟩ hinv
      dsimp only
      simpa using dp_loop0_body n dp i hinv
    · unfold dp_inv1
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [alloc.vec.Vec.new]
      · intro x hx
        simp [alloc.vec.Vec.new] at hx
      · simp
      · intro r hr
        simp [alloc.vec.Vec.new] at hr
  /-! #### Cell surgery -/

  theorem dp_cell_get_row (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat)
      (ha : a < dp.val.length) : dp_cell dp a b = (dp.val[a]).val[b]? := by
    unfold dp_cell
    rw [List.getElem?_eq_getElem ha, Option.bind_some]

  /-- Overwriting the cell `(i,j)` only changes that cell. -/
  theorem dp_cell_set_cell (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Std.Usize)
      (x : Std.I64) (a b : Nat) (hi : i.val < dp.val.length)
      (hj : j.val < (dp.val[i.val]).val.length) :
      dp_cell (dp.set i ((dp.val[i.val]).set j x)) a b =
        (if a = i.val ∧ b = j.val then some x else dp_cell dp a b) := by
    rw [dp_cell_set_set dp i j (dp.val[i.val]) x a b hi hj]
    by_cases h1 : a = i.val
    · by_cases h2 : j.val = b
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, by omega⟩]
      · rw [if_pos h1, if_neg h2, if_neg (by omega)]
        rw [h1]
        exact (dp_cell_get_row dp i.val b hi).symm
    · rw [if_neg h1, if_neg (by omega)]

  theorem dp_ok_val (l : List U8) (n L : Nat) {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      (h : dp_ok l n L dp) {a b : Nat} (hab : a ≤ b) (hbn : b < n) (hk : b - a + 1 ≤ L)
      {y : Std.I64} (hy : dp_cell dp a b = some y) :
      y.val = (midp (subList l a (b - a + 1)) : Int) := by
    obtain ⟨x, hx, hv⟩ := h a b hab hbn hk
    rw [hy, Option.some.injEq] at hx
    rw [hx]
    exact hv

  /-! #### The DP-filling inner loop -/

  /-- Loop state invariant of `min_insertions_loop1_loop0`. -/
  def dp_inv2 (l : List U8) (n len : Nat)
      (st : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize) : Prop :=
    dp_rows n st.1 ∧ dp_ok l n (len - 1) st.1 ∧ dp_stage l n len st.2.val st.1

  /-- Writing the correct value into the cell `(start, start + len - 1)` preserves the invariant
  and advances the stage. -/
  theorem dp_inv2_step (l : List U8) (n len : Nat) {dp dp1 : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {start e : Std.Usize} {x : Std.I64} (hlen2 : 2 ≤ len) (hstart : start.val + len ≤ n)
      (he : e.val = start.val + len - 1)
      (hrows : dp_rows n dp) (hok : dp_ok l n (len - 1) dp) (hstage : dp_stage l n len start.val dp)
      (hrows1 : dp_all_rows n dp1) (hrows1len : dp1.val.length = n)
      (hset : ∀ (a b : Nat), dp_cell dp1 a b =
        (if a = start.val ∧ b = e.val then some x else dp_cell dp a b))
      (hx : x.val = (midp (subList l start.val len) : Int)) :
      dp_rows n dp1 ∧ dp_ok l n (len - 1) dp1 ∧ dp_stage l n len (start.val + 1) dp1 := by
    refine ⟨⟨hrows1len, hrows1⟩, ?_, ?_⟩
    · refine dp_ok_of_agree l n (len - 1) hok ?_
      intro a b hab hbn hk
      rw [hset a b, if_neg (by rintro ⟨rfl, rfl⟩; omega)]
    · intro a ha hb
      rcases Nat.lt_or_eq_of_le (show a ≤ start.val from by omega) with hlt | heq
      · obtain ⟨y, hy, hv⟩ := hstage a hlt hb
        rw [hset a (a + len - 1), if_neg (by rintro ⟨rfl, _⟩; omega)]
        exact ⟨y, hy, hv⟩
      · subst heq
        refine ⟨x, ?_, hx⟩
        rw [hset start.val (start.val + len - 1), if_pos ⟨rfl, by omega⟩]

  theorem dp_rows_row_len (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (h : dp_rows n dp) (a : Nat) (v : alloc.vec.Vec Std.I64) (hv : dp.val[a]? = some v) :
      v.val.length = n := by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ha, he⟩ := List.getElem?_eq_some_iff.mp hv
    rw [← he]
    exact h2 _ (List.getElem_mem ha)

  theorem dp_all_rows_set (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) (h : dp_all_rows n dp) (hr : r'.val.length = n) :
      dp_all_rows n (dp.set i r') := by
    intro q hq
    rw [alloc.vec.Vec.set_val_eq] at hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact h q hq
    · exact hr

  theorem dp_len_set (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (r' : alloc.vec.Vec Std.I64) : (dp.set i r').val.length = dp.val.length := by
    simp only [alloc.vec.Vec.set_val_eq, List.length_set]

  theorem dp_cell_set_cell2 (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Std.Usize)
      (row : alloc.vec.Vec Std.I64) (j : Std.Usize) (x w : Std.I64) (a b : Nat)
      (hi : dp.val[i.val]? = some row) (hj : row.val[j.val]? = some w) :
      dp_cell (dp.set i (row.set j x)) a b =
        (if a = i.val ∧ b = j.val then some x else dp_cell dp a b) := by
    obtain ⟨hi1, hi2⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj1, hj2⟩ := List.getElem?_eq_some_iff.mp hj
    have hj1' : j.val < (dp.val[i.val]).val.length := by rw [← hi2] at hj1; exact hj1
    rw [← hi2]
    exact dp_cell_set_cell dp i j x a b hi1 hj1'

  theorem dp_midp_subList_two (l : List U8) (i : Nat) (hle : i + 2 ≤ l.length)
      (h : l[i]? = l[i + 1]?) : midp (subList l i 2) = 0 := by
    rw [dp_midp_subList_step l i 2 hle (by omega), if_pos (by simpa using h)]
    rw [show subList l (i + 1) 0 = [] from by simp [subList], midp_nil]

  theorem dp_midp_subList_eq (l : List U8) (i len : Nat) (hle : i + len ≤ l.length)
      (h2 : 2 ≤ len) (h : l[i]? = l[i + len - 1]?) :
      midp (subList l i len) = midp (subList l (i+1) (len-2)) := by
    rw [dp_midp_subList_step l i len hle h2, if_pos h]

  theorem dp_midp_subList_ne (l : List U8) (i len : Nat) (hle : i + len ≤ l.length)
      (h2 : 2 ≤ len) (h : ¬ l[i]? = l[i + len - 1]?) :
      midp (subList l i len) =
        1 + min (midp (subList l (i+1) (len-1))) (midp (subList l i (len-1))) := by
    rw [dp_midp_subList_step l i len hle h2, if_neg h]

  theorem dp_spec_vec_index' {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
      dp_spec (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i)
        (fun x => v.val[i.val]? = some x) := by
    rw [alloc.vec.Vec.index_slice_index]
    exact dp_spec_vec_index v i

  theorem dp_usize_ne_two {len : Std.Usize} (h : ¬ len = 2#usize) : len.val ≠ 2 := by
    rintro hc
    exact h (by scalar_tac)

  /-- Everything after the new cell `(start, start + len - 1)` has been written. -/
  theorem dp_write_step (l : List U8) (n len : Nat) {dp dp1 : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {start e : Std.Usize} {v : alloc.vec.Vec Std.I64} {u x : Std.I64}
      (hlen : 2 ≤ len) (hstn : start.val + len ≤ n) (he2 : e.val = start.val + len - 1)
      (hrowslen : dp.val.length = n) (hrowsall : dp_all_rows n dp)
      (hok : dp_ok l n (len - 1) dp) (hstage : dp_stage l n len start.val dp)
      (hrowv : dp.val[start.val]? = some v) (hcolu : v.val[e.val]? = some u)
      (hdp1 : dp1 = dp.set start (v.set e x))
      (hx : x.val = (midp (subList l start.val len) : Int)) :
      dp_rows n dp1 ∧ dp_ok l n (len - 1) dp1 ∧ dp_stage l n len (start.val + 1) dp1 := by
    have hset : ∀ (a b : Nat), dp_cell dp1 a b =
        (if a = start.val ∧ b = e.val then some x else dp_cell dp a b) := by
      intro a b
      rw [hdp1]
      exact dp_cell_set_cell2 dp start v e x u a b hrowv hcolu
    have hvlen : v.val.length = n := dp_rows_row_len n dp ⟨hrowslen, hrowsall⟩ start.val v hrowv
    have hrlen : (v.set e x).val.length = n := by
      rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hvlen
    have hrows1 : dp_all_rows n dp1 := by
      rw [hdp1]; exact dp_all_rows_set n dp start (v.set e x) hrowsall hrlen
    have hrows1len : dp1.val.length = n := by
      rw [hdp1, dp_len_set]; exact hrowslen
    exact dp_inv2_step l n len hlen hstn he2 ⟨hrowslen, hrowsall⟩ hok hstage hrows1 hrows1len hset hx

  /-- At the end of the inner loop the table contains all cells of length `len`. -/
  theorem dp_ok_of_stage (l : List U8) (n len : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (start : Nat) (hlen : 1 ≤ len) (hrows : dp_rows n dp) (hok : dp_ok l n (len - 1) dp)
      (hstage : dp_stage l n len start dp) (hexit : n < start + len) :
      dp_ok l n len dp := by
    intro a b hab hbn hk
    by_cases h1 : b - a + 1 ≤ len - 1
    · exact hok a b hab hbn h1
    · have h2 : b - a + 1 = len := by omega
      have hb : b = a + len - 1 := by omega
      have ha : a < start := by omega
      have han : a + len ≤ n := by omega
      obtain ⟨x, hx, hv⟩ := hstage a ha han
      rw [h2, hb]
      exact ⟨x, hx, hv⟩
  theorem dp_loop1_loop0_body (s : Slice U8) (n len : Std.Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (start : Std.Usize)
      (hnlen : n.val = s.val.length) (hlen : 2 ≤ len.val)
      (hinv : dp_inv2 s.val n.val len.val (dp, start)) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len dp start)
        (dp_cf (fun y => dp_rows n.val y ∧ dp_ok s.val n.val len.val y)
          (fun x' => dp_inv2 s.val n.val len.val x' ∧ n.val - x'.2.val < n.val - start.val)) := by
    unfold dp_inv2 at hinv
    dsimp only at hinv
    obtain ⟨hrows, hok, hstage⟩ := hinv
    obtain ⟨hrowslen, hrowsall⟩ := (dp_rows_iff n.val dp).mp hrows
    intro r h
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body at h
    obtain ⟨i, hi, h⟩ := dp_spec_bind_elim h
    have hi' : i.val = start.val + len.val := by simpa using dp_spec_usize_add start len i hi
    split at h
    ·
      rename_i hb
      have hb' : i.val ≤ n.val := hb
      have hstn : start.val + len.val ≤ n.val := by omega
      have hle : start.val + len.val ≤ s.val.length := by omega
      obtain ⟨e, he, h⟩ := dp_spec_bind_elim h
      have he' : e.val = i.val - 1 := by simpa using dp_spec_usize_sub i 1#usize e he
      have he2 : e.val = start.val + len.val - 1 := by omega
      obtain ⟨i1, hi1, h⟩ := dp_spec_bind_elim h
      obtain ⟨i2, hi2, h⟩ := dp_spec_bind_elim h
      have hi1' : s.val[start.val]? = some i1 := dp_spec_slice_index s start i1 hi1
      have hi2' : s.val[e.val]? = some i2 := dp_spec_slice_index s e i2 hi2
      have hlast : s.val[start.val + len.val - 1]? = some i2 := by rw [← he2]; exact hi2'
      obtain ⟨dp1, hif, h⟩ := dp_spec_bind_elim h
      obtain ⟨start1, hs1, h⟩ := dp_spec_bind_elim h
      have hs1' : start1.val = start.val + 1 := by simpa using dp_spec_usize_add start 1#usize start1 hs1
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      split at hif
      · rename_i heq
        have hEq : s.val[start.val]? = s.val[start.val + len.val - 1]? := by rw [hi1', hlast, heq]
        split at hif
        · -- equal ends, `len = 2`
          rename_i hlen2
          have hlen2v : len.val = 2 := by rw [hlen2]; rfl
          obtain ⟨⟨v, back⟩, hback, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hrowv0, hbackv0⟩ := dp_spec_vec_index_mut dp start (v, back) hback
          obtain ⟨⟨u, back1⟩, hback1, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hcolu0, hback1u0⟩ := dp_spec_vec_index_mut v e (u, back1) hback1
          have hrowv : dp.val[start.val]? = some v := hrowv0
          have hbackv : back = dp.set start := hbackv0
          have hcolu : v.val[e.val]? = some u := hcolu0
          have hback1u : back1 = v.set e := hback1u0
          have h3 : back (back1 0#i64) = dp1 := by
            have h4 := hif
            dsimp only at h4
            exact Result.ok_injective h4
          have hdp1 : dp1 = dp.set start (v.set e 0#i64) := by rw [← h3, hbackv, hback1u]
          have hx : (0#i64).val = (midp (subList s.val start.val len.val) : Int) := by
            have hle2 : start.val + 2 ≤ s.val.length := by omega
            have hEq2 : s.val[start.val]? = s.val[start.val + 1]? := by
              have h' := hEq
              rw [hlen2v] at h'
              rw [show start.val + 2 - 1 = start.val + 1 from by omega] at h'
              exact h'
            have h0 : midp (subList s.val start.val len.val) = 0 := by
              rw [hlen2v]
              exact dp_midp_subList_two s.val start.val hle2 hEq2
            rw [h0]; simp
          have hres := dp_write_step s.val n.val len.val hlen hstn he2 hrowslen hrowsall hok hstage
            hrowv hcolu hdp1 hx
          refine ⟨?_, ?_⟩
          · unfold dp_inv2; dsimp only; rw [hs1']; exact hres
          · rw [hs1']; omega
        · -- equal ends, `len ≠ 2`
          rename_i hlen2
          have hlenne : len.val ≠ 2 := dp_usize_ne_two hlen2
          obtain ⟨i3, hi3, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨v0, hv0, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨i4, hi4, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨i5, hi5, hif⟩ := dp_spec_bind_elim hif
          have hi3' : i3.val = start.val + 1 := by simpa using dp_spec_usize_add start 1#usize i3 hi3
          have hv0' : dp.val[i3.val]? = some v0 := dp_spec_vec_index' dp i3 v0 hv0
          have hi4' : i4.val = e.val - 1 := by simpa using dp_spec_usize_sub e 1#usize i4 hi4
          have hi5' : v0.val[i4.val]? = some i5 := dp_spec_vec_index v0 i4 i5 hi5
          obtain ⟨⟨v, back⟩, hback, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hrowv0, hbackv0⟩ := dp_spec_vec_index_mut dp start (v, back) hback
          obtain ⟨⟨u, back1⟩, hback1, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hcolu0, hback1u0⟩ := dp_spec_vec_index_mut v e (u, back1) hback1
          have hrowv : dp.val[start.val]? = some v := hrowv0
          have hbackv : back = dp.set start := hbackv0
          have hcolu : v.val[e.val]? = some u := hcolu0
          have hback1u : back1 = v.set e := hback1u0
          have h3 : back (back1 i5) = dp1 := by
            have h4 := hif
            dsimp only at h4
            exact Result.ok_injective h4
          have hdp1 : dp1 = dp.set start (v.set e i5) := by rw [← h3, hbackv, hback1u]
          have hcell : dp_cell dp (start.val + 1) (e.val - 1) = some i5 := by
            rw [← hi3', ← hi4']
            exact dp_cell_of_rows dp _ _ v0 i5 hv0' hi5'
          have hv1 : i5.val = (midp (subList s.val (start.val + 1) (len.val - 2)) : Int) := by
            have h := dp_ok_val s.val n.val (len.val - 1) hok (a := start.val + 1) (b := e.val - 1)
              (by omega) (by omega) (by omega) hcell
            rwa [show e.val - 1 - (start.val + 1) + 1 = len.val - 2 from by omega] at h
          have hx : i5.val = (midp (subList s.val start.val len.val) : Int) := by
            rw [dp_midp_subList_eq s.val start.val len.val hle hlen hEq, hv1]
          have hres := dp_write_step s.val n.val len.val hlen hstn he2 hrowslen hrowsall hok hstage
            hrowv hcolu hdp1 hx
          refine ⟨?_, ?_⟩
          · unfold dp_inv2; dsimp only; rw [hs1']; exact hres
          · rw [hs1']; omega
      · -- unequal ends
        rename_i hne
        have hne_l : ¬ s.val[start.val]? = s.val[start.val + len.val - 1]? := by
          intro hc
          rw [hi1', hlast] at hc
          exact hne (Option.some.inj hc)
        obtain ⟨i3, hi3, hif⟩ := dp_spec_bind_elim hif
        obtain ⟨v0, hv0, hif⟩ := dp_spec_bind_elim hif
        obtain ⟨lv, hlv, hif⟩ := dp_spec_bind_elim hif
        obtain ⟨v1, hv1, hif⟩ := dp_spec_bind_elim hif
        obtain ⟨i4, hi4, hif⟩ := dp_spec_bind_elim hif
        obtain ⟨rv, hrv, hif⟩ := dp_spec_bind_elim hif
        have hi3' : i3.val = start.val + 1 := by simpa using dp_spec_usize_add start 1#usize i3 hi3
        have hv0' : dp.val[i3.val]? = some v0 := dp_spec_vec_index' dp i3 v0 hv0
        have hlv1 : v0.val[e.val]? = some lv := dp_spec_vec_index v0 e lv hlv
        have hv1' : dp.val[start.val]? = some v1 := dp_spec_vec_index' dp start v1 hv1
        have hi4' : i4.val = e.val - 1 := by simpa using dp_spec_usize_sub e 1#usize i4 hi4
        have hrv1 : v1.val[i4.val]? = some rv := dp_spec_vec_index v1 i4 rv hrv
        have hlvV : lv.val = (midp (subList s.val (start.val + 1) (len.val - 1)) : Int) := by
          have hc : dp_cell dp (start.val + 1) e.val = some lv := by
            rw [← hi3']
            exact dp_cell_of_rows dp _ _ v0 lv hv0' hlv1
          have h := dp_ok_val s.val n.val (len.val - 1) hok (a := start.val + 1) (b := e.val)
            (by omega) (by omega) (by omega) hc
          rwa [show e.val - (start.val + 1) + 1 = len.val - 1 from by omega] at h
        have hrvV : rv.val = (midp (subList s.val start.val (len.val - 1)) : Int) := by
          have hc : dp_cell dp start.val (e.val - 1) = some rv := by
            rw [← hi4']
            exact dp_cell_of_rows dp _ _ v1 rv hv1' hrv1
          have h := dp_ok_val s.val n.val (len.val - 1) hok (a := start.val) (b := e.val - 1)
            (by omega) (by omega) (by omega) hc
          rwa [show e.val - 1 - start.val + 1 = len.val - 1 from by omega] at h
        split at hif
        · rename_i hlt
          obtain ⟨i5, hi5, hif⟩ := dp_spec_bind_elim hif
          have hi5' : i5.val = lv.val + 1 := by
            have h := dp_spec_i64_add lv 1#i64 i5 hi5
            simpa using h
          obtain ⟨⟨v, back⟩, hback, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hrowv0, hbackv0⟩ := dp_spec_vec_index_mut dp start (v, back) hback
          obtain ⟨⟨u, back1⟩, hback1, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hcolu0, hback1u0⟩ := dp_spec_vec_index_mut v e (u, back1) hback1
          have hrowv : dp.val[start.val]? = some v := hrowv0
          have hbackv : back = dp.set start := hbackv0
          have hcolu : v.val[e.val]? = some u := hcolu0
          have hback1u : back1 = v.set e := hback1u0
          have h3 : back (back1 i5) = dp1 := by
            have h4 := hif
            dsimp only at h4
            exact Result.ok_injective h4
          have hdp1 : dp1 = dp.set start (v.set e i5) := by rw [← h3, hbackv, hback1u]
          have hx : i5.val = (midp (subList s.val start.val len.val) : Int) := by
            rw [dp_midp_subList_ne s.val start.val len.val hle hlen hne_l, hi5', hlvV]
            have hmin : min (midp (subList s.val (start.val + 1) (len.val - 1)))
                (midp (subList s.val start.val (len.val - 1)))
                = midp (subList s.val (start.val + 1) (len.val - 1)) := by
              have hlt' : lv.val < rv.val := hlt
              rw [hlvV, hrvV] at hlt'
              omega
            rw [hmin]
            push_cast
            ring
          have hres := dp_write_step s.val n.val len.val hlen hstn he2 hrowslen hrowsall hok hstage
            hrowv hcolu hdp1 hx
          refine ⟨?_, ?_⟩
          · unfold dp_inv2; dsimp only; rw [hs1']; exact hres
          · rw [hs1']; omega
        · rename_i hge
          obtain ⟨i5, hi5, hif⟩ := dp_spec_bind_elim hif
          have hi5' : i5.val = rv.val + 1 := by
            have h := dp_spec_i64_add rv 1#i64 i5 hi5
            simpa using h
          obtain ⟨⟨v, back⟩, hback, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hrowv0, hbackv0⟩ := dp_spec_vec_index_mut dp start (v, back) hback
          obtain ⟨⟨u, back1⟩, hback1, hif⟩ := dp_spec_bind_elim hif
          obtain ⟨hcolu0, hback1u0⟩ := dp_spec_vec_index_mut v e (u, back1) hback1
          have hrowv : dp.val[start.val]? = some v := hrowv0
          have hbackv : back = dp.set start := hbackv0
          have hcolu : v.val[e.val]? = some u := hcolu0
          have hback1u : back1 = v.set e := hback1u0
          have h3 : back (back1 i5) = dp1 := by
            have h4 := hif
            dsimp only at h4
            exact Result.ok_injective h4
          have hdp1 : dp1 = dp.set start (v.set e i5) := by rw [← h3, hbackv, hback1u]
          have hx : i5.val = (midp (subList s.val start.val len.val) : Int) := by
            rw [dp_midp_subList_ne s.val start.val len.val hle hlen hne_l, hi5', hrvV]
            have hmin : min (midp (subList s.val (start.val + 1) (len.val - 1)))
                (midp (subList s.val start.val (len.val - 1)))
                = midp (subList s.val start.val (len.val - 1)) := by
              have hge' : ¬ lv.val < rv.val := hge
              rw [hlvV, hrvV] at hge'
              omega
            rw [hmin]
            push_cast
            ring
          have hres := dp_write_step s.val n.val len.val hlen hstn he2 hrowslen hrowsall hok hstage
            hrowv hcolu hdp1 hx
          refine ⟨?_, ?_⟩
          · unfold dp_inv2; dsimp only; rw [hs1']; exact hres
          · rw [hs1']; omega
    · -- the loop terminates: the whole table is filled
      rename_i hb
      have hb' : ¬ i.val ≤ n.val := hb
      have hexit : n.val < start.val + len.val := by omega
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      refine ⟨⟨hrowslen, hrowsall⟩, ?_⟩
      exact dp_ok_of_stage s.val n.val len.val dp start.val (by omega) ⟨hrowslen, hrowsall⟩ hok hstage hexit
  theorem dp_midp_of_le_one (l : List U8) (h : l.length ≤ 1) : midp l = 0 := by
    rw [midp]
    simp [h]

  theorem dp_ok_one (l : List U8) (n : Nat) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hrows : dp_rows n dp) (hzero : ∀ r ∈ dp.val, ∀ x ∈ r.val, x = 0#i64) :
      dp_ok l n 1 dp := by
    intro a b hab hbn hk
    have hab' : a = b := by omega
    subst hab'
    obtain ⟨h1, h2⟩ := (dp_rows_iff n dp).mp hrows
    have ha : a < dp.val.length := by omega
    have hb : a < (dp.val[a]).val.length := by
      have := h2 _ (List.getElem_mem ha); omega
    have hz : (dp.val[a]).val[a] = 0#i64 := hzero _ (List.getElem_mem ha) _ (List.getElem_mem hb)
    refine ⟨0#i64, dp_cell_of_getElem dp a a 0#i64 ha hb hz, ?_⟩
    have hab2 : a - a + 1 = 1 := by omega
    rw [hab2]
    have hm : midp (subList l a 1) = 0 := dp_midp_of_le_one _ (by rw [subList_length]; omega)
    rw [hm]
    simp

  theorem dp_loop1_loop0_spec (s : Slice U8) (n len : Std.Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (start : Std.Usize)
      (hnlen : n.val = s.val.length) (hlen : 2 ≤ len.val)
      (hinv : dp_inv2 s.val n.val len.val (dp, start)) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start)
        (fun y => dp_rows n.val y ∧ dp_ok s.val n.val len.val y) := by
    refine dp_loop_ok (α := alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (measure := fun st => n.val - st.2.val) (inv := dp_inv2 s.val n.val len.val)
      (post := fun y => dp_rows n.val y ∧ dp_ok s.val n.val len.val y)
      (body := fun st => Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len st.1 st.2)
      ?_ (dp, start) hinv
    · rintro ⟨dp0, st0⟩ hinv0
      dsimp only
      exact dp_loop1_loop0_body s n len dp0 st0 hnlen hlen hinv0

  /-- Loop state invariant of `min_insertions_loop1`: all cells of length `< len` are filled. -/
  def dp_inv3 (s : Slice U8) (n : Std.Usize)
      (st : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize) : Prop :=
    2 ≤ st.2.val ∧ st.2.val ≤ n.val + 1 ∧ dp_rows n.val st.1 ∧
      dp_ok s.val n.val (st.2.val - 1) st.1

  theorem dp_loop1_body (s : Slice U8) (n : Std.Usize) (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (len : Std.Usize) (hnlen : n.val = s.val.length) (hinv : dp_inv3 s n (dp, len)) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop1.body s n dp len)
        (dp_cf (fun y => dp_rows n.val y ∧ dp_ok s.val n.val n.val y)
          (fun x' => dp_inv3 s n x' ∧ n.val + 1 - x'.2.val < n.val + 1 - len.val)) := by
    unfold dp_inv3 at hinv
    dsimp only at hinv
    obtain ⟨hlen2, hlenle, hrows, hok⟩ := hinv
    intro r h
    unfold Aegis.MinInsertions.min_insertions_loop1.body at h
    split at h
    · rename_i hb
      have hb' : len.val ≤ n.val := hb
      obtain ⟨dp1, hdp1, h⟩ := dp_spec_bind_elim h
      obtain ⟨len1, hlen1, h⟩ := dp_spec_bind_elim h
      have hlen1' : len1.val = len.val + 1 := by simpa using dp_spec_usize_add len 1#usize len1 hlen1
      have hstart : dp_stage s.val n.val len.val 0 dp := by
        intro a ha
        omega
      have hinv2 : dp_inv2 s.val n.val len.val (dp, 0#usize) := by
        unfold dp_inv2
        dsimp only
        exact ⟨hrows, hok, hstart⟩
      have hres := dp_loop1_loop0_spec s n len dp 0#usize hnlen hlen2 hinv2 dp1 hdp1
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      refine ⟨?_, ?_⟩
      · unfold dp_inv3
        dsimp only
        refine ⟨by omega, by omega, hres.1, ?_⟩
        rw [hlen1']
        simpa using hres.2
      · rw [hlen1']
        omega
    · rename_i hb
      have hb' : ¬ len.val ≤ n.val := hb
      simp only [Result.ok.injEq] at h
      subst h
      simp only [dp_cf]
      exact ⟨hrows, dp_ok_mono s.val n.val (L := n.val) (L' := len.val - 1) (by omega) hok⟩

  theorem dp_loop1_spec (s : Slice U8) (n : Std.Usize)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hn : 2 ≤ n.val)
      (hnlen : n.val = s.val.length)
      (hdp : dp_rows n.val dp ∧ ∀ r ∈ dp.val, ∀ x ∈ r.val, x = 0#i64) :
      dp_spec (Aegis.MinInsertions.min_insertions_loop1 s n dp 2#usize)
        (fun y => dp_rows n.val y ∧ dp_ok s.val n.val n.val y) := by
    obtain ⟨hrows, hzero⟩ := hdp
    refine dp_loop_ok (α := alloc.vec.Vec (alloc.vec.Vec Std.I64) × Std.Usize)
      (β := alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (measure := fun st => n.val + 1 - st.2.val) (inv := dp_inv3 s n)
      (post := fun y => dp_rows n.val y ∧ dp_ok s.val n.val n.val y)
      (body := fun st => Aegis.MinInsertions.min_insertions_loop1.body s n st.1 st.2)
      ?_ (dp, 2#usize) ?_
    · rintro ⟨dp0, len0⟩ hinv
      dsimp only
      simpa using dp_loop1_body s n dp0 len0 hnlen hinv
    · unfold dp_inv3
      dsimp only
      have h2v : (2#usize).val = 2 := by simp
      refine ⟨by omega, by omega, hrows, ?_⟩
      rw [h2v]
      exact dp_ok_one s.val n.val dp hrows hzero

  theorem dp_min_insertions_val (s : Slice U8) (r : Std.I64)
      (h : Aegis.MinInsertions.min_insertions s = ok r) : r.val = (midp s.val : Int) := by
    unfold Aegis.MinInsertions.min_insertions at h
    dsimp only at h
    split at h
    · rename_i hb
      simp only [Result.ok.injEq] at h
      subst h
      have hlen : s.val.length ≤ 1 := by
        have h1 : (Slice.len s).val ≤ (1#usize).val := hb
        rw [Slice.len_val] at h1
        simpa using h1
      rw [dp_midp_of_le_one s.val hlen]
      simp
    · rename_i hb
      have hn : 2 ≤ (Slice.len s).val := by
        have h1 : ¬ (Slice.len s).val ≤ (1#usize).val := hb
        have h2 : (1#usize).val = 1 := by simp
        rw [h2] at h1
        omega
      obtain ⟨dp0, hd0, h⟩ := dp_spec_bind_elim h
      obtain ⟨dp1, hd1, h⟩ := dp_spec_bind_elim h
      obtain ⟨v, hv, h⟩ := dp_spec_bind_elim h
      obtain ⟨ii, hii, h⟩ := dp_spec_bind_elim h
      have hnlen : (Slice.len s).val = s.val.length := by rw [Slice.len_val]
      have hz0 : dp_rows (Slice.len s).val dp0 ∧ ∀ r ∈ dp0.val, ∀ x ∈ r.val, x = 0#i64 :=
        dp_loop0_spec (Slice.len s) dp0 hd0
      have hz1 : dp_rows (Slice.len s).val dp1 ∧
          dp_ok s.val (Slice.len s).val (Slice.len s).val dp1 :=
        dp_loop1_spec s (Slice.len s) dp0 hn hnlen hz0 dp1 hd1
      have hv' : dp1.val[(0#usize).val]? = some v := dp_spec_vec_index' dp1 0#usize v hv
      have hfin : v.val[ii.val]? = some r := dp_spec_vec_index' v ii r h
      have hii' : ii.val = (Slice.len s).val - 1 := by
        have := dp_spec_usize_sub (Slice.len s) 1#usize ii hii
        simpa using this
      have hcell : dp_cell dp1 (0#usize).val ii.val = some r :=
        dp_cell_of_rows dp1 _ _ v r hv' hfin
      rw [hii'] at hcell
      have hval := dp_ok_val s.val (Slice.len s).val (Slice.len s).val hz1.2
        (a := 0) (b := (Slice.len s).val - 1) (by omega) (by omega) (by omega) hcell
      rw [hval]
      have hsub : subList s.val 0 ((Slice.len s).val - 1 - 0 + 1) = s.val := by
        rw [subList_zero]
        omega
      rw [hsub]

  /-- **S1 (main, functional).** When `min_insertions s` returns `r`, `r` is the least
  nonnegative `k` such that `s` can be extended to a palindrome by inserting `k` bytes. -/
  theorem spec_1 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧
          hasPalindromicSupersequence s.val r.val.toNat ∧
            (∀ k, hasPalindromicSupersequence s.val k → r.val.toNat ≤ k) := by
    intro r h
    have hv : r.val = (midp s.val : Int) := dp_min_insertions_val s r h
    have ht : r.val.toNat = midp s.val := by rw [hv]; exact Int.toNat_natCast _
    refine ⟨?_, ?_, ?_⟩
    · rw [hv]; exact Int.natCast_nonneg _
    · rw [ht]; exact mA_hasPSS_midp s.val
    · intro k hk; rw [ht]; exact mB_hasPSS_le_midp s.val k hk

  end AegisSpec.MinInsertions
