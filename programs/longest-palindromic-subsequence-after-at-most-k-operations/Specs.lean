import Aegis.LongestPalindromicSubsequence.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindromicSubsequence.longest_palindromic_subsequence`

LeetCode problem `longest-palindromic-subsequence-after-at-most-k-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.LongestPalindromicSubsequence

  open Aegis.LongestPalindromicSubsequence

  def IsLower (c : Std.U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

  def AllLower (s : Slice Std.U8) : Prop :=
    ∀ (i : ℕ) (h : i < s.val.length), IsLower (s.val.get ⟨i, h⟩)

  def lowerVal (c : Std.U8) : ℕ := c.val - 97

  def byteDist (c d : Std.U8) : ℕ :=
    let delta := if lowerVal c ≤ lowerVal d then lowerVal d - lowerVal c else lowerVal c - lowerVal d
    min delta (26 - delta)

  def StrictIncr {L n : ℕ} (i : Fin L → Fin n) : Prop :=
    ∀ a b : Fin L, a < b → (i a).val < (i b).val

  def halfIdx {L : ℕ} (t : Fin (L / 2)) : Fin L :=
    ⟨t.val, by have h := t.isLt; have h' := Nat.div_le_self L 2; omega⟩

  def mirrorIdx {L : ℕ} (t : Fin (L / 2)) : Fin L :=
    ⟨L - 1 - t.val, by have h := t.isLt; have h' := Nat.div_le_self L 2; omega⟩

  def pcost (s : Slice Std.U8) (L : ℕ) (i : Fin L → Fin s.val.length) : ℕ :=
    ∑ t : Fin (L / 2), byteDist (s.val.get (i (halfIdx t))) (s.val.get (i (mirrorIdx t)))

  def fullCost (s : Slice Std.U8) : ℕ :=
    ∑ t : Fin (s.val.length / 2),
      byteDist (s.val.get (halfIdx t)) (s.val.get (mirrorIdx t))

  def mkSlice (l : List Std.U8) (h : l.length ≤ Usize.max) : Slice Std.U8 :=
    ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

  def revSlice (s : Slice Std.U8) : Slice Std.U8 :=
    mkSlice s.val.reverse (by
      have hb := s.bound
      have hl : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
      simp only [List.length_reverse]
      omega)

  def shiftByte (c : Std.U8) : Std.U8 :=
    ⟨BitVec.ofNat 8 (97 + (lowerVal c + 1) % 26)⟩

  def shiftSlice (s : Slice Std.U8) : Slice Std.U8 :=
    mkSlice (s.val.map shiftByte) (by
      have hb := s.bound
      have hl : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
      simp only [List.length_map]
      omega)

  def subSlice (s : Slice Std.U8) (l u : ℕ) : Slice Std.U8 :=
    mkSlice ((s.val.drop l).take (u + 1 - l)) (by
      have hb := s.bound
      have hl : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
      have hsub : ((s.val.drop l).take (u + 1 - l)).Sublist s.val :=
        (List.take_sublist (u + 1 - l) (s.val.drop l)).trans (List.drop_sublist l s.val)
      have hlen : ((s.val.drop l).take (u + 1 - l)).length ≤ s.val.length :=
        hsub.length_le
      omega)

  /-- For a lowercase byte c let val(c) = code(c) - 97. For lowercase bytes c,d let dist(c,d) = min(|val(c)-val(d)|, 26 - |val(c)-val(d)|). For an integer L with 1 <= L <= len(s) and indices i_0 < i_1 < ... < i_{L-1} in [0,len(s)), define pcost(i_0,...,i_{L-1}) = sum_{t=0}^{floor(L/2)-1} dist(s[i_t], s[i_{L-1-t}]). The function returns a result r, and r is the largest such L for which there exist indices i_0 < ... < i_{L-1} satisfying pcost(i_0,...,i_{L-1}) <= k.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_1
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∃ r : Std.I64,
        longest_palindromic_subsequence s k = ok r ∧
        (∀ (L : ℕ) (i : Fin L → Fin s.val.length),
          1 ≤ L → StrictIncr i → (pcost s L i : ℤ) ≤ k.val → (L : ℤ) ≤ r.val) ∧
        (∃ i : Fin r.val.toNat → Fin s.val.length,
          StrictIncr i ∧ (pcost s r.val.toNat i : ℤ) ≤ k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∃ r : Std.I64,
          longest_palindromic_subsequence s k = ok r ∧
          (∀ (L : ℕ) (i : Fin L → Fin s.val.length),
            1 ≤ L → StrictIncr i → (pcost s L i : ℤ) ≤ k.val → (L : ℤ) ≤ r.val) ∧
          (∃ i : Fin r.val.toNat → Fin s.val.length,
            StrictIncr i ∧ (pcost s r.val.toNat i : ℤ) ≤ k.val)) := by
    sorry

  /-- The function returns a result r (it does not fail by overflow, out-of-bounds access, or panic).
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_2
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∃ r : Std.I64, longest_palindromic_subsequence s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∃ r : Std.I64, longest_palindromic_subsequence s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(s).
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_3
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
    sorry

  /-- For a lowercase byte c let val(c) = code(c) - 97, and for lowercase bytes c,d let dist(c,d) = min(|val(c)-val(d)|, 26 - |val(c)-val(d)|). Let W = sum_{t=0}^{floor(len(s)/2)-1} dist(s[t], s[len(s)-1-t]). Whenever the function returns a result r, r = len(s) if and only if W <= k.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_4
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        (r.val = (s.val.length : ℤ) ↔ (fullCost s : ℤ) ≤ k.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          (r.val = (s.val.length : ℤ) ↔ (fullCost s : ℤ) ≤ k.val)) := by
    sorry

  /-- For a lowercase byte c let val(c) = code(c) - 97, and for lowercase bytes c,d let dist(c,d) = min(|val(c)-val(d)|, 26 - |val(c)-val(d)|). Whenever the function returns a result r, r = 1 if and only if for every pair of indices i,j with 0 <= i < j < len(s), dist(s[i], s[j]) > k.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_5
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        (r.val = 1 ↔
          ∀ i j : Fin s.val.length, i < j → k.val < (byteDist (s.val.get i) (s.val.get j) : ℤ)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          (r.val = 1 ↔
            ∀ i j : Fin s.val.length, i < j → k.val < (byteDist (s.val.get i) (s.val.get j) : ℤ))) := by
    sorry

  /-- For a lowercase byte c let val(c) = code(c) - 97, and for lowercase bytes c,d let dist(c,d) = min(|val(c)-val(d)|, 26 - |val(c)-val(d)|). Whenever the function returns a result r, there exist indices i_0 < i_1 < ... < i_{r-1} in [0,len(s)) such that sum_{t=0}^{floor(r/2)-1} dist(s[i_t], s[i_{r-1-t}]) <= k.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_6
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        ∃ i : Fin r.val.toNat → Fin s.val.length,
          StrictIncr i ∧ (pcost s r.val.toNat i : ℤ) ≤ k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          ∃ i : Fin r.val.toNat → Fin s.val.length,
            StrictIncr i ∧ (pcost s r.val.toNat i : ℤ) ≤ k.val) := by
    sorry

  /-- For a lowercase byte c let val(c) = code(c) - 97, and for lowercase bytes c,d let dist(c,d) = min(|val(c)-val(d)|, 26 - |val(c)-val(d)|). Whenever the function returns a result r, for every integer L with r < L <= len(s) and every choice of indices i_0 < i_1 < ... < i_{L-1} in [0,len(s)), we have sum_{t=0}^{floor(L/2)-1} dist(s[i_t], s[i_{L-1-t}]) > k.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_7
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        ∀ (L : ℕ) (i : Fin L → Fin s.val.length),
          r.val < (L : ℤ) → L ≤ s.val.length → StrictIncr i → k.val < (pcost s L i : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          ∀ (L : ℕ) (i : Fin L → Fin s.val.length),
            r.val < (L : ℤ) → L ≤ s.val.length → StrictIncr i → k.val < (pcost s L i : ℤ)) := by
    sorry

  /-- Let r1 be the result returned by the function on input (s,k1), and let r2 be the result returned on input (s,k2). Whenever both calls return, r1 <= r2.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, and k1,k2 are i64 values with 1 <= k1 <= k2 <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_8
      (s : Slice Std.U8) (k1 k2 : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r1 r2 : Std.I64,
        longest_palindromic_subsequence s k1 = ok r1 →
        longest_palindromic_subsequence s k2 = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 200)
        (hlower : AllLower s), ∀ r1 r2 : Std.I64,
          longest_palindromic_subsequence s k1 = ok r1 →
          longest_palindromic_subsequence s k2 = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Let rev(s) be the byte array of length len(s) with rev(s)[i] = s[len(s)-1-i] for 0 <= i < len(s). The value returned by the function on (s,k) equals the value returned on (rev(s),k) whenever both calls return.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_9
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r1 r2 : Std.I64,
        longest_palindromic_subsequence s k = ok r1 →
        longest_palindromic_subsequence (revSlice s) k = ok r2 →
        r1.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r1 r2 : Std.I64,
          longest_palindromic_subsequence s k = ok r1 →
          longest_palindromic_subsequence (revSlice s) k = ok r2 →
          r1.val = r2.val) := by
    sorry

  /-- Let val(c) = code(c) - 97 for a lowercase byte c, and let shift(s) be the byte array with shift(s)[i] = 'a' + ((val(s[i]) + 1) mod 26) for 0 <= i < len(s). The value returned by the function on (s,k) equals the value returned on (shift(s),k) whenever both calls return.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_10
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r1 r2 : Std.I64,
        longest_palindromic_subsequence s k = ok r1 →
        longest_palindromic_subsequence (shiftSlice s) k = ok r2 →
        r1.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r1 r2 : Std.I64,
          longest_palindromic_subsequence s k = ok r1 →
          longest_palindromic_subsequence (shiftSlice s) k = ok r2 →
          r1.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, if k >= 13 * floor(len(s)/2), then r = len(s).
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122). -/
  theorem spec_11
      (s : Slice Std.U8) (k : Std.I64)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s) :
      ∀ r : Std.I64,
        longest_palindromic_subsequence s k = ok r →
        ((13 * (s.val.length / 2) : ℕ) : ℤ) ≤ k.val → r.val = (s.val.length : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s), ∀ r : Std.I64,
          longest_palindromic_subsequence s k = ok r →
          ((13 * (s.val.length / 2) : ℕ) : ℤ) ≤ k.val → r.val = (s.val.length : ℤ)) := by
    sorry

  /-- Let t be the slice consisting of s[l], s[l+1], ..., s[u]. Let r_t be the result returned by the function on input (t,k), and let r_s be the result returned on input (s,k). Whenever both calls return, r_t <= r_s.
    Preconditions: s is a slice of bytes with 1 <= len(s) <= 200, k is an i64 with 1 <= k <= 200, for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter ('a'..'z', codes 97..122), and 0 <= l <= u < len(s). -/
  theorem spec_12
      (s : Slice Std.U8) (k : Std.I64) (l u : ℕ)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
      (hlower : AllLower s)
      (hlu : l ≤ u) (hu : u < s.val.length) :
      ∀ rt rs : Std.I64,
        longest_palindromic_subsequence (subSlice s l u) k = ok rt →
        longest_palindromic_subsequence s k = ok rs →
        rt.val ≤ rs.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (l u : ℕ)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 200)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 200)
        (hlower : AllLower s)
        (hlu : l ≤ u) (hu : u < s.val.length), ∀ rt rs : Std.I64,
          longest_palindromic_subsequence (subSlice s l u) k = ok rt →
          longest_palindromic_subsequence s k = ok rs →
          rt.val ≤ rs.val) := by
    sorry

  end AegisSpec.LongestPalindromicSubsequence
