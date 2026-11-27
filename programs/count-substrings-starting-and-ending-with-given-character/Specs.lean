import Aegis.CountSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountSubstrings.count_substrings`

LeetCode problem `count-substrings-starting-and-ending-with-given-character`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountSubstrings

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def countOcc (l : List Std.U8) (target : Std.U8) : ℕ :=
    l.countP (fun b => b = target)

  def numPairs (l : List Std.U8) (target : Std.U8) : ℕ :=
    ((List.range l.length).product (List.range l.length)).countP
      (fun p => p.1 ≤ p.2 ∧ l[p.1]? = some target ∧ l[p.2]? = some target)

  def revSlice (s : Slice Std.U8) : Slice Std.U8 :=
    { leng := s.val.reverse.length
      list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
      bound := by
        rw [List.length_reverse]
        exact (Aeneas.Data.ListN.ListN_length s.list).trans_le s.bound }

  theorem revSlice_val (s : Slice Std.U8) : (revSlice s).val = s.val.reverse :=
    Aeneas.Data.ListN.ListN.from_to_inverse

  /-- The function returns a result r and r equals the number of pairs (i, j) of indices such that 0 <= i <= j < len(s), s[i] = c[0], and s[j] = c[0]. Equivalently, r is the number of non-empty contiguous substrings s[i..j] (inclusive) whose first byte and last byte are both c[0].
    Preconditions: len(c) = 1, len(s) <= 100000, and every byte of s and c[0] is a lowercase English letter. No lower bound is imposed on len(s), so len(s) may be 0. -/
  theorem spec_1 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000)
      (hs_lower : ∀ b ∈ s.val, IsLowerByte b)
      (hc_lower : ∀ b ∈ c.val, IsLowerByte b) :
      ∃ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r ∧
          r.val = (numPairs s.val (c.val[0]'(by omega)) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000)
        (hs_lower : ∀ b ∈ s.val, IsLowerByte b)
        (hc_lower : ∀ b ∈ c.val, IsLowerByte b), ∃ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r ∧
            r.val = (numPairs s.val (c.val[0]'(by omega)) : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_2 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      ∃ r : Std.I64, Aegis.CountSubstrings.count_substrings s c = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), ∃ r : Std.I64, Aegis.CountSubstrings.count_substrings s c = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_3 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      ∀ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), ∀ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(s)*(len(s)+1)/2.
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_4 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      ∀ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r →
          r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), ∀ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r →
            r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Let k be the number of indices i with 0 <= i < len(s) and s[i] = c[0]. Whenever the function returns a result r, r >= k.
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_5 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      let k := countOcc s.val (c.val[0]'(by omega))
      ∀ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), let k := countOcc s.val (c.val[0]'(by omega))
        ∀ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r → (k : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(c) = 1 and len(s) = 0. -/
  theorem spec_6 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_len : s.val.length = 0) :
      ∃ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_len : s.val.length = 0), ∃ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: len(c) = 1, len(s) = 1, and s[0] = c[0]. -/
  theorem spec_7 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_len : s.val.length = 1)
      (hs_eq : s.val[0]'(by omega) = c.val[0]'(by omega)) :
      ∃ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_len : s.val.length = 1)
        (hs_eq : s.val[0]'(by omega) = c.val[0]'(by omega)), ∃ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = n*(n+1)/2.
    Preconditions: len(c) = 1, len(s) = n with n <= 100000, and for every i with 0 <= i < n, s[i] = c[0]. -/
  theorem spec_8 (s c : Slice Std.U8) (n : ℕ)
      (hc_len : c.val.length = 1)
      (hn_max : n ≤ 100000)
      (hs_len : s.val.length = n)
      (hs_all : ∀ i : ℕ, (hi : i < n) → s.val[i]'(by omega) = c.val[0]'(by omega)) :
      ∃ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r ∧
          r.val = ((n * (n + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s c : Slice Std.U8) (n : ℕ)
        (hc_len : c.val.length = 1)
        (hn_max : n ≤ 100000)
        (hs_len : s.val.length = n)
        (hs_all : ∀ i : ℕ, (hi : i < n) → s.val[i]'(by omega) = c.val[0]'(by omega)), ∃ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r ∧
            r.val = ((n * (n + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Let k be the number of indices i with 0 <= i < len(s) and s[i] = c[0]. The function returns a result r and r = k*(k+1)/2.
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_9 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      let k := countOcc s.val (c.val[0]'(by omega))
      ∃ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r ∧
          r.val = ((k * (k + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), let k := countOcc s.val (c.val[0]'(by omega))
        ∃ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r ∧
            r.val = ((k * (k + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever count_substrings(s, c) returns r_s and count_substrings(t, c) returns r_t, we have r_s = r_t.
    Preconditions: len(c) = 1, len(s) = len(t) <= 100000, and for every i with 0 <= i < len(s), s[i] = c[0] iff t[i] = c[0]. -/
  theorem spec_10 (s t c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_len : s.val.length = t.val.length)
      (hs_max : s.val.length ≤ 100000)
      (hsame : ∀ i : ℕ, (hi : i < s.val.length) →
        (s.val[i]'(by omega) = c.val[0]'(by omega) ↔
          t.val[i]'(by omega) = c.val[0]'(by omega))) :
      ∀ r_s r_t : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r_s →
          Aegis.CountSubstrings.count_substrings t c = ok r_t → r_s.val = r_t.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_len : s.val.length = t.val.length)
        (hs_max : s.val.length ≤ 100000)
        (hsame : ∀ i : ℕ, (hi : i < s.val.length) →
          (s.val[i]'(by omega) = c.val[0]'(by omega) ↔
            t.val[i]'(by omega) = c.val[0]'(by omega))), ∀ r_s r_t : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r_s →
            Aegis.CountSubstrings.count_substrings t c = ok r_t → r_s.val = r_t.val) := by
    sorry

  /-- Whenever count_substrings(s, c) returns r and count_substrings(rev(s), c) returns r_rev, we have r = r_rev.
    Preconditions: len(c) = 1 and len(s) <= 100000. Let rev(s) be the slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for every 0 <= i < len(s). -/
  theorem spec_11 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      ∀ r r_rev : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r →
          Aegis.CountSubstrings.count_substrings (revSlice s) c = ok r_rev →
            r.val = r_rev.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), ∀ r r_rev : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r →
            Aegis.CountSubstrings.count_substrings (revSlice s) c = ok r_rev →
              r.val = r_rev.val) := by
    sorry

  /-- Whenever count_substrings(s, c) returns r_s and count_substrings(t, c) returns r_t, we have r_s <= r_t.
    Preconditions: len(c) = 1, len(s) <= len(t) <= 100000, and s is a prefix of t, i.e., for every i with 0 <= i < len(s), s[i] = t[i]. -/
  theorem spec_12 (s t c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_len : s.val.length ≤ t.val.length)
      (ht_max : t.val.length ≤ 100000)
      (hprefix : ∀ i : ℕ, (hi : i < s.val.length) →
        s.val[i]'(by omega) = t.val[i]'(by omega)) :
      ∀ r_s r_t : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r_s →
          Aegis.CountSubstrings.count_substrings t c = ok r_t → r_s.val ≤ r_t.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_len : s.val.length ≤ t.val.length)
        (ht_max : t.val.length ≤ 100000)
        (hprefix : ∀ i : ℕ, (hi : i < s.val.length) →
          s.val[i]'(by omega) = t.val[i]'(by omega)), ∀ r_s r_t : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r_s →
            Aegis.CountSubstrings.count_substrings t c = ok r_t → r_s.val ≤ r_t.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i and j such that 0 <= i <= j < len(s), s[i] = c[0], and s[j] = c[0].
    Preconditions: len(c) = 1 and len(s) <= 100000. -/
  theorem spec_13 (s c : Slice Std.U8)
      (hc_len : c.val.length = 1)
      (hs_max : s.val.length ≤ 100000) :
      ∀ r : Std.I64,
        Aegis.CountSubstrings.count_substrings s c = ok r → 0 < r.val →
          ∃ (i j : ℕ) (hij : i ≤ j) (hj : j < s.val.length),
            s.val[i]'(by omega) = c.val[0]'(by omega) ∧
              s.val[j]'(by omega) = c.val[0]'(by omega) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s c : Slice Std.U8)
        (hc_len : c.val.length = 1)
        (hs_max : s.val.length ≤ 100000), ∀ r : Std.I64,
          Aegis.CountSubstrings.count_substrings s c = ok r → 0 < r.val →
            ∃ (i j : ℕ) (hij : i ≤ j) (hj : j < s.val.length),
              s.val[i]'(by omega) = c.val[0]'(by omega) ∧
                s.val[j]'(by omega) = c.val[0]'(by omega)) := by
    sorry

  end AegisSpec.CountSubstrings
