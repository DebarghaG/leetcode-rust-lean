import Aegis.LengthOfLongestSubstringKDistinct.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLongestSubstringKDistinct.length_of_longest_substring_k_distinct`

LeetCode problem `longest-substring-with-at-most-k-distinct-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LengthOfLongestSubstringKDistinct (length_of_longest_substring_k_distinct)

  namespace AegisSpec.LengthOfLongestSubstringKDistinct

  open Aeneas Aeneas.Std Result

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def window (l : List ℕ) (i j : ℕ) : List ℕ := (l.drop i).take (j - i)

  def windowDistinct (l : List ℕ) (i j : ℕ) : ℕ := (window l i j).dedup.length

  def numDistinct (l : List ℕ) : ℕ := l.dedup.length

  def maxWindowLen (l : List ℕ) (k : ℕ) : ℕ :=
    (Finset.range (l.length + 1)).sup fun i =>
      (Finset.range (l.length + 1)).sup fun j =>
        if i ≤ j ∧ windowDistinct l i j ≤ k then j - i else 0

  def IsSubslice (t s : Slice Std.U8) : Prop :=
    ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧ bytes t = window (bytes s) i j

  @[reducible] def windowAllEqual (l : List ℕ) (i j : ℕ) : Prop :=
    (window l i j).dedup.length ≤ 1

  def maxConstRunLen (l : List ℕ) : ℕ :=
    (Finset.range (l.length + 1)).sup fun i =>
      (Finset.range (l.length + 1)).sup fun j =>
        if i ≤ j ∧ windowAllEqual l i j then j - i else 0

  /-- Let A(s,k) be the maximum length of a contiguous substring of s whose set of byte values has cardinality at most k; the empty substring is allowed and has length 0, so A(s,k) is always defined. The function returns a result r and r = A(s,k). Equivalently, r is the largest integer such that there exist indices 0 <= i <= j <= len(s) with j - i = r and the set {s[t] : i <= t < j} has at most k elements, and every 0 <= i <= j <= len(s) with |{s[t] : i <= t < j}| <= k satisfies j - i <= r.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∃ r : Std.I64,
        length_of_longest_substring_k_distinct s k = ok r ∧
        r.val = ((maxWindowLen (bytes s) k.val.toNat : ℕ) : Int) ∧
        (∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
          (j : Int) - (i : Int) = r.val ∧
          windowDistinct (bytes s) i j ≤ k.val.toNat) ∧
        (∀ i j : ℕ, i ≤ j → j ≤ s.val.length →
          windowDistinct (bytes s) i j ≤ k.val.toNat →
          (j : Int) - (i : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∃ r : Std.I64,
          length_of_longest_substring_k_distinct s k = ok r ∧
          r.val = ((maxWindowLen (bytes s) k.val.toNat : ℕ) : Int) ∧
          (∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
            (j : Int) - (i : Int) = r.val ∧
            windowDistinct (bytes s) i j ≤ k.val.toNat) ∧
          (∀ i j : ℕ, i ≤ j → j ≤ s.val.length →
            windowDistinct (bytes s) i j ≤ k.val.toNat →
            (j : Int) - (i : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∃ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∃ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        0 ≤ r.val ∧ r.val ≤ ((s.val.length : ℕ) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          0 ≤ r.val ∧ r.val ≤ ((s.val.length : ℕ) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices 0 <= i <= j <= len(s) such that j - i = r and the contiguous substring s[i..j) contains at most k distinct byte values.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
          (j : Int) - (i : Int) = r.val ∧
          windowDistinct (bytes s) i j ≤ k.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
            (j : Int) - (i : Int) = r.val ∧
            windowDistinct (bytes s) i j ≤ k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices 0 <= i <= j <= len(s) such that the contiguous substring s[i..j) contains at most k distinct byte values, we have j - i <= r.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        ∀ i j : ℕ, i ≤ j → j ≤ s.val.length →
          windowDistinct (bytes s) i j ≤ k.val.toNat →
          (j : Int) - (i : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          ∀ i j : ℕ, i ≤ j → j ≤ s.val.length →
            windowDistinct (bytes s) i j ≤ k.val.toNat →
            (j : Int) - (i : Int) ≤ r.val) := by
    sorry

  /-- Let D(s) be the number of distinct byte values appearing in s (D(s)=0 when len(s)=0). Whenever the function returns a result r, r = len(s) if and only if D(s) <= k.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        (r.val = ((s.val.length : ℕ) : Int) ↔ numDistinct (bytes s) ≤ k.val.toNat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          (r.val = ((s.val.length : ℕ) : Int) ↔ numDistinct (bytes s) ≤ k.val.toNat)) := by
    sorry

  /-- For every byte slice s and integers k1,k2 satisfying the preconditions, if the call on (s,k1) returns r1 and the call on (s,k2) returns r2, then r1 <= r2.
    Preconditions: len(s) <= 50000 and 0 <= k1 <= k2 <= 50. -/
  theorem spec_7 (s : Slice Std.U8) (k1 k2 : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk1_low : 0 ≤ k1.val)
      (hk_le : k1.val ≤ k2.val) (hk2_high : k2.val ≤ 50) :
      ∀ r1 r2 : Std.I64,
        length_of_longest_substring_k_distinct s k1 = ok r1 →
        length_of_longest_substring_k_distinct s k2 = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk1_low : 0 ≤ k1.val)
        (hk_le : k1.val ≤ k2.val) (hk2_high : k2.val ≤ 50), ∀ r1 r2 : Std.I64,
          length_of_longest_substring_k_distinct s k1 = ok r1 →
          length_of_longest_substring_k_distinct s k2 = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Let m = len(s) if len(s) <= k, and m = k otherwise (so m is the smaller of len(s) and k). The function returns a result r and r >= m.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∃ r : Std.I64,
        length_of_longest_substring_k_distinct s k = ok r ∧
        ((min s.val.length k.val.toNat : ℕ) : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∃ r : Std.I64,
          length_of_longest_substring_k_distinct s k = ok r ∧
          ((min s.val.length k.val.toNat : ℕ) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if k = 0 or len(s) = 0.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_9 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        (r.val = 0 ↔ k.val = 0 ∨ s.val.length = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          (r.val = 0 ↔ k.val = 0 ∨ s.val.length = 0)) := by
    sorry

  /-- If the call on (t,k) returns r_t and the call on (s,k) returns r_s, then r_t <= r_s.
    Preconditions: len(s) <= 50000, 0 <= k <= 50, and t is a contiguous substring of s (possibly empty), i.e., there exist 0 <= i <= j <= len(s) with len(t) = j - i and t[p] = s[i+p] for all 0 <= p < len(t). -/
  theorem spec_10 (s t : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hsub : IsSubslice t s)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r_t r_s : Std.I64,
        length_of_longest_substring_k_distinct t k = ok r_t →
        length_of_longest_substring_k_distinct s k = ok r_s →
        r_t.val ≤ r_s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hsub : IsSubslice t s)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r_t r_s : Std.I64,
          length_of_longest_substring_k_distinct t k = ok r_t →
          length_of_longest_substring_k_distinct s k = ok r_s →
          r_t.val ≤ r_s.val) := by
    sorry

  /-- If the call on (s,k) returns r_s and the call on (t,k) returns r_t, then r_s = r_t.
    Preconditions: len(s) = len(t) <= 50000, 0 <= k <= 50, and for all indices 0 <= i,j < len(s), s[i] = s[j] if and only if t[i] = t[j]. -/
  theorem spec_11 (s t : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hlen_eq : s.val.length = t.val.length)
      (hsame : ∀ i j : ℕ, i < s.val.length → j < s.val.length →
        ((bytes s)[i]? = (bytes s)[j]? ↔ (bytes t)[i]? = (bytes t)[j]?))
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r_s r_t : Std.I64,
        length_of_longest_substring_k_distinct s k = ok r_s →
        length_of_longest_substring_k_distinct t k = ok r_t →
        r_s.val = r_t.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hlen_eq : s.val.length = t.val.length)
        (hsame : ∀ i j : ℕ, i < s.val.length → j < s.val.length →
          ((bytes s)[i]? = (bytes s)[j]? ↔ (bytes t)[i]? = (bytes t)[j]?))
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r_s r_t : Std.I64,
          length_of_longest_substring_k_distinct s k = ok r_s →
          length_of_longest_substring_k_distinct t k = ok r_t →
          r_s.val = r_t.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer L with 0 <= L <= r there exist indices 0 <= i <= j <= len(s) such that j - i = L and the substring s[i..j) contains at most k distinct byte values.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_12 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        ∀ L : ℕ, L ≤ r.val.toNat →
          ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧ j - i = L ∧
            windowDistinct (bytes s) i j ≤ k.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          ∀ L : ℕ, L ≤ r.val.toNat →
            ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧ j - i = L ∧
              windowDistinct (bytes s) i j ≤ k.val.toNat) := by
    sorry

  /-- If the call on (s,k) returns r and the call on (rev(s),k) returns r_rev, then r = r_rev.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. Let rev(s) be the byte slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for all 0 <= i < len(s). -/
  theorem spec_13 (s t : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hrev : t.val = s.val.reverse)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r r_rev : Std.I64,
        length_of_longest_substring_k_distinct s k = ok r →
        length_of_longest_substring_k_distinct t k = ok r_rev →
        r.val = r_rev.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hrev : t.val = s.val.reverse)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r r_rev : Std.I64,
          length_of_longest_substring_k_distinct s k = ok r →
          length_of_longest_substring_k_distinct t k = ok r_rev →
          r.val = r_rev.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices 0 <= i <= j <= len(s) such that j - i = r, the substring s[i..j) has at most k distinct byte values, and both of the following hold: (1) either i = 0 or the substring s[i-1..j) has more than k distinct byte values; (2) either j = len(s) or the substring s[i..j+1) has more than k distinct byte values.
    Preconditions: len(s) <= 50000 and 0 <= k <= 50. -/
  theorem spec_14 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
        ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
          (j : Int) - (i : Int) = r.val ∧
          windowDistinct (bytes s) i j ≤ k.val.toNat ∧
          (i = 0 ∨ k.val.toNat < windowDistinct (bytes s) (i - 1) j) ∧
          (j = s.val.length ∨ k.val.toNat < windowDistinct (bytes s) i (j + 1)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 50), ∀ r : Std.I64, length_of_longest_substring_k_distinct s k = ok r →
          ∃ i j : ℕ, i ≤ j ∧ j ≤ s.val.length ∧
            (j : Int) - (i : Int) = r.val ∧
            windowDistinct (bytes s) i j ≤ k.val.toNat ∧
            (i = 0 ∨ k.val.toNat < windowDistinct (bytes s) (i - 1) j) ∧
            (j = s.val.length ∨ k.val.toNat < windowDistinct (bytes s) i (j + 1))) := by
    sorry

  /-- Let R(s) be the maximum length of a contiguous block of equal byte values in s, i.e., the maximum of j - i over 0 <= i <= j <= len(s) such that all bytes s[t] for i <= t < j are equal; R(s)=0 when len(s)=0. The function returns a result r and r >= R(s).
    Preconditions: len(s) <= 50000 and 1 <= k <= 50. -/
  theorem spec_15 (s : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length ≤ 50000) (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 50) :
      ∃ r : Std.I64,
        length_of_longest_substring_k_distinct s k = ok r ∧
        ((maxConstRunLen (bytes s) : ℕ) : Int) ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length ≤ 50000) (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 50), ∃ r : Std.I64,
          length_of_longest_substring_k_distinct s k = ok r ∧
          ((maxConstRunLen (bytes s) : ℕ) : Int) ≤ r.val) := by
    sorry

  end AegisSpec.LengthOfLongestSubstringKDistinct
