import Aegis.LongestDecomposition.Code.Funs

/-!
# Specifications of `Aegis.LongestDecomposition.longest_decomposition`

LeetCode problem `longest-chunked-palindrome-decomposition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestDecomposition

  def byteAt (text : Slice Std.U8) (i : Nat) : Nat :=
    match text.val[i]? with
    | some b => b.val
    | none => 0

  def IsPalindrome (text : Slice Std.U8) : Prop :=
    ∀ i, i < text.val.length → byteAt text i = byteAt text (text.val.length - 1 - i)

  def reverseText (text : Slice Std.U8) : List Std.U8 :=
    text.val.reverse

  def IsPalindromicDecomposition (l : List Std.U8) (pieces : List (List Std.U8)) : Prop :=
    (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten = l ∧ pieces = pieces.reverse

  def HasDecomposition (l : List Std.U8) (k : Int) : Prop :=
    ∃ pieces : List (List Std.U8), IsPalindromicDecomposition l pieces ∧ (pieces.length : Int) = k

  def IsLongestDecomposition (l : List Std.U8) (k : Int) : Prop :=
    HasDecomposition l k ∧ ∀ k' : Int, HasDecomposition l k' → k' ≤ k

  def prefixEqSuffix (text : Slice Std.U8) (L : Nat) : Prop :=
    text.val.take L = text.val.drop (text.val.length - L)

  def IsBorder (text : Slice Std.U8) (L : Nat) : Prop :=
    1 ≤ L ∧ 2 * L ≤ text.val.length ∧ prefixEqSuffix text L

  def IsStrictBorder (text : Slice Std.U8) (L : Nat) : Prop :=
    1 ≤ L ∧ 2 * L < text.val.length ∧ prefixEqSuffix text L

  def IsLeastBorder (text : Slice Std.U8) (L : Nat) : Prop :=
    IsBorder text L ∧ ∀ L' : Nat, IsBorder text L' → L ≤ L'

  def middleText (text : Slice Std.U8) (L : Nat) : List Std.U8 :=
    (text.val.drop L).take (text.val.length - 2 * L)

  /-- The function returns a result r and r is the largest integer k for which there exist non-empty byte strings s_1, ..., s_k such that s_1 ++ ... ++ s_k equals text byte-for-byte and s_i = s_{k-i+1} for every i with 1 <= i <= k. Equivalently, r is the maximum number of non-empty contiguous pieces in a partition of text whose sequence of pieces reads the same forwards and backwards.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_1 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∃ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r ∧
          IsLongestDecomposition text.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∃ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r ∧
            IsLongestDecomposition text.val r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_2 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∃ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∃ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_3 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(text).
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_4 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          r.val ≤ (text.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            r.val ≤ (text.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: 1 <= len(text) <= 1000, len(text) = 1, and every byte of text is between 97 and 122 inclusive. -/
  theorem spec_5 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hlen_eq : text.val.length = 1)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r → r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hlen_eq : text.val.length = 1)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64, Aegis.LongestDecomposition.longest_decomposition text = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = len(text) if and only if text[i] = text[len(text)-1-i] for every i with 0 <= i < len(text).
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_6 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (r.val = (text.val.length : Int) ↔ IsPalindrome text) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (r.val = (text.val.length : Int) ↔ IsPalindrome text)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there is no integer L such that 1 <= L <= floor(len(text)/2) and the prefix text[0..L) equals the suffix text[len(text)-L..len(text)) byte-for-byte.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_7 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (r.val = 1 ↔ ¬ ∃ L : Nat, IsBorder text L) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (r.val = 1 ↔ ¬ ∃ L : Nat, IsBorder text L)) := by
    sorry

  /-- Whenever the function returns a result r, there exist non-empty byte strings s_1, ..., s_r such that s_1 ++ ... ++ s_r equals text byte-for-byte and s_i = s_{r-i+1} for every i with 1 <= i <= r.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_8 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          HasDecomposition text.val r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            HasDecomposition text.val r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with r < k there do not exist non-empty byte strings s_1, ..., s_k such that s_1 ++ ... ++ s_k equals text byte-for-byte and s_i = s_{k-i+1} for every i with 1 <= i <= k.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_9 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          ∀ k : Int, r.val < k → ¬ HasDecomposition text.val k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            ∀ k : Int, r.val < k → ¬ HasDecomposition text.val k) := by
    sorry

  /-- Whenever the function returns a result r, let text^R be the byte array with text^R[i] = text[len(text)-1-i] for 0 <= i < len(text). Then r is also the largest integer k for which text^R admits a decomposition into non-empty byte strings t_1, ..., t_k with t_1 ++ ... ++ t_k = text^R and t_i = t_{k-i+1} for every i with 1 <= i <= k.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_10 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          IsLongestDecomposition (reverseText text) r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            IsLongestDecomposition (reverseText text) r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 if text[0] = text[1], and r = 1 otherwise.
    Preconditions: 1 <= len(text) <= 1000, len(text) = 2, and every byte of text is between 97 and 122 inclusive. -/
  theorem spec_11 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hlen_eq : text.val.length = 2)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (byteAt text 0 = byteAt text 1 → r.val = 2) ∧
            (byteAt text 0 ≠ byteAt text 1 → r.val = 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hlen_eq : text.val.length = 2)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (byteAt text 0 = byteAt text 1 → r.val = 2) ∧
              (byteAt text 0 ≠ byteAt text 1 → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 3 if text[0] = text[2], and r = 1 otherwise.
    Preconditions: 1 <= len(text) <= 1000, len(text) = 3, and every byte of text is between 97 and 122 inclusive. -/
  theorem spec_12 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hlen_eq : text.val.length = 3)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (byteAt text 0 = byteAt text 2 → r.val = 3) ∧
            (byteAt text 0 ≠ byteAt text 2 → r.val = 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hlen_eq : text.val.length = 3)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (byteAt text 0 = byteAt text 2 → r.val = 3) ∧
              (byteAt text 0 ≠ byteAt text 2 → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, if len(text) is odd then r is odd.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_13 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          text.val.length % 2 = 1 → Odd r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            text.val.length % 2 = 1 → Odd r.val) := by
    sorry

  /-- Whenever the function returns a result r, if text[i] != text[j] for all i and j with 0 <= i < j < len(text), then r = 1.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_14 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (∀ i j : Nat, i < j → j < text.val.length → byteAt text i ≠ byteAt text j) →
            r.val = 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (∀ i j : Nat, i < j → j < text.val.length → byteAt text i ≠ byteAt text j) →
              r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an integer L such that 1 <= L and 2*L < len(text) and the prefix text[0..L) equals the suffix text[len(text)-L..len(text)) byte-for-byte, then r >= 3.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_15 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          (∃ L : Nat, IsStrictBorder text L) → 3 ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            (∃ L : Nat, IsStrictBorder text L) → 3 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if there is no integer L with 1 <= L <= len(text)/2 and text[0..L) = text[len(text)-L..len(text)), then r = 1. Otherwise let L be the least such integer. If 2*L = len(text), then r = 2; if 2*L < len(text), then r = 2 + f(text[L..len(text)-L)), where f(text') is the largest integer m for which there exist non-empty byte strings t_1, ..., t_m with t_1 ++ ... ++ t_m = text' and t_i = t_{m-i+1} for every i with 1 <= i <= m.
    Preconditions: 1 <= len(text) <= 1000 and for every i with 0 <= i < len(text), 97 <= text[i] <= 122. -/
  theorem spec_16 (text : Slice Std.U8)
      (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
      (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122) :
      ∀ r : Std.I64,
        Aegis.LongestDecomposition.longest_decomposition text = ok r →
          ((¬ ∃ L : Nat, IsBorder text L) → r.val = 1) ∧
            (∀ L : Nat,
              IsLeastBorder text L →
                (2 * L = text.val.length → r.val = 2) ∧
                  (2 * L < text.val.length →
                    ∃ m : Int, IsLongestDecomposition (middleText text L) m ∧ r.val = 2 + m)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (text : Slice Std.U8)
        (hlen_ge_one : 1 ≤ text.val.length) (hlen_le : text.val.length ≤ 1000)
        (hbytes : ∀ i, i < text.val.length → 97 ≤ byteAt text i ∧ byteAt text i ≤ 122), ∀ r : Std.I64,
          Aegis.LongestDecomposition.longest_decomposition text = ok r →
            ((¬ ∃ L : Nat, IsBorder text L) → r.val = 1) ∧
              (∀ L : Nat,
                IsLeastBorder text L →
                  (2 * L = text.val.length → r.val = 2) ∧
                    (2 * L < text.val.length →
                      ∃ m : Int, IsLongestDecomposition (middleText text L) m ∧ r.val = 2 + m))) := by
    sorry

  end AegisSpec.LongestDecomposition
