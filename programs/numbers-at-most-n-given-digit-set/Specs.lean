import Aegis.AtMostNGivenDigitSet.Code.Funs

/-!
# Specifications of `Aegis.AtMostNGivenDigitSet.at_most_n_given_digit_set`

LeetCode problem `numbers-at-most-n-given-digit-set`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  open Aegis.AtMostNGivenDigitSet

  namespace AegisSpec.AtMostNGivenDigitSet

  def byteAt? (digits : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Option Nat :=
    (digits.val[i]?).bind fun v => (v.val[0]?).map fun b => b.val

  def digitAt (digits : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Nat :=
    (byteAt? digits i).getD 0 - 48

  def digitSet (digits : Slice (alloc.vec.Vec Std.U8)) : Finset Nat :=
    (Finset.Icc 1 9).filter fun d => ∃ i, i < digits.val.length ∧ digitAt digits i = d

  def decDigits : Nat → List Nat
    | 0 => []
    | (n + 1) => decDigits ((n + 1) / 10) ++ [(n + 1) % 10]
  termination_by n => n
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

  def usesOnlyDigits (D : Finset Nat) (m : Nat) : Bool :=
    (decDigits m).all fun d => decide (d ∈ D)

  def countWithDigits (D : Finset Nat) (lo hi : Nat) : Nat :=
    ((Finset.Icc lo hi).filter fun m => usesOnlyDigits D m = true).card

  def numDigits (m : Nat) : Nat := (decDigits m).length

  def digitSum (D : Finset Nat) (levels : Nat) : Nat :=
    ∑ k ∈ Finset.Icc 1 levels, D.card ^ k

  def DigitsShaped (digits : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    1 ≤ digits.val.length ∧ digits.val.length ≤ 9 ∧
      ∀ v ∈ digits.val, ∃ b : Std.U8, v.val = [b] ∧ 49 ≤ b.val ∧ b.val ≤ 57

  def DigitsPairwiseDistinct (digits : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ (i j b c : Nat), i < j → j < digits.val.length →
      byteAt? digits i = some b → byteAt? digits j = some c → b ≠ c

  def DigitsNondecreasing (digits : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ (i j b c : Nat), i < j → j < digits.val.length →
      byteAt? digits i = some b → byteAt? digits j = some c → b ≤ c

  /-- Let D be the set of decimal digits represented by digits: D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. The function returns a result r (it does not fail) and r is exactly the number of positive integers m with 1 <= m <= n whose ordinary decimal representation (base 10, without leading zeros) has every digit in D.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_1 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∃ r : Std.I64, at_most_n_given_digit_set digits n = ok r ∧
        r.val = ((countWithDigits (digitSet digits) 1 n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, at_most_n_given_digit_set digits n = ok r ∧
          r.val = ((countWithDigits (digitSet digits) 1 n.val.toNat : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_2 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∃ r : Std.I64, at_most_n_given_digit_set digits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, at_most_n_given_digit_set digits n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_3 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= n.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_4 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r → r.val ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r → r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(digits) and digits[i][0] - 48 <= n, then r >= 1. In that case the one-digit integer digits[i][0] - 48 is counted.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_5 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        (∃ i, i < digits.val.length ∧ (digitAt digits i : Int) ≤ n.val) → 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          (∃ i, i < digits.val.length ∧ (digitAt digits i : Int) ≤ n.val) → 1 ≤ r.val) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, let L be the number of decimal digits of n, so 10^(L-1) <= n <= 10^L - 1. Then r = (sum_{k=1}^{L-1} |D|^k) + B, where B is the number of integers m with 10^(L-1) <= m <= n whose decimal representation uses only digits in D.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_6 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        let L := numDigits n.val.toNat
        r.val = ((digitSum (digitSet digits) (L - 1) +
          countWithDigits (digitSet digits) (10 ^ (L - 1)) n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          let L := numDigits n.val.toNat
          r.val = ((digitSum (digitSet digits) (L - 1) +
            countWithDigits (digitSet digits) (10 ^ (L - 1)) n.val.toNat : Nat) : Int)) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, r = |{ d in D | d <= n }|.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 10. -/
  theorem spec_7 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val = ((((digitSet digits).filter fun d => d ≤ n.val.toNat).card : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val = ((((digitSet digits).filter fun d => d ≤ n.val.toNat).card : Nat) : Int)) := by
    sorry

  /-- Let d = digits[0][0] - 48. Whenever the function returns a result r, r = |{ k in the natural numbers | k >= 1 and d * (10^k - 1)/9 <= n }|. The expression d * (10^k - 1)/9 is the k-digit integer whose decimal representation consists of k copies of d.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000; len(digits) = 1. -/
  theorem spec_8 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
      (hlen : digits.val.length = 1) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val = ((((Finset.Icc 1 (n.val.toNat + 1)).filter fun k =>
          digitAt digits 0 * (10 ^ k - 1) / 9 ≤ n.val.toNat).card : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
        (hlen : digits.val.length = 1), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val = ((((Finset.Icc 1 (n.val.toNat + 1)).filter fun k =>
            digitAt digits 0 * (10 ^ k - 1) / 9 ≤ n.val.toNat).card : Nat) : Int)) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. For the q with n = 10^q, whenever the function returns a result r, r = sum_{k=1}^{q} |D|^k.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; there exists an integer q with 1 <= q <= 9 and n = 10^q. -/
  theorem spec_9 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64) (q : Nat)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hq_lo : 1 ≤ q) (hq_hi : q ≤ 9) (hn_pow : n.val = (10 : Int) ^ q) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val = ((digitSum (digitSet digits) q : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64) (q : Nat)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hq_lo : 1 ≤ q) (hq_hi : q ≤ 9) (hn_pow : n.val = (10 : Int) ^ q), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val = ((digitSum (digitSet digits) q : Nat) : Int)) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. For the q with n = 10^q - 1, whenever the function returns a result r, r = sum_{k=1}^{q} |D|^k.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; there exists an integer q with 1 <= q <= 9 and n = 10^q - 1. -/
  theorem spec_10 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64) (q : Nat)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hq_lo : 1 ≤ q) (hq_hi : q ≤ 9) (hn_pow : n.val = (10 : Int) ^ q - 1) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val = ((digitSum (digitSet digits) q : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64) (q : Nat)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hq_lo : 1 ≤ q) (hq_hi : q ≤ 9) (hn_pow : n.val = (10 : Int) ^ q - 1), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val = ((digitSum (digitSet digits) q : Nat) : Int)) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. If the function returns r1 on input (digits, n1) and r2 on input (digits, n2), then r1 <= r2.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n1 <= n2 <= 1000000000. -/
  theorem spec_11 (digits : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000000000) :
      ∀ r1 r2 : Std.I64,
        at_most_n_given_digit_set digits n1 = ok r1 →
        at_most_n_given_digit_set digits n2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000000000), ∀ r1 r2 : Std.I64,
          at_most_n_given_digit_set digits n1 = ok r1 →
          at_most_n_given_digit_set digits n2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. If the function returns r1 on input (digits, n1) and r2 on input (digits, n2), and if for every integer m with n1 < m <= n2 the decimal representation of m contains at least one digit not in D, then r1 = r2.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n1 <= n2 <= 1000000000. -/
  theorem spec_12 (digits : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000000000) :
      ∀ r1 r2 : Std.I64,
        at_most_n_given_digit_set digits n1 = ok r1 →
        at_most_n_given_digit_set digits n2 = ok r2 →
        (∀ m : Nat, n1.val < (m : Int) → (m : Int) ≤ n2.val →
          ∃ d, d ∈ decDigits m ∧ d ∉ digitSet digits) → r1 = r2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000000000), ∀ r1 r2 : Std.I64,
          at_most_n_given_digit_set digits n1 = ok r1 →
          at_most_n_given_digit_set digits n2 = ok r2 →
          (∀ m : Nat, n1.val < (m : Int) → (m : Int) ≤ n2.val →
            ∃ d, d ∈ decDigits m ∧ d ∉ digitSet digits) → r1 = r2) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, let L be the number of decimal digits of n. Then r <= sum_{k=1}^{L} |D|^k.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_13 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val ≤ ((digitSum (digitSet digits) (numDigits n.val.toNat) : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val ≤ ((digitSum (digitSet digits) (numDigits n.val.toNat) : Nat) : Int)) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(digits), digits[i][0] - 48 > n.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_14 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        (r.val = 0 ↔ ∀ i, i < digits.val.length → n.val < (digitAt digits i : Int)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          (r.val = 0 ↔ ∀ i, i < digits.val.length → n.val < (digitAt digits i : Int))) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, r >= |{ d in D | d <= n }|.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_15 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        ((((digitSet digits).filter fun d => d ≤ n.val.toNat).card : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          ((((digitSet digits).filter fun d => d ≤ n.val.toNat).card : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Let D = { d in {1,...,9} | there exists i with 0 <= i < len(digits) and digits[i][0] = 48 + d }. Whenever the function returns a result r, r <= sum_{k=1}^{9} |D|^k <= 435848049.
    Preconditions: 1 <= len(digits) <= 9; for every i with 0 <= i < len(digits), len(digits[i]) = 1 and 49 <= digits[i][0] <= 57; the byte values digits[i][0] are pairwise distinct and non-decreasing in i; 1 <= n <= 1000000000. -/
  theorem spec_16 (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
      (hmono : DigitsNondecreasing digits)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
      ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
        r.val ≤ ((digitSum (digitSet digits) 9 : Nat) : Int) ∧
          ((digitSum (digitSet digits) 9 : Nat) : Int) ≤ 435848049 := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (digits : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hshape : DigitsShaped digits) (hdist : DigitsPairwiseDistinct digits)
        (hmono : DigitsNondecreasing digits)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∀ r : Std.I64, at_most_n_given_digit_set digits n = ok r →
          r.val ≤ ((digitSum (digitSet digits) 9 : Nat) : Int) ∧
            ((digitSum (digitSet digits) 9 : Nat) : Int) ≤ 435848049) := by
    sorry

  end AegisSpec.AtMostNGivenDigitSet
