import Aegis.CountGoodStrings.Code.Funs

/-!
# Specifications of `Aegis.CountGoodStrings.count_good_strings`

LeetCode problem `count-ways-to-build-good-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountGoodStrings

  namespace AegisSpec.CountGoodStrings

  abbrev BinString : Type := List Bool

  def block (b : Bool) (n : ℕ) : BinString := List.replicate n b

  inductive Constructible (zero one : ℕ) : BinString → Prop where
    | nil : Constructible zero one []
    | cons_zero {s : BinString} :
        Constructible zero one s → Constructible zero one (block false zero ++ s)
    | cons_one {s : BinString} :
        Constructible zero one s → Constructible zero one (block true one ++ s)

  def allBinStringsUpTo : ℕ → Finset BinString
    | 0 => {[]}
    | n + 1 =>
        allBinStringsUpTo n ∪ (allBinStringsUpTo n).image (fun s => false :: s) ∪
          (allBinStringsUpTo n).image (fun s => true :: s)

  noncomputable def goodSet (low high zero one : ℕ) : Finset BinString := by
    classical
    exact (allBinStringsUpTo high).filter (fun s => low ≤ s.length ∧ Constructible zero one s)

  noncomputable def trueCount (low high zero one : ℕ) : ℕ := (goodSet low high zero one).card

  noncomputable def exactCount (zero one n : ℕ) : ℕ := trueCount n n zero one

  noncomputable def rangeCount (low high zero one : ℕ) : ℕ :=
    ∑ n ∈ Finset.Icc low high, exactCount zero one n

  noncomputable def multCount (low high s : ℤ) : ℕ :=
    ((Finset.range (high.toNat + 1)).filter
        (fun m : ℕ => 1 ≤ m ∧ low ≤ (m : ℤ) * s ∧ (m : ℤ) * s ≤ high)).card

  /-- The function returns a result r (i.e., it does not fail), and r = N mod 1000000007, where N is the number of distinct binary strings s such that: (1) low <= len(s) <= high, and (2) s is constructible, meaning s is the concatenation of a finite (possibly empty) sequence of blocks, each block being either the string consisting of zero copies of '0' or the string consisting of one copies of '1'.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_1 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∃ r : Std.I64,
        count_good_strings low high zero one = ok r ∧
          r.val = ((trueCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat : ℕ) : ℤ) %
            1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∃ r : Std.I64,
          count_good_strings low high zero one = ok r ∧
            r.val = ((trueCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat : ℕ) : ℤ) %
              1000000007) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result (i.e., it does not panic, fail, or return an error).
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_2 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∃ r : Std.I64, count_good_strings low high zero one = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∃ r : Std.I64, count_good_strings low high zero one = ok r) := by
    sorry

  /-- Whenever the function returns a result r, it holds that 0 <= r <= 1000000006.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_3 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∀ r : Std.I64, count_good_strings low high zero one = ok r →
        0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∀ r : Std.I64, count_good_strings low high zero one = ok r →
          0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- If zero = one = k (for some positive integer k), then the returned value r satisfies r = (sum over all integers j >= 0 with low <= j*k <= high of 2^j) mod 1000000007.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_4 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) (h_eq : zero.val = one.val) :
      ∀ r : Std.I64, count_good_strings low high zero one = ok r →
        r.val = ((∑ j ∈ (Finset.range (high.val.toNat + 1)).filter
            (fun j : ℕ => low.val ≤ (j : ℤ) * zero.val ∧ (j : ℤ) * zero.val ≤ high.val),
            (2 : ℤ) ^ j) % 1000000007) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val) (h_eq : zero.val = one.val), ∀ r : Std.I64, count_good_strings low high zero one = ok r →
          r.val = ((∑ j ∈ (Finset.range (high.val.toNat + 1)).filter
              (fun j : ℕ => low.val ≤ (j : ℤ) * zero.val ∧ (j : ℤ) * zero.val ≤ high.val),
              (2 : ℤ) ^ j) % 1000000007)) := by
    sorry

  /-- Let r1 be the value returned for parameters (low, high, zero, one) and r2 be the value returned for parameters (low, high, one, zero), both satisfying the preconditions. Then r1 = r2.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_5 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∀ r1 r2 : Std.I64,
        count_good_strings low high zero one = ok r1 →
          count_good_strings low high one zero = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∀ r1 r2 : Std.I64,
          count_good_strings low high zero one = ok r1 →
            count_good_strings low high one zero = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Let r be the value returned for (low, high, zero, one) and r_c be the value returned for (c*low, c*high, c*zero, c*one). Then r_c = r.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low, and c is a positive integer with c*high <= 100000. -/
  theorem spec_6 (low high zero one low' high' zero' one' : Std.I64) (c : ℕ)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) (h_c_pos : 0 < c)
      (h_c_high : (c : ℤ) * high.val ≤ 100000)
      (h_low' : low'.val = (c : ℤ) * low.val) (h_high' : high'.val = (c : ℤ) * high.val)
      (h_zero' : zero'.val = (c : ℤ) * zero.val) (h_one' : one'.val = (c : ℤ) * one.val) :
      ∀ r rc : Std.I64,
        count_good_strings low high zero one = ok r →
          count_good_strings low' high' zero' one' = ok rc → rc.val = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (low high zero one low' high' zero' one' : Std.I64) (c : ℕ)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val) (h_c_pos : 0 < c)
        (h_c_high : (c : ℤ) * high.val ≤ 100000)
        (h_low' : low'.val = (c : ℤ) * low.val) (h_high' : high'.val = (c : ℤ) * high.val)
        (h_zero' : zero'.val = (c : ℤ) * zero.val) (h_one' : one'.val = (c : ℤ) * one.val), ∀ r rc : Std.I64,
          count_good_strings low high zero one = ok r →
            count_good_strings low' high' zero' one' = ok rc → rc.val = r.val) := by
    sorry

  /-- If the returned value r is non-zero, then N > 0, where N is the true count (as in spec_1); equivalently, there exists at least one good string.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_7 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∀ r : Std.I64, count_good_strings low high zero one = ok r → r.val ≠ 0 →
        0 < trueCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∀ r : Std.I64, count_good_strings low high zero one = ok r → r.val ≠ 0 →
          0 < trueCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat) := by
    sorry

  /-- If low = high = zero, then the returned value r equals 2 if zero is a multiple of one (i.e., zero mod one = 0), and equals 1 otherwise.
    Preconditions: 1 <= low = high <= 100000, 1 <= zero = low, 1 <= one <= low. -/
  theorem spec_8 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_eq_high : low.val = high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_low : zero.val = low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∀ r : Std.I64, count_good_strings low high zero one = ok r →
        r.val = (if zero.val % one.val = 0 then (2 : ℤ) else 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_eq_high : low.val = high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_low : zero.val = low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∀ r : Std.I64, count_good_strings low high zero one = ok r →
          r.val = (if zero.val % one.val = 0 then (2 : ℤ) else 1)) := by
    sorry

  /-- Let C(n) be the true number of constructible binary strings of length exactly n (before taking modulo). Then C(0) = 1, and for every integer n >= 1, C(n) = (if n >= zero then C(n - zero) else 0) + (if n >= one then C(n - one) else 0). Consequently, the returned value r is congruent to the sum of C(n) for n from low to high modulo 1000000007, with 0 <= r < 1000000007.
    Preconditions: 1 <= low <= high <= 100000, 1 <= zero <= low, 1 <= one <= low. -/
  theorem spec_9 (low high zero one : Std.I64)
      (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
      (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
      (h_one_le : one.val ≤ low.val) :
      ∀ r : Std.I64, count_good_strings low high zero one = ok r →
        exactCount zero.val.toNat one.val.toNat 0 = 1 ∧
          (∀ n : ℕ, 1 ≤ n →
            exactCount zero.val.toNat one.val.toNat n =
              (if zero.val.toNat ≤ n then
                  exactCount zero.val.toNat one.val.toNat (n - zero.val.toNat)
                else 0) +
                if one.val.toNat ≤ n then
                  exactCount zero.val.toNat one.val.toNat (n - one.val.toNat)
                else 0) ∧
          r.val = ((rangeCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat : ℕ) : ℤ) %
            1000000007 ∧
          0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (low high zero one : Std.I64)
        (h_low_pos : 1 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ 100000) (h_zero_pos : 1 ≤ zero.val)
        (h_zero_le : zero.val ≤ low.val) (h_one_pos : 1 ≤ one.val)
        (h_one_le : one.val ≤ low.val), ∀ r : Std.I64, count_good_strings low high zero one = ok r →
          exactCount zero.val.toNat one.val.toNat 0 = 1 ∧
            (∀ n : ℕ, 1 ≤ n →
              exactCount zero.val.toNat one.val.toNat n =
                (if zero.val.toNat ≤ n then
                    exactCount zero.val.toNat one.val.toNat (n - zero.val.toNat)
                  else 0) +
                  if one.val.toNat ≤ n then
                    exactCount zero.val.toNat one.val.toNat (n - one.val.toNat)
                  else 0) ∧
            r.val = ((rangeCount low.val.toNat high.val.toNat zero.val.toNat one.val.toNat : ℕ) : ℤ) %
              1000000007 ∧
            0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  end AegisSpec.CountGoodStrings
