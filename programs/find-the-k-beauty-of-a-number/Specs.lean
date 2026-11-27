import Aegis.DivisorSubstrings.Code.Funs

/-!
# Specifications of `Aegis.DivisorSubstrings.divisor_substrings`

LeetCode problem `find-the-k-beauty-of-a-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DivisorSubstrings

  def digitsOf (n : Nat) : List Nat :=
    if _h : n = 0 then [] else digitsOf (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

  def digitList (num : Std.I64) : List Nat := digitsOf num.val.toNat

  def numDigits (num : Std.I64) : Nat := (digitList num).length

  def digitAt (num : Std.I64) (i : Nat) : Nat := (digitList num).getD i 0

  def substringValue (ds : List Nat) (start len : Nat) : Nat :=
    ((ds.drop start).take len).foldl (fun acc d => acc * 10 + d) 0

  def window (num k : Std.I64) (i : Nat) : Nat := substringValue (digitList num) i k.toNat

  def counted (num k : Std.I64) (i : Nat) : Prop :=
    window num k i ≠ 0 ∧ num.val % (window num k i : ℤ) = 0

  instance countedDecidable (num k : Std.I64) : DecidablePred (counted num k) :=
    fun i => by unfold counted; infer_instance

  def countUpTo (n : Nat) (p : Nat → Prop) [DecidablePred p] : Nat :=
    ((List.range n).filter (fun i => decide (p i))).length

  def countOf (num k : Std.I64) : Nat :=
    countUpTo (numDigits num - k.toNat + 1) (fun i => counted num k i)

  def digitCountOf (num : Std.I64) : Nat :=
    countUpTo (numDigits num) (fun i => digitAt num i ≠ 0 ∧ num.val % (digitAt num i : ℤ) = 0)

  /-- The function returns a result r and r is exactly the number of indices i with 0 <= i <= L-k such that v_i != 0 and num mod v_i = 0.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those decimal digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. -/
  theorem spec_1 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = (countOf num k : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = (countOf num k : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or encounter integer overflow. This specification imposes no further condition on r.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). -/
  theorem spec_2 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= L-k+1.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). -/
  theorem spec_3 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
        0 ≤ r.val ∧ r.val ≤ (numDigits num : ℤ) - k.val + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
          0 ≤ r.val ∧ r.val ≤ (numDigits num : ℤ) - k.val + 1) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Additionally k = L. -/
  theorem spec_4 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (hkL : k.val = (numDigits num : ℤ)) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (hkL : k.val = (numDigits num : ℤ)), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = 1) := by
    sorry

  /-- Let d_0 ... d_{L-1} be the decimal digits of num. The function returns a result r and r is exactly the number of indices i with 0 <= i < L such that d_i != 0 and num mod d_i = 0.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Additionally k = 1. -/
  theorem spec_5 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (hk1 : k.val = 1) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧
        r.val = (digitCountOf num : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (hk1 : k.val = 1), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧
          r.val = (digitCountOf num : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an index i with 0 <= i <= L-k such that v_i != 0 and num mod v_i = 0.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. -/
  theorem spec_6 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
        (0 < r.val ↔
          ∃ i ∈ List.range (numDigits num - k.toNat + 1), counted num k i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
          (0 < r.val ↔
            ∃ i ∈ List.range (numDigits num - k.toNat + 1), counted num k i)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every index i with 0 <= i <= L-k, either v_i = 0 or num mod v_i != 0.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. -/
  theorem spec_7 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
        (r.val = 0 ↔
          ∀ i ∈ List.range (numDigits num - k.toNat + 1), ¬ counted num k i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
          (r.val = 0 ↔
            ∀ i ∈ List.range (numDigits num - k.toNat + 1), ¬ counted num k i)) := by
    sorry

  /-- The function returns a result r and r = L-k+1.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. Additionally, assume that for every i with 0 <= i <= L-k, v_i != 0 and num mod v_i = 0. -/
  theorem spec_8 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (hall : ∀ i ∈ List.range (numDigits num - k.toNat + 1), counted num k i) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧
        r.val = (numDigits num : ℤ) - k.val + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (hall : ∀ i ∈ List.range (numDigits num - k.toNat + 1), counted num k i), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧
          r.val = (numDigits num : ℤ) - k.val + 1) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. Additionally, assume that for every i with 0 <= i <= L-k, either v_i = 0 or num mod v_i != 0. -/
  theorem spec_9 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (hnone : ∀ i ∈ List.range (numDigits num - k.toNat + 1), ¬ counted num k i) :
      ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (hnone : ∀ i ∈ List.range (numDigits num - k.toNat + 1), ¬ counted num k i), ∃ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the number of indices i with 0 <= i <= L-k such that v_i = 1; equivalently, every such index satisfies v_i != 0 and num mod v_i = 0 and is therefore counted in r.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. -/
  theorem spec_10 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
        ((countUpTo (numDigits num - k.toNat + 1) (fun i => window num k i = 1) : Nat) : ℤ) ≤
          r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
          ((countUpTo (numDigits num - k.toNat + 1) (fun i => window num k i = 1) : Nat) : ℤ) ≤
            r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is the number of indices i with 0 <= i <= L-k such that v_i != 0 and num mod v_i = 0; in particular, for every index i with v_i = 0, the predicate v_i != 0 and num mod v_i = 0 is false, so i is not counted in r.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. -/
  theorem spec_11 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
        r.val = (countOf num k : ℤ) ∧
          ∀ i ∈ List.range (numDigits num - k.toNat + 1),
            window num k i = 0 → ¬ counted num k i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ)), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r →
          r.val = (countOf num k : ℤ) ∧
            ∀ i ∈ List.range (numDigits num - k.toNat + 1),
              window num k i = 0 → ¬ counted num k i) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. Additionally, assume there exist two distinct indices i and j with 0 <= i < j <= L-k such that v_i != 0, num mod v_i = 0, v_j != 0, and num mod v_j = 0. -/
  theorem spec_12 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (hpair : ∃ i ∈ List.range (numDigits num - k.toNat + 1),
        ∃ j ∈ List.range (numDigits num - k.toNat + 1),
          i < j ∧ counted num k i ∧ counted num k j) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (hpair : ∃ i ∈ List.range (numDigits num - k.toNat + 1),
          ∃ j ∈ List.range (numDigits num - k.toNat + 1),
            i < j ∧ counted num k i ∧ counted num k j), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r → 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: num and k satisfy the problem constraints: 1 <= num <= 10^9 and 1 <= k <= L, where L is the number of decimal digits in the ordinary decimal representation of num (no leading zeros). Let d_0 ... d_{L-1} be those digits, so d_0 != 0, and for each i with 0 <= i <= L-k let v_i = sum_{j=0}^{k-1} d_{i+j} * 10^{k-1-j}. Additionally, assume there is exactly one index i with 0 <= i <= L-k such that v_i != 0 and num mod v_i = 0. -/
  theorem spec_13 (num k : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
      (huniq : ∃ i ∈ List.range (numDigits num - k.toNat + 1),
        counted num k i ∧
          ∀ j ∈ List.range (numDigits num - k.toNat + 1), counted num k j → j = i) :
      ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r → r.val = 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num k : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 10 ^ 9)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (numDigits num : ℤ))
        (huniq : ∃ i ∈ List.range (numDigits num - k.toNat + 1),
          counted num k i ∧
            ∀ j ∈ List.range (numDigits num - k.toNat + 1), counted num k j → j = i), ∀ r, Aegis.DivisorSubstrings.divisor_substrings num k = ok r → r.val = 1) := by
    sorry

  end AegisSpec.DivisorSubstrings
