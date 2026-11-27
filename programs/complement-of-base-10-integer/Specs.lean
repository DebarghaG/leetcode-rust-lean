import Aegis.BitwiseComplement.Code.Funs

/-!
# Specifications of `Aegis.BitwiseComplement.bitwise_complement`

LeetCode problem `complement-of-base-10-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.BitwiseComplement

  namespace AegisSpec.BitwiseComplement

  def L (n : ℤ) : ℕ := if n = 0 then 1 else n.natAbs.log2 + 1

  def bitAt (x : ℤ) (j : ℕ) : Bool := x.testBit j

  /-- Whenever the function returns a result r, r = 2^{L(n)} - 1 - n, where L(n) is 1 if n = 0, and otherwise is the unique positive integer such that 2^{L(n)-1} <= n < 2^{L(n)}. Equivalently, write n in binary without leading zeros (using the one-bit string "0" for n = 0), flip every 0 to 1 and every 1 to 0 in that binary string, and interpret the resulting string as a base-10 integer; that integer is r.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_1 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val = 2 ^ L n.val - 1 - n.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val = 2 ^ L n.val - 1 - n.val) := by
    sorry

  /-- For every n satisfying the precondition, the function returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_2 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9) :
      ∃ r : Std.I64, bitwise_complement n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9), ∃ r : Std.I64, bitwise_complement n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 2^{L(n)}, where L(n) is as defined in spec_1.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_3 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      0 ≤ r.val ∧ r.val < 2 ^ L n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), 0 ≤ r.val ∧ r.val < 2 ^ L n.val) := by
    sorry

  /-- Whenever the function returns a result r, r < 2^{L(n)-1}, where L(n) is as defined in spec_1.
    Preconditions: 0 < n < 10^9 -/
  theorem spec_4 (n : Std.I64) (hn0 : 0 < n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val < 2 ^ (L n.val - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 < n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val < 2 ^ (L n.val - 1)) := by
    sorry

  /-- For every n satisfying the precondition such that n = 2^k - 1 for some integer k >= 1, whenever the function returns a result r, r = 0.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_5 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (k : ℕ) (hk : 1 ≤ k) (hnk : n.val = 2 ^ k - 1)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (k : ℕ) (hk : 1 ≤ k) (hnk : n.val = 2 ^ k - 1)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val = 0) := by
    sorry

  /-- For every n satisfying the precondition such that n = 2^k for some integer k >= 0, whenever the function returns a result r, r = 2^k - 1.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_6 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (k : ℕ) (hnk : n.val = 2 ^ k)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val = 2 ^ k - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (k : ℕ) (hnk : n.val = 2 ^ k)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val = 2 ^ k - 1) := by
    sorry

  /-- Whenever the function returns a result r, n + r = 2^{L(n)} - 1, where L(n) is as defined in spec_1.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_7 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      n.val + r.val = 2 ^ L n.val - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), n.val + r.val = 2 ^ L n.val - 1) := by
    sorry

  /-- For every n and m satisfying the precondition with n < m and L(n) = L(m), if r is the result returned for n and s is the result returned for m, then r > s.
    Preconditions: 0 <= n < 10^9 and 0 <= m < 10^9 -/
  theorem spec_8 (n m : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (hm0 : 0 ≤ m.val) (hm : m.val < 10 ^ 9) (hnm : n.val < m.val)
      (hL : L n.val = L m.val)
      (r s : Std.I64) (hr : bitwise_complement n = ok r) (hs : bitwise_complement m = ok s) :
      r.val > s.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n m : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (hm0 : 0 ≤ m.val) (hm : m.val < 10 ^ 9) (hnm : n.val < m.val)
        (hL : L n.val = L m.val)
        (r s : Std.I64) (hr : bitwise_complement n = ok r) (hs : bitwise_complement m = ok s), r.val > s.val) := by
    sorry

  /-- For every n and m satisfying the precondition with L(n) = L(m), if r is the result returned for n and s is the result returned for m, then r - s = m - n.
    Preconditions: 0 <= n < 10^9 and 0 <= m < 10^9 -/
  theorem spec_9 (n m : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (hm0 : 0 ≤ m.val) (hm : m.val < 10 ^ 9)
      (hL : L n.val = L m.val)
      (r s : Std.I64) (hr : bitwise_complement n = ok r) (hs : bitwise_complement m = ok s) :
      r.val - s.val = m.val - n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n m : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (hm0 : 0 ≤ m.val) (hm : m.val < 10 ^ 9)
        (hL : L n.val = L m.val)
        (r s : Std.I64) (hr : bitwise_complement n = ok r) (hs : bitwise_complement m = ok s), r.val - s.val = m.val - n.val) := by
    sorry

  /-- Whenever the function returns a result r, for every bit position j with 0 <= j < L(n), the j-th bit of r (0-indexed from the least significant bit) is 1 if and only if the j-th bit of n is 0.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_10 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      ∀ j : ℕ, j < L n.val → (bitAt r.val j = true ↔ bitAt n.val j = false) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), ∀ j : ℕ, j < L n.val → (bitAt r.val j = true ↔ bitAt n.val j = false)) := by
    sorry

  /-- Whenever the function returns a result r, for every bit position j with j >= L(n), the j-th bit of r is 0.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_11 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      ∀ j : ℕ, L n.val ≤ j → bitAt r.val j = false := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), ∀ j : ℕ, L n.val ≤ j → bitAt r.val j = false) := by
    sorry

  /-- Whenever the function returns a result r, r is odd if and only if n is even, and r is even if and only if n is odd.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_12 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      (Odd r.val ↔ Even n.val) ∧ (Even r.val ↔ Odd n.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), (Odd r.val ↔ Even n.val) ∧ (Even r.val ↔ Odd n.val)) := by
    sorry

  /-- Whenever the function returns a result r, r < n.
    Preconditions: 0 < n < 10^9 -/
  theorem spec_13 (n : Std.I64) (hn0 : 0 < n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val < n.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 < n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val < n.val) := by
    sorry

  /-- Whenever the function returns a result r, r is the unique integer s such that 0 <= s < 2^{L(n)} and s + n = 2^{L(n)} - 1, where L(n) is as defined in spec_1.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_14 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      0 ≤ r.val ∧ r.val < 2 ^ L n.val ∧ r.val + n.val = 2 ^ L n.val - 1 ∧
        ∀ s : ℤ, 0 ≤ s → s < 2 ^ L n.val → s + n.val = 2 ^ L n.val - 1 → s = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), 0 ≤ r.val ∧ r.val < 2 ^ L n.val ∧ r.val + n.val = 2 ^ L n.val - 1 ∧
          ∀ s : ℤ, 0 ≤ s → s < 2 ^ L n.val → s + n.val = 2 ^ L n.val - 1 → s = r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 2^29 (that is, 0 <= r <= 536870911).
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_15 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      0 ≤ r.val ∧ r.val < 2 ^ 29 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), 0 ≤ r.val ∧ r.val < 2 ^ 29) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if n = 2^k - 1 for some integer k >= 1.
    Preconditions: 0 <= n < 10^9 -/
  theorem spec_16 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
      (r : Std.I64) (hr : bitwise_complement n = ok r) :
      r.val = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1 := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val < 10 ^ 9)
        (r : Std.I64) (hr : bitwise_complement n = ok r), r.val = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1) := by
    sorry

  end AegisSpec.BitwiseComplement
