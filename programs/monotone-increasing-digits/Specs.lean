import Aegis.MonotoneIncreasingDigits.Code.Funs

/-!
# Specifications of `Aegis.MonotoneIncreasingDigits.monotone_increasing_digits`

LeetCode problem `monotone-increasing-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MonotoneIncreasingDigits

  open Aegis.MonotoneIncreasingDigits

  def digitsRev : Nat → List Nat
    | 0 => []
    | n + 1 => (n + 1) % 10 :: digitsRev ((n + 1) / 10)
  termination_by n => n
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

  def digitsOf (m : Nat) : List Nat := (digitsRev m).reverse

  def HasMonotoneDigits (m : Nat) : Prop := (digitsOf m).Pairwise (· ≤ ·)

  def HasMonotoneDigitsZ (z : Int) : Prop := 0 ≤ z ∧ HasMonotoneDigits z.toNat

  /-- Whenever monotone_increasing_digits(n) returns a result r, r is the unique integer satisfying all three conditions: (1) 0 <= r <= n; (2) r has monotone increasing digits, meaning that if the usual base-10 representation of r without leading zeros is d_0 d_1 ... d_{k-1} (with k >= 1; d_0 != 0 when r > 0, and d_0 = 0 when r = 0), then d_i <= d_{i+1} for every 0 <= i < k-1; (3) for every integer m with 0 <= m <= n that has monotone increasing digits, m <= r. Equivalently, r is the largest integer not exceeding n whose decimal digits are nondecreasing from left to right.
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_1 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      (0 ≤ r.val ∧ r.val ≤ n.val) ∧
        HasMonotoneDigits r.val.toNat ∧
        (∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r.val) ∧
        (∀ r' : Int,
          (0 ≤ r' ∧ r' ≤ n.val) →
            HasMonotoneDigits r'.toNat →
              (∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r') →
                r' = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), (0 ≤ r.val ∧ r.val ≤ n.val) ∧
          HasMonotoneDigits r.val.toNat ∧
          (∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r.val) ∧
          (∀ r' : Int,
            (0 ≤ r' ∧ r' ≤ n.val) →
              HasMonotoneDigits r'.toNat →
                (∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r') →
                  r' = r.val)) := by
    sorry

  /-- For every n with 0 <= n <= 1,000,000,000, the call monotone_increasing_digits(n) returns a result r (it does not fail, panic, overflow, or produce an out-of-bounds error).
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_2 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000) :
      ∃ r : Std.I64, monotone_increasing_digits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000), ∃ r : Std.I64, monotone_increasing_digits n = ok r) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, 0 <= r <= n.
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_3 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      0 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), 0 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, r has monotone increasing digits: writing the usual base-10 representation of r without leading zeros as d_0 d_1 ... d_{k-1} (with k >= 1; for r = 0 this is the single digit 0), we have d_i <= d_{i+1} for every 0 <= i < k-1.
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_4 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      HasMonotoneDigits r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), HasMonotoneDigits r.val.toNat) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, for every integer m with 0 <= m <= n that has monotone increasing digits, we have m <= r. (Here m has monotone increasing digits in the same sense: in its base-10 representation without leading zeros, every adjacent pair x on the left and y on the right satisfies x <= y.)
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_5 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      ∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), ∀ m : Int, 0 ≤ m → m ≤ n.val → HasMonotoneDigits m.toNat → m ≤ r.val) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, r = n if and only if n has monotone increasing digits. (Monotone increasing digits means: in n's usual base-10 representation without leading zeros, every adjacent pair x, y from left to right satisfies x <= y; for n = 0 the single digit 0 is vacuously monotone.)
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_6 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      (r.val = n.val ↔ HasMonotoneDigits n.val.toNat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), (r.val = n.val ↔ HasMonotoneDigits n.val.toNat)) := by
    sorry

  /-- If monotone_increasing_digits(n1) returns r1 and monotone_increasing_digits(n2) returns r2, then r1 <= r2.
    Preconditions: n1 and n2 are 64-bit signed integers satisfying 0 <= n1 <= n2 <= 1,000,000,000. -/
  theorem spec_7 (n1 n2 : Std.I64) (h1 : 0 ≤ n1.val) (h12 : n1.val ≤ n2.val)
      (h2 : n2.val ≤ 1000000000)
      (r1 r2 : Std.I64) (hr1 : monotone_increasing_digits n1 = ok r1)
      (hr2 : monotone_increasing_digits n2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n1 n2 : Std.I64) (h1 : 0 ≤ n1.val) (h12 : n1.val ≤ n2.val)
        (h2 : n2.val ≤ 1000000000)
        (r1 r2 : Std.I64) (hr1 : monotone_increasing_digits n1 = ok r1)
        (hr2 : monotone_increasing_digits n2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Let L be the number of decimal digits in n, with L = 1 when n = 0, and for n > 0 let L be characterized by 10^{L-1} <= n < 10^L. Whenever monotone_increasing_digits(n) returns a result r, r >= 10^{L-1} - 1.
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_8 (n : Std.I64) (L : Nat) (hn0 : 0 ≤ n.val)
      (hn1 : n.val ≤ 1000000000)
      (hL : (n.val = 0 ∧ L = 1) ∨
        (0 < n.val ∧ (10 : Int) ^ (L - 1) ≤ n.val ∧ n.val < (10 : Int) ^ L))
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      r.val ≥ (10 : Int) ^ (L - 1) - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (L : Nat) (hn0 : 0 ≤ n.val)
        (hn1 : n.val ≤ 1000000000)
        (hL : (n.val = 0 ∧ L = 1) ∨
          (0 < n.val ∧ (10 : Int) ^ (L - 1) ≤ n.val ∧ n.val < (10 : Int) ^ L))
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), r.val ≥ (10 : Int) ^ (L - 1) - 1) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, r = n - 1.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 1,000,000,000, and n = d * 10^k for some integers d and k with 1 <= d <= 9 and 1 <= k. -/
  theorem spec_9 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (d : Int) (k : Nat) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk : 1 ≤ k)
      (hn : n.val = d * 10 ^ k)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      r.val = n.val - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (d : Int) (k : Nat) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk : 1 ≤ k)
        (hn : n.val = d * 10 ^ k)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), r.val = n.val - 1) := by
    sorry

  /-- Whenever monotone_increasing_digits(n) returns a result r, r = 10*(d - 1) + 9.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 1,000,000,000, and n = 10*d + e where d and e are integers with 1 <= d <= 9 and 1 <= e < d. -/
  theorem spec_10 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (d e : Int) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (he1 : 1 ≤ e) (hed : e < d)
      (hn : n.val = 10 * d + e)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      r.val = 10 * (d - 1) + 9 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (d e : Int) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (he1 : 1 ≤ e) (hed : e < d)
        (hn : n.val = 10 * d + e)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), r.val = 10 * (d - 1) + 9) := by
    sorry

  /-- For every n with 0 <= n <= 1,000,000,000, if monotone_increasing_digits(n) returns a result r, then the call monotone_increasing_digits(r) returns r.
    Preconditions: n is a 64-bit signed integer satisfying 0 <= n <= 1,000,000,000. -/
  theorem spec_11 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
      (r : Std.I64) (hr : monotone_increasing_digits n = ok r) :
      monotone_increasing_digits r = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 1000000000)
        (r : Std.I64) (hr : monotone_increasing_digits n = ok r), monotone_increasing_digits r = ok r) := by
    sorry

  end AegisSpec.MonotoneIncreasingDigits
