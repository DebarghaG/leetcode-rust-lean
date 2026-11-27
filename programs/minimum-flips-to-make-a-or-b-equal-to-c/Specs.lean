import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-flips-to-make-a-or-b-equal-to-c`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinFlips

  def bit (n : ℤ) (i : ℕ) : ℤ := n / (2 : ℤ) ^ i % 2

  def bor (x y : ℤ) : ℤ := ((x.toNat ||| y.toNat : ℕ) : ℤ)

  def bitDiff (x y : ℤ) : ℕ :=
    ((Finset.range (max x.natAbs y.natAbs + 1)).filter (fun i => bit x i ≠ bit y i)).card

  def totalFlips (x y a b : ℤ) : ℕ := bitDiff x a + bitDiff y b

  def IsMinTotalFlips (a b c r : ℤ) : Prop :=
    (∃ x y : ℕ, bor x y = c ∧ (totalFlips x y a b : ℤ) = r) ∧
      ∀ x y : ℕ, bor x y = c → r ≤ (totalFlips x y a b : ℤ)

  def popcount (n : ℤ) : ℕ :=
    ((Finset.range (n.natAbs + 1)).filter (fun i => bit n i = 1)).card

  def bitWidth (a b c : ℤ) : ℕ := (max (max a.natAbs b.natAbs) c.natAbs) + 1

  def bitCost (a b c : ℤ) (i : ℕ) : ℤ :=
    if bit c i = 1 then (if bit a i = 0 ∧ bit b i = 0 then 1 else 0)
    else bit a i + bit b i

  def totalCost (a b c : ℤ) : ℤ :=
    Finset.sum (Finset.range (bitWidth a b c)) (fun i => bitCost a b c i)

  def missingBits (a b c : ℤ) : ℕ :=
    ((Finset.range (bitWidth a b c)).filter
      (fun i => bit c i = 1 ∧ bit a i = 0 ∧ bit b i = 0)).card

  def clearCost (a b c : ℤ) : ℤ :=
    Finset.sum (Finset.range (bitWidth a b c))
      (fun i => if bit c i = 0 then bit a i + bit b i else 0)

  def i64Of (n : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

  theorem i64Of_val {n : ℤ} (h_lo : 0 ≤ n) (h_hi : n < 2 ^ 63) : (i64Of n).val = n := by
    show (BitVec.ofInt 64 n).toInt = n
    rw [BitVec.toInt_ofInt, Int.bmod_def]
    split <;> omega

  /-- The function returns a result r, and r is the minimum, over all pairs (x,y) of nonnegative integers with (x OR y) = c, of the total number of bit positions i >= 0 with bit_i(x) != bit_i(a) plus the total number of bit positions i >= 0 with bit_i(y) != bit_i(b). Equivalently, r is the least possible number of single-bit flips in a and b, where each flip changes one bit in exactly one of the two numbers, needed so that the bitwise OR of the two resulting nonnegative integers equals c. The minimum is attained.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2. -/
  theorem spec_1 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MinFlips.min_flips a b c = ok r ∧ IsMinTotalFlips a.val b.val c.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MinFlips.min_flips a b c = ok r ∧ IsMinTotalFlips a.val b.val c.val r.val) := by
    sorry

  /-- For every a,b,c satisfying the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. -/
  theorem spec_2 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.MinFlips.min_flips a b c = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000), ∃ r : Std.I64, Aegis.MinFlips.min_flips a b c = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. -/
  theorem spec_3 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 60.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. -/
  theorem spec_4 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      r.val ≤ 60 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), r.val ≤ 60) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if (a OR b) = c, where OR is bitwise OR on the nonnegative integers represented by a and b.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. -/
  theorem spec_5 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      (r.val = 0 ↔ bor a.val b.val = c.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), (r.val = 0 ↔ bor a.val b.val = c.val)) := by
    sorry

  /-- For every a,b,c satisfying the preconditions, the value returned for inputs (a,b,c) equals the value returned for inputs (b,a,c) with the same c; that is, the minimum number of flips is symmetric in a and b.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. -/
  theorem spec_6 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000) :
      Aegis.MinFlips.min_flips a b c = Aegis.MinFlips.min_flips b a c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000), Aegis.MinFlips.min_flips a b c = Aegis.MinFlips.min_flips b a c) := by
    sorry

  /-- Whenever the function returns a result r, r = sum over all i >= 0 of cost_i, where a_i = bit_i(a), b_i = bit_i(b), c_i = bit_i(c), and cost_i is defined by: cost_i = 0 if c_i = 1 and (a_i = 1 or b_i = 1); cost_i = 1 if c_i = 1 and a_i = b_i = 0; and cost_i = a_i + b_i if c_i = 0. The sum has only finitely many nonzero terms.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2. -/
  theorem spec_7 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      r.val = totalCost a.val b.val c.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), r.val = totalCost a.val b.val c.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the number of bit positions i >= 0 for which bit_i(c) = 1 and bit_i(a) = bit_i(b) = 0.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2. -/
  theorem spec_8 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      (missingBits a.val b.val c.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), (missingBits a.val b.val c.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the sum, over all bit positions i >= 0 with bit_i(c) = 0, of (bit_i(a) + bit_i(b)).
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2. -/
  theorem spec_9 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      clearCost a.val b.val c.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), clearCost a.val b.val c.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= popcount(a) + popcount(b) + popcount(c).
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2; popcount(n) is the number of bit positions i >= 0 with bit_i(n) = 1. -/
  theorem spec_10 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      r.val ≤ (popcount a.val : ℤ) + (popcount b.val : ℤ) + (popcount c.val : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), r.val ≤ (popcount a.val : ℤ) + (popcount b.val : ℤ) + (popcount c.val : ℤ)) := by
    sorry

  /-- For every such k, the value returned for inputs (a,b,c) equals the value returned for inputs (2^k * a, 2^k * b, 2^k * c).
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000, and for an integer k >= 0, 1 <= 2^k * a <= 1000000000, 1 <= 2^k * b <= 1000000000, 1 <= 2^k * c <= 1000000000. -/
  theorem spec_11 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (k : ℕ)
      (hka_lo : 1 ≤ 2 ^ k * a.val) (hka_hi : 2 ^ k * a.val ≤ 1000000000)
      (hkb_lo : 1 ≤ 2 ^ k * b.val) (hkb_hi : 2 ^ k * b.val ≤ 1000000000)
      (hkc_lo : 1 ≤ 2 ^ k * c.val) (hkc_hi : 2 ^ k * c.val ≤ 1000000000) :
      Aegis.MinFlips.min_flips a b c
        = Aegis.MinFlips.min_flips (i64Of (2 ^ k * a.val)) (i64Of (2 ^ k * b.val))
            (i64Of (2 ^ k * c.val)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (k : ℕ)
        (hka_lo : 1 ≤ 2 ^ k * a.val) (hka_hi : 2 ^ k * a.val ≤ 1000000000)
        (hkb_lo : 1 ≤ 2 ^ k * b.val) (hkb_hi : 2 ^ k * b.val ≤ 1000000000)
        (hkc_lo : 1 ≤ 2 ^ k * c.val) (hkc_hi : 2 ^ k * c.val ≤ 1000000000), Aegis.MinFlips.min_flips a b c
          = Aegis.MinFlips.min_flips (i64Of (2 ^ k * a.val)) (i64Of (2 ^ k * b.val))
              (i64Of (2 ^ k * c.val))) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers x and y such that (x OR y) = c and the total number of bit positions i >= 0 with bit_i(x) != bit_i(a) plus the total number of bit positions i >= 0 with bit_i(y) != bit_i(b) is exactly r.
    Preconditions: 1 <= a <= 1000000000, 1 <= b <= 1000000000, 1 <= c <= 1000000000. For a nonnegative integer n and integer i >= 0, bit_i(n) = floor(n / 2^i) mod 2. -/
  theorem spec_12 (a b c : Std.I64)
      (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
      (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
      (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
      (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r) :
      ∃ x y : ℕ, bor x y = c.val ∧ (totalFlips x y a.val b.val : ℤ) = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha_lo : 1 ≤ a.val) (ha_hi : a.val ≤ 1000000000)
        (hb_lo : 1 ≤ b.val) (hb_hi : b.val ≤ 1000000000)
        (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 1000000000)
        (r : Std.I64) (hr : Aegis.MinFlips.min_flips a b c = ok r), ∃ x y : ℕ, bor x y = c.val ∧ (totalFlips x y a.val b.val : ℤ) = r.val) := by
    sorry

  end AegisSpec.MinFlips
