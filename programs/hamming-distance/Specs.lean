import Aegis.HammingDistance.Code.Funs

/-!
# Specifications of `Aegis.HammingDistance.hamming_distance`

LeetCode problem `hamming-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HammingDistance

def bit (z : ℤ) (k : ℕ) : ℤ := (z / 2 ^ k) % 2

def diffBits (x y : ℤ) : Finset ℕ := (Finset.range 31).filter (fun k => bit x k ≠ bit y k)

def onesBits (z : ℤ) : Finset ℕ := (Finset.range 31).filter (fun k => bit z k = 1)

def popcount (z : ℤ) : ℕ := (onesBits z).card

/-- Whenever hamming_distance(x, y) returns a result r, the integer value of r is the cardinality of the set { k | 0 <= k < 31 and bit_k(x) != bit_k(y) }, where bit_k(z) = (z div 2^k) mod 2 is the k-th least significant bit of z.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_1 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val = ((diffBits x.val y.val).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val = ((diffBits x.val y.val).card : ℤ)) := by
  sorry

/-- For every x and y satisfying the preconditions, hamming_distance(x, y) returns a result r; it does not fail by overflow, panic, or any other runtime error.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_2 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, 0 <= r <= 31.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_3 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r → 0 ≤ r.val ∧ r.val ≤ 31 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r → 0 ≤ r.val ∧ r.val ≤ 31) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r = 0 if and only if x = y.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_4 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r → (r.val = 0 ↔ x = y) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r → (r.val = 0 ↔ x = y)) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r and hamming_distance(y, x) returns a result s, r = s.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_5 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r s : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance y x = ok s → r = s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r s : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance y x = ok s → r = s) := by
  sorry

/-- For every z with 0 <= z <= 2^31 - 1, if hamming_distance(x, y) returns a result r and hamming_distance(x XOR z, y XOR z) returns a result s, then r = s, where XOR denotes bitwise exclusive-or of the 31 low-order bits.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_6 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1)
    (z : I64) (hz0 : 0 ≤ z.val) (hz1 : z.val ≤ 2 ^ 31 - 1) :
    ∀ r s : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance (x ^^^ z) (y ^^^ z) = ok s → r = s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1)
    (z : I64) (hz0 : 0 ≤ z.val) (hz1 : z.val ≤ 2 ^ 31 - 1), ∀ r s : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance (x ^^^ z) (y ^^^ z) = ok s → r = s) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r is the cardinality of the set { k | 0 <= k < 31 and bit_k(y) = 1 }, where bit_k(y) = (y div 2^k) mod 2.
  Preconditions: x = 0 and 0 <= y <= 2^31 - 1, interpreting y as its non-negative integer value. -/
theorem spec_7 (x y : I64)
    (hx : x.val = 0)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val = ((popcount y.val : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (x y : I64)
    (hx : x.val = 0)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val = ((popcount y.val : ℕ) : ℤ)) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r = 31 if and only if for every k with 0 <= k < 31, bit_k(x) != bit_k(y), where bit_k(z) = (z div 2^k) mod 2.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_8 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      (r.val = 31 ↔ ∀ k : ℕ, k < 31 → bit x.val k ≠ bit y.val k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      (r.val = 31 ↔ ∀ k : ℕ, k < 31 → bit x.val k ≠ bit y.val k)) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r = 1 if and only if there exists exactly one k with 0 <= k < 31 such that bit_k(x) != bit_k(y), where bit_k(z) = (z div 2^k) mod 2.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_9 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      (r.val = 1 ↔ ∃! k : ℕ, k < 31 ∧ bit x.val k ≠ bit y.val k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      (r.val = 1 ↔ ∃! k : ℕ, k < 31 ∧ bit x.val k ≠ bit y.val k)) := by
  sorry

/-- For every z with 0 <= z <= 2^31 - 1, if hamming_distance(x, y) returns a result r, hamming_distance(x, z) returns a result s, and hamming_distance(z, y) returns a result t, then r <= s + t.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_10 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1)
    (z : I64) (hz0 : 0 ≤ z.val) (hz1 : z.val ≤ 2 ^ 31 - 1) :
    ∀ r s t : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance x z = ok s →
      Aegis.HammingDistance.hamming_distance z y = ok t → r.val ≤ s.val + t.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1)
    (z : I64) (hz0 : 0 ≤ z.val) (hz1 : z.val ≤ 2 ^ 31 - 1), ∀ r s t : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      Aegis.HammingDistance.hamming_distance x z = ok s →
      Aegis.HammingDistance.hamming_distance z y = ok t → r.val ≤ s.val + t.val) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r <= popcount(x) + popcount(y), where popcount(z) is the cardinality of { k | 0 <= k < 31 and bit_k(z) = 1 } and bit_k(z) = (z div 2^k) mod 2.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_11 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val ≤ ((popcount x.val : ℕ) : ℤ) + ((popcount y.val : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val ≤ ((popcount x.val : ℕ) : ℤ) + ((popcount y.val : ℕ) : ℤ)) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r >= |popcount(x) - popcount(y)|, where popcount(z) is the cardinality of { k | 0 <= k < 31 and bit_k(z) = 1 } and bit_k(z) = (z div 2^k) mod 2.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_12 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      |((popcount x.val : ℕ) : ℤ) - ((popcount y.val : ℕ) : ℤ)| ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      |((popcount x.val : ℕ) : ℤ) - ((popcount y.val : ℕ) : ℤ)| ≤ r.val) := by
  sorry

/-- Whenever hamming_distance(x, y) returns a result r, r mod 2 = (popcount(x) + popcount(y)) mod 2, where popcount(z) is the cardinality of { k | 0 <= k < 31 and bit_k(z) = 1 } and bit_k(z) = (z div 2^k) mod 2.
  Preconditions: 0 <= x <= 2^31 - 1 and 0 <= y <= 2^31 - 1, interpreting x and y as their non-negative integer values. -/
theorem spec_13 (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1) :
    ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val % 2 = (((popcount x.val : ℕ) : ℤ) + ((popcount y.val : ℕ) : ℤ)) % 2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (x y : I64)
    (hx0 : 0 ≤ x.val) (hx1 : x.val ≤ 2 ^ 31 - 1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 2 ^ 31 - 1), ∀ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r →
      r.val % 2 = (((popcount x.val : ℕ) : ℤ) + ((popcount y.val : ℕ) : ℤ)) % 2) := by
  sorry

/-- hamming_distance(x, y) returns a result r and r = 31.
  Preconditions: x = 0 and y = 2^31 - 1. -/
theorem spec_14 (x y : I64)
    (hx : x.val = 0) (hy : y.val = 2 ^ 31 - 1) :
    ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r ∧ r.val = 31 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (x y : I64)
    (hx : x.val = 0) (hy : y.val = 2 ^ 31 - 1), ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r ∧ r.val = 31) := by
  sorry

/-- hamming_distance(x, y) returns a result r and the integer value of r is 1.
  Preconditions: x = 0 and there exists an integer k with 0 <= k < 31 such that y = 2^k, interpreting y as its non-negative integer value. -/
theorem spec_15 (x y : I64)
    (hx : x.val = 0) (hy : ∃ k : ℕ, k < 31 ∧ y.val = 2 ^ k) :
    ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r ∧ r.val = 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (x y : I64)
    (hx : x.val = 0) (hy : ∃ k : ℕ, k < 31 ∧ y.val = 2 ^ k), ∃ r : I64, Aegis.HammingDistance.hamming_distance x y = ok r ∧ r.val = 1) := by
  sorry

end AegisSpec.HammingDistance
