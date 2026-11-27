import Aegis.ReverseBits.Code.Funs

/-!
# Specifications of `Aegis.ReverseBits.reverse_bits`

LeetCode problem `reverse-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReverseBits

  def bitAt (x : ℤ) (i : ℕ) : ℤ :=
    (x / (2 : ℤ) ^ i) % 2

  def reverse32 (x : ℤ) : ℤ :=
    ∑ i ∈ Finset.range 32, bitAt x i * (2 : ℤ) ^ (31 - i)

  def popcount32 (x : ℤ) : ℕ :=
    ((Finset.range 32).filter (fun i => bitAt x i = 1)).card

  def highestBit (x : ℤ) : ℕ :=
    Nat.findGreatest (fun i => bitAt x i = 1) 31

  /-- The function returns a result r and r = sum_{i=0}^{31} b_i * 2^(31-i), where b_i is the i-th least significant bit of n, defined by b_i = ((n / 2^i) mod 2) using integer division. Equivalently, for every i with 0 <= i < 32, the i-th least significant bit of r equals the (31-i)-th least significant bit of n.
    Preconditions: n is an i64 with 0 <= n <= 4294967295 (i.e. n is a 32-bit unsigned integer represented in an i64). -/
  theorem spec_1 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∃ r : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r ∧
          r.val = reverse32 n.val ∧
            ∀ i : ℕ, i < 32 → bitAt r.val i = bitAt n.val (31 - i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∃ r : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r ∧
            r.val = reverse32 n.val ∧
              ∀ i : ℕ, i < 32 → bitAt r.val i = bitAt n.val (31 - i)) := by
    sorry

  /-- The function returns a result r for every such n; it does not panic, fail, or overflow.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_2 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∃ r : Std.I64, Aegis.ReverseBits.reverse_bits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∃ r : Std.I64, Aegis.ReverseBits.reverse_bits n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 4294967295.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_3 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∀ r : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r → 0 <= r.val ∧ r.val <= 4294967295 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∀ r : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r → 0 <= r.val ∧ r.val <= 4294967295) := by
    sorry

  /-- If the function returns r for input n, 0 <= r <= 4294967295, and the function returns s for input r, then s = n.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_4 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∀ r s : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r →
          0 <= r.val →
            r.val <= 4294967295 →
              Aegis.ReverseBits.reverse_bits r = ok s → s.val = n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∀ r s : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r →
            0 <= r.val →
              r.val <= 4294967295 →
                Aegis.ReverseBits.reverse_bits r = ok s → s.val = n.val) := by
    sorry

  /-- Let c = 4294967295 - n. If the function returns r for input n and returns s for input c, then r + s = 4294967295.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_5 (n c : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295)
      (hc : c.val = 4294967295 - n.val) :
      ∀ r s : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r →
          Aegis.ReverseBits.reverse_bits c = ok s → r.val + s.val = 4294967295 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n c : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295)
        (hc : c.val = 4294967295 - n.val), ∀ r s : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r →
            Aegis.ReverseBits.reverse_bits c = ok s → r.val + s.val = 4294967295) := by
    sorry

  /-- If the function returns r, then 0 <= r <= 4294967295 and the number of indices i with 0 <= i < 32 and ((n / 2^i) mod 2) = 1 equals the number of indices i with 0 <= i < 32 and ((r / 2^i) mod 2) = 1.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_6 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∀ r : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r →
          0 <= r.val ∧ r.val <= 4294967295 ∧ popcount32 r.val = popcount32 n.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∀ r : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r →
            0 <= r.val ∧ r.val <= 4294967295 ∧ popcount32 r.val = popcount32 n.val) := by
    sorry

  /-- If the function returns r, then r = 0 if and only if n = 0.
    Preconditions: 0 <= n <= 4294967295. -/
  theorem spec_7 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295) :
      ∀ r : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r → (r.val = 0 ↔ n.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295), ∀ r : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r → (r.val = 0 ↔ n.val = 0)) := by
    sorry

  /-- Let bit_j(x) = ((x / 2^j) mod 2) for 0 <= j < 32. If the function returns r, let h be the largest index i with 0 <= i < 32 and bit_i(n) = 1. Then there exists an index l with 0 <= l < 32 such that bit_l(r) = 1, bit_i(r) = 0 for every i with 0 <= i < l, and h + l = 31.
    Preconditions: 0 <= n <= 4294967295 and n != 0. -/
  theorem spec_8 (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295)
      (hne : n.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReverseBits.reverse_bits n = ok r →
          ∃ l : ℕ,
            l < 32 ∧
              bitAt r.val l = 1 ∧
                (∀ i : ℕ, i < l → bitAt r.val i = 0) ∧ highestBit n.val + l = 31 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 <= n.val) (hn : n.val <= 4294967295)
        (hne : n.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReverseBits.reverse_bits n = ok r →
            ∃ l : ℕ,
              l < 32 ∧
                bitAt r.val l = 1 ∧
                  (∀ i : ℕ, i < l → bitAt r.val i = 0) ∧ highestBit n.val + l = 31) := by
    sorry

  end AegisSpec.ReverseBits
