import Aegis.HammingWeight.Code.Funs

/-!
# Specifications of `Aegis.HammingWeight.hamming_weight`

LeetCode problem `number-of-1-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HammingWeight

  def setBits31 (N : Int) : Nat :=
    ((Finset.range 31).filter (fun i => N / (2 : Int) ^ i % 2 = 1)).card

  def IsTwoAdicVal (N : Int) (k : Nat) : Prop :=
    (2 : Int) ^ k ∣ N ∧ ¬ ((2 : Int) ^ (k + 1) ∣ N)

  /-- Let N be the integer value of n. The function returns a result r, and the integer value of r is the number of indices i with 0 <= i < 31 for which floor(N / 2^i) mod 2 = 1. This is exactly the number of set bits in the binary representation of N.
    Preconditions: 1 <= n <= 2147483647 (the problem constraint, since 2147483647 = 2^31 - 1). -/
  theorem spec_1 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647) :
      ∃ r : Aeneas.Std.I64,
        Aegis.HammingWeight.hamming_weight n = ok r ∧ r.val = (setBits31 n.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647), ∃ r : Aeneas.Std.I64,
          Aegis.HammingWeight.hamming_weight n = ok r ∧ r.val = (setBits31 n.val : Int)) := by
    sorry

  /-- For every n with 0 <= n <= 2147483647, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: 0 <= n <= 2147483647. -/
  theorem spec_2 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647) :
      ∃ r : Aeneas.Std.I64, Aegis.HammingWeight.hamming_weight n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647), ∃ r : Aeneas.Std.I64, Aegis.HammingWeight.hamming_weight n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is at least 1.
    Preconditions: 1 <= n <= 2147483647. -/
  theorem spec_3 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if n = 0.
    Preconditions: 0 <= n <= 2147483647. -/
  theorem spec_4 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r) :
      r.val = 0 ↔ n.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r), r.val = 0 ↔ n.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 31 if and only if n = 2147483647.
    Preconditions: 0 <= n <= 2147483647. -/
  theorem spec_5 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r) :
      r.val = 31 ↔ n.val = 2147483647 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r), r.val = 31 ↔ n.val = 2147483647) := by
    sorry

  /-- Whenever the function returns r on input n and returns r' on input 2147483647 - n, the values satisfy r + r' = 31.
    Preconditions: 0 <= n <= 2147483647. -/
  theorem spec_6 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
      (m : Aeneas.Std.I64) (hm : m.val = 2147483647 - n.val)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r') :
      r.val + r'.val = 31 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
        (m : Aeneas.Std.I64) (hm : m.val = 2147483647 - n.val)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r'), r.val + r'.val = 31) := by
    sorry

  /-- Whenever the function returns r on input n and returns r' on input 2*n, the values satisfy r = r'.
    Preconditions: 0 <= n and 2*n <= 2147483647. -/
  theorem spec_7 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ 2 * n.val ≤ 2147483647)
      (m : Aeneas.Std.I64) (hm : m.val = 2 * n.val)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ 2 * n.val ≤ 2147483647)
        (m : Aeneas.Std.I64) (hm : m.val = 2 * n.val)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on input n and returns r' on input n/2, the values satisfy r = r'.
    Preconditions: 0 <= n <= 2147483647 and n is even. -/
  theorem spec_8 (n : Aeneas.Std.I64)
      (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647 ∧ n.val % 2 = 0)
      (m : Aeneas.Std.I64) (hm : m.val = n.val / 2)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64)
        (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647 ∧ n.val % 2 = 0)
        (m : Aeneas.Std.I64) (hm : m.val = n.val / 2)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on input n and returns r' on input n-1, the values satisfy r = r' + 1.
    Preconditions: 1 <= n <= 2147483647 and n is odd. -/
  theorem spec_9 (n : Aeneas.Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647 ∧ n.val % 2 = 1)
      (m : Aeneas.Std.I64) (hm : m.val = n.val - 1)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r') :
      r.val = r'.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Aeneas.Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647 ∧ n.val % 2 = 1)
        (m : Aeneas.Std.I64) (hm : m.val = n.val - 1)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r'), r.val = r'.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, if n < 2^m then r <= m.
    Preconditions: 0 <= n <= 2147483647 and 0 <= m <= 31. -/
  theorem spec_10 (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
      (m : Nat) (hm : 0 ≤ m ∧ m ≤ 31)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (hlt : n.val < (2 : Int) ^ m) :
      r.val ≤ (m : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 0 ≤ n.val ∧ n.val ≤ 2147483647)
        (m : Nat) (hm : 0 ≤ m ∧ m ≤ 31)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (hlt : n.val < (2 : Int) ^ m), r.val ≤ (m : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= n.
    Preconditions: 1 <= n <= 2147483647. -/
  theorem spec_11 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r) :
      r.val ≤ n.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r), r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is 1 if and only if there exists an integer k with 0 <= k < 31 and n = 2^k.
    Preconditions: 1 <= n <= 2147483647 -/
  theorem spec_12 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r) :
      r.val = 1 ↔ ∃ k : Nat, k < 31 ∧ n.val = (2 : Int) ^ k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r), r.val = 1 ↔ ∃ k : Nat, k < 31 ∧ n.val = (2 : Int) ^ k) := by
    sorry

  /-- Let 2^k be the largest power of two dividing n, and let m = n - 2^k. Whenever the function returns r on input n and returns r' on input m, the values satisfy r = r' + 1.
    Preconditions: 1 <= n <= 2147483647 -/
  theorem spec_13 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
      (k : Nat) (hk : IsTwoAdicVal n.val k)
      (m : Aeneas.Std.I64) (hm : m.val = n.val - (2 : Int) ^ k)
      (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
      (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r') :
      r.val = r'.val + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 2147483647)
        (k : Nat) (hk : IsTwoAdicVal n.val k)
        (m : Aeneas.Std.I64) (hm : m.val = n.val - (2 : Int) ^ k)
        (r : Aeneas.Std.I64) (hr : Aegis.HammingWeight.hamming_weight n = ok r)
        (r' : Aeneas.Std.I64) (hr' : Aegis.HammingWeight.hamming_weight m = ok r'), r.val = r'.val + 1) := by
    sorry

  end AegisSpec.HammingWeight
