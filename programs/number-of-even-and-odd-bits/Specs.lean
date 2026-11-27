import Aegis.EvenOddBit.Code.Funs

/-!
# Specifications of `Aegis.EvenOddBit.even_odd_bit`

LeetCode problem `number-of-even-and-odd-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.EvenOddBit

  def bit (n : Int) (i : Nat) : Int := (n / 2 ^ i) % 2

  def bitIndices : Finset Nat := Finset.range 64

  def countOnes (n : Int) (P : Nat → Prop) [DecidablePred P] : Int :=
    ((bitIndices.filter P).filter (fun i => bit n i = 1)).card

  def even_count (n : Int) : Int := countOnes n (fun i => i % 2 = 0)

  def odd_count (n : Int) : Int := countOnes n (fun i => i % 2 = 1)

  def popcount (n : Int) : Int := countOnes n (fun _ => True)

  def alt_sum (n : Int) : Int :=
    ((bitIndices.filter (fun i => bit n i = 1))).sum (fun i => (-1 : Int) ^ i)

  /-- The function returns a result r such that len(r) = 2, r[0] = even_count(n), and r[1] = odd_count(n), where even_count(n) is the number of indices i with i >= 0, i even, and (n / 2^i) mod 2 = 1, and odd_count(n) is the number of indices i with i >= 0, i odd, and (n / 2^i) mod 2 = 1. Here / denotes integer division.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_1 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r ∧
        r.val.length = 2 ∧
        (r.val[0]!).val = even_count n.val ∧
        (r.val[1]!).val = odd_count n.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r ∧
          r.val.length = 2 ∧
          (r.val[0]!).val = even_count n.val ∧
          (r.val[1]!).val = odd_count n.val) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_2 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.EvenOddBit.even_odd_bit n = ok r → r.val.length = 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.EvenOddBit.even_odd_bit n = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r[0] <= 5 and 0 <= r[1] <= 5.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_3 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        0 ≤ (r.val[0]!).val ∧ (r.val[0]!).val ≤ 5 ∧
          0 ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ 5 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          0 ≤ (r.val[0]!).val ∧ (r.val[0]!).val ≤ 5 ∧
            0 ≤ (r.val[1]!).val ∧ (r.val[1]!).val ≤ 5) := by
    sorry

  /-- Whenever the function returns a result r, r[0] + r[1] = popcount(n), where popcount(n) is the number of indices i >= 0 such that (n / 2^i) mod 2 = 1.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_4 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val + (r.val[1]!).val = popcount n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val + (r.val[1]!).val = popcount n.val) := by
    sorry

  /-- Whenever the function returns a result r, r[0] - r[1] = alt_sum(n), where alt_sum(n) is the sum over all i >= 0 with (n / 2^i) mod 2 = 1 of (-1)^i.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_5 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val - (r.val[1]!).val = alt_sum n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val - (r.val[1]!).val = alt_sum n.val) := by
    sorry

  /-- Whenever the function returns a result r, r[0] > 0 if and only if there exists an even index i >= 0 such that (n / 2^i) mod 2 = 1.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_6 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (0 < (r.val[0]!).val ↔ ∃ i : Nat, i % 2 = 0 ∧ bit n.val i = 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (0 < (r.val[0]!).val ↔ ∃ i : Nat, i % 2 = 0 ∧ bit n.val i = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r[1] > 0 if and only if there exists an odd index i >= 0 such that (n / 2^i) mod 2 = 1.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_7 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (0 < (r.val[1]!).val ↔ ∃ i : Nat, i % 2 = 1 ∧ bit n.val i = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (0 < (r.val[1]!).val ↔ ∃ i : Nat, i % 2 = 1 ∧ bit n.val i = 1)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow).
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_8 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.EvenOddBit.even_odd_bit n = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.EvenOddBit.even_odd_bit n = ok r) := by
    sorry

  /-- Let m = n / 2. Whenever the function returns a result r for n, we have r[0] = odd_count(m) and r[1] = even_count(m), where even_count(m) is the number of even indices i with (m / 2^i) mod 2 = 1, and odd_count(m) is the number of odd indices i with (m / 2^i) mod 2 = 1.
    Preconditions: The parameter n is an integer with 2 <= n <= 1000 and n is even. -/
  theorem spec_9 (n : Std.I64) (hpos : 2 ≤ n.val) (hle : n.val ≤ 1000) (heven : Even n.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val = odd_count (n.val / 2) ∧
          (r.val[1]!).val = even_count (n.val / 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hpos : 2 ≤ n.val) (hle : n.val ≤ 1000) (heven : Even n.val), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val = odd_count (n.val / 2) ∧
            (r.val[1]!).val = even_count (n.val / 2)) := by
    sorry

  /-- Let m = (n - 1) / 2. Whenever the function returns a result r for n, we have r[0] = 1 + odd_count(m) and r[1] = even_count(m), where even_count(m) is the number of even indices i with (m / 2^i) mod 2 = 1, and odd_count(m) is the number of odd indices i with (m / 2^i) mod 2 = 1.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000 and n is odd. -/
  theorem spec_10 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) (hodd : Odd n.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val = 1 + odd_count ((n.val - 1) / 2) ∧
          (r.val[1]!).val = even_count ((n.val - 1) / 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) (hodd : Odd n.val), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val = 1 + odd_count ((n.val - 1) / 2) ∧
            (r.val[1]!).val = even_count ((n.val - 1) / 2)) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = sum_{i in {0,2,4,6,8}} ((n / 2^i) mod 2) and r[1] = sum_{i in {1,3,5,7,9}} ((n / 2^i) mod 2).
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_11 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val = ({0, 2, 4, 6, 8} : Finset Nat).sum (fun i => bit n.val i) ∧
          (r.val[1]!).val = ({1, 3, 5, 7, 9} : Finset Nat).sum (fun i => bit n.val i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val = ({0, 2, 4, 6, 8} : Finset Nat).sum (fun i => bit n.val i) ∧
            (r.val[1]!).val = ({1, 3, 5, 7, 9} : Finset Nat).sum (fun i => bit n.val i)) := by
    sorry

  /-- Whenever the function returns a result r, r[0] + r[1] <= 9.
    Preconditions: The parameter n is an integer with 1 <= n <= 1000. -/
  theorem spec_12 (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.EvenOddBit.even_odd_bit n = ok r →
        (r.val[0]!).val + (r.val[1]!).val ≤ 9 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hpos : 1 ≤ n.val) (hle : n.val ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
        Aegis.EvenOddBit.even_odd_bit n = ok r →
          (r.val[0]!).val + (r.val[1]!).val ≤ 9) := by
    sorry

  end AegisSpec.EvenOddBit
