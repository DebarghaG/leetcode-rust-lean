import Aegis.CountBits.Code.Funs

/-!
# Specifications of `Aegis.CountBits.count_bits`

LeetCode problem `counting-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountBits

open Aegis.CountBits

def onesCount (i : ℤ) : ℕ :=
  ((Finset.range (i.toNat + 1)).filter (fun k => (i / (2 : ℤ) ^ k) % 2 = 1)).card

def isPowerOfTwo (i : ℤ) : Prop := ∃ k : ℕ, i = (2 : ℤ) ^ k

/-- The function returns a result r such that len(r) = n + 1, and for every integer i with 0 <= i <= n, the integer value of r[i] is the number of 1s in the binary representation of i, i.e. the number of positions k >= 0 such that floor(i / 2^k) mod 2 = 1.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_1 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64,
      count_bits n = ok r ∧
        r.val.length = n.val.toNat + 1 ∧
          ∀ i : ℤ, 0 ≤ i → i ≤ n.val → (r.val[i.toNat]!).val = (onesCount i : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
      count_bits n = ok r ∧
        r.val.length = n.val.toNat + 1 ∧
          ∀ i : ℤ, 0 ≤ i → i ≤ n.val → (r.val[i.toNat]!).val = (onesCount i : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail by integer overflow, out-of-bounds access, or panic.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_2 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64, count_bits n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, count_bits n = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n + 1.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_3 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r) :
    r.val.length = n.val.toNat + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r), r.val.length = n.val.toNat + 1) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 0 <= i <= n, 0 <= (integer value of r[i]) <= 17.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_4 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 0 ≤ (r.val[i.toNat]!).val ∧ (r.val[i.toNat]!).val ≤ 17 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 0 ≤ (r.val[i.toNat]!).val ∧ (r.val[i.toNat]!).val ≤ 17) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 1 <= i <= n, the integer value of r[i] equals (the integer value of r[floor(i/2)]) + (i mod 2).
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_5 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
      (r.val[i.toNat]!).val = (r.val[(i / 2).toNat]!).val + i % 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 1 ≤ i → i ≤ n.val →
      (r.val[i.toNat]!).val = (r.val[(i / 2).toNat]!).val + i % 2) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 0 <= i <= n and 2*i <= n, the integer value of r[2*i] equals the integer value of r[i].
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_6 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 2 * i ≤ n.val →
      (r.val[(2 * i).toNat]!).val = (r.val[i.toNat]!).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 2 * i ≤ n.val →
      (r.val[(2 * i).toNat]!).val = (r.val[i.toNat]!).val) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 0 <= i <= n and 2*i + 1 <= n, the integer value of r[2*i + 1] equals (the integer value of r[i]) + 1.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_7 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 2 * i + 1 ≤ n.val →
      (r.val[(2 * i + 1).toNat]!).val = (r.val[i.toNat]!).val + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 0 ≤ i → i ≤ n.val → 2 * i + 1 ≤ n.val →
      (r.val[(2 * i + 1).toNat]!).val = (r.val[i.toNat]!).val + 1) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, the sum of the integer values of all entries r[0],...,r[n] equals the sum, over i = 0 to n, of the number of 1s in the binary representation of i.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_8 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    (r.val.map (fun x => x.val)).sum
      = ∑ i ∈ Finset.range (n.val.toNat + 1), (onesCount (i : ℤ) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), (r.val.map (fun x => x.val)).sum
      = ∑ i ∈ Finset.range (n.val.toNat + 1), (onesCount (i : ℤ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 0 <= i <= n, the integer value of r[i] = 0 if and only if i = 0.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_9 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 0 ≤ i → i ≤ n.val → ((r.val[i.toNat]!).val = 0 ↔ i = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 0 ≤ i → i ≤ n.val → ((r.val[i.toNat]!).val = 0 ↔ i = 0)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n + 1, for every integer i with 1 <= i <= n, the integer value of r[i] = 1 if and only if there exists an integer k >= 0 such that i = 2^k.
  Preconditions: 0 <= n <= 100000, where n is the integer value of the Std.I64 parameter. -/
theorem spec_10 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1) :
    ∀ i : ℤ, 1 ≤ i → i ≤ n.val → ((r.val[i.toNat]!).val = 1 ↔ isPowerOfTwo i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≤ 100000)
    (r : alloc.vec.Vec Std.I64) (hr : count_bits n = ok r)
    (hlen : r.val.length = n.val.toNat + 1), ∀ i : ℤ, 1 ≤ i → i ≤ n.val → ((r.val[i.toNat]!).val = 1 ↔ isPowerOfTwo i)) := by
  sorry

end AegisSpec.CountBits
