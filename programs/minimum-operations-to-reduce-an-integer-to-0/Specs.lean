import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-reduce-an-integer-to-0`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std
open Aeneas.Std.Result
open scoped BigOperators

namespace AegisSpec.MinOperations

def pow2 (e : Nat) : Int := (2 : Int) ^ e

def HasSignedExpansion (n : Int) (k : Nat) : Prop :=
  ∃ (e : Fin k → Nat) (s : Fin k → Int),
    (∀ i, s i = 1 ∨ s i = -1) ∧ n = ∑ i, s i * pow2 (e i)

def IsMinSignedExpansionLength (n : Int) (r : Nat) : Prop :=
  HasSignedExpansion n r ∧ ∀ k : Nat, HasSignedExpansion n k → r ≤ k

def popcount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun i => n.testBit i)).length

def bitRuns (n : Nat) : Nat :=
  ((List.range (n + 1)).filter
      (fun i => n.testBit i && (i == 0 || !(n.testBit (i - 1))))).length

/-- Whenever the function returns a result r, r is the least nonnegative integer k for which there exist exponents e_0, …, e_{k−1} with each e_i ≥ 0 and signs s_0, …, s_{k−1} ∈ {−1, +1} such that n = Σ_{i=0}^{k−1} s_i · 2^{e_i}. Equivalently, r is the minimum number of operations, each adding or subtracting one power of two, needed to change n into 0.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      0 ≤ r.val ∧ IsMinSignedExpansionLength n.val r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      0 ≤ r.val ∧ IsMinSignedExpansionLength n.val r.val.toNat) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any n in this range.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∃ r : Std.I64, Aegis.MinOperations.min_operations n = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every nonnegative integer k and every choice of k exponents e_0, …, e_{k−1} ≥ 0 and signs s_0, …, s_{k−1} ∈ {−1, +1} satisfying n = Σ_{i=0}^{k−1} s_i · 2^{e_i}, one has r ≤ k.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ (k : Nat) (e : Fin k → Nat) (s : Fin k → Int),
        (∀ i, s i = 1 ∨ s i = -1) → n.val = ∑ i, s i * pow2 (e i) → r.val ≤ (k : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ (k : Nat) (e : Fin k → Nat) (s : Fin k → Int),
        (∀ i, s i = 1 ∨ s i = -1) → n.val = ∑ i, s i * pow2 (e i) → r.val ≤ (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exist exponents e_0, …, e_{r−1} ≥ 0 and signs s_0, …, s_{r−1} ∈ {−1, +1} such that n = Σ_{i=0}^{r−1} s_i · 2^{e_i}.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      HasSignedExpansion n.val r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      HasSignedExpansion n.val r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, r ≥ 1.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r → 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r ≤ popcount(n), where popcount(n) is the number of indices i ≥ 0 such that the i-th binary digit of n is 1, equivalently the number of summands in the binary expansion n = Σ_i b_i 2^i with b_i ∈ {0,1}.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      r.val ≤ (popcount n.val.toNat : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      r.val ≤ (popcount n.val.toNat : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if there exists an integer j ≥ 0 such that n = 2^j.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      (r.val = 1 ↔ ∃ j : Nat, n.val = pow2 j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      (r.val = 1 ↔ ∃ j : Nat, n.val = pow2 j)) := by
  sorry

/-- Whenever the function returns a result r, if there exist integers a and b with 0 ≤ a < b and n = 2^a + 2^b, then r = 2.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ a b : Nat, a < b → n.val = pow2 a + pow2 b → r.val = 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ a b : Nat, a < b → n.val = pow2 a + pow2 b → r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, if there exists an integer q ≥ 2 such that n = 2^q − 1, then r = 2.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ q : Nat, 2 ≤ q → n.val = pow2 q - 1 → r.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      ∀ q : Nat, 2 ≤ q → n.val = pow2 q - 1 → r.val = 2) := by
  sorry

/-- Let t ≥ 0 be the largest integer such that 2^t divides n, and let m = n / 2^t be the odd part of n. Whenever the function returns a result r on input n and a result r_m on input m, one has r = r_m.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_10 (n m : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (t : Nat) (hdiv : pow2 t ∣ n.val) (hmax : ∀ s : Nat, pow2 s ∣ n.val → s ≤ t)
    (hm : m.val = n.val / pow2 t) :
    ∀ r r_m : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations m = ok r_m → r.val = r_m.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n m : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (t : Nat) (hdiv : pow2 t ∣ n.val) (hmax : ∀ s : Nat, pow2 s ∣ n.val → s ≤ t)
    (hm : m.val = n.val / pow2 t), ∀ r r_m : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations m = ok r_m → r.val = r_m.val) := by
  sorry

/-- For every odd n with n ≥ 3, if the function returns r on input n, a on input (n − 1)/2, and b on input (n + 1)/2, then r = 1 + min(a, b).
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_11 (n : Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hodd : n.val % 2 = 1) :
    ∀ (n_lo n_hi r a b : Std.I64), n_lo.val = (n.val - 1) / 2 → n_hi.val = (n.val + 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_lo = ok a →
      Aegis.MinOperations.min_operations n_hi = ok b →
      r.val = 1 + min a.val b.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hodd : n.val % 2 = 1), ∀ (n_lo n_hi r a b : Std.I64), n_lo.val = (n.val - 1) / 2 → n_hi.val = (n.val + 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_lo = ok a →
      Aegis.MinOperations.min_operations n_hi = ok b →
      r.val = 1 + min a.val b.val) := by
  sorry

/-- If the function returns r on input x + y, r_x on input x, and r_y on input y, then r ≤ r_x + r_y.
  Preconditions: 1 ≤ x, 1 ≤ y, and x + y ≤ 100000, so the inputs x, y, and x+y all satisfy the problem constraint. -/
theorem spec_12 (x y s : Std.I64) (hx1 : 1 ≤ x.val) (hy1 : 1 ≤ y.val)
    (hxy : x.val + y.val ≤ 100000) (hs : s.val = x.val + y.val) :
    ∀ r r_x r_y : Std.I64, Aegis.MinOperations.min_operations s = ok r →
      Aegis.MinOperations.min_operations x = ok r_x →
      Aegis.MinOperations.min_operations y = ok r_y → r.val ≤ r_x.val + r_y.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (x y s : Std.I64) (hx1 : 1 ≤ x.val) (hy1 : 1 ≤ y.val)
    (hxy : x.val + y.val ≤ 100000) (hs : s.val = x.val + y.val), ∀ r r_x r_y : Std.I64, Aegis.MinOperations.min_operations s = ok r →
      Aegis.MinOperations.min_operations x = ok r_x →
      Aegis.MinOperations.min_operations y = ok r_y → r.val ≤ r_x.val + r_y.val) := by
  sorry

/-- For every n with n ≥ 5 and n mod 4 = 1, if the function returns r on input n and r_halve on input (n − 1)/2, then r = 1 + r_halve.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_13 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hmod : n.val % 4 = 1) :
    ∀ (n_halve r r_halve : Std.I64), n_halve.val = (n.val - 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_halve = ok r_halve → r.val = 1 + r_halve.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hmod : n.val % 4 = 1), ∀ (n_halve r r_halve : Std.I64), n_halve.val = (n.val - 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_halve = ok r_halve → r.val = 1 + r_halve.val) := by
  sorry

/-- For every n with n ≥ 3 and n mod 4 = 3, if the function returns r on input n and r_halve on input (n + 1)/2, then r = 1 + r_halve.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_14 (n : Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hmod : n.val % 4 = 3) :
    ∀ (n_halve r r_halve : Std.I64), n_halve.val = (n.val + 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_halve = ok r_halve → r.val = 1 + r_halve.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hmod : n.val % 4 = 3), ∀ (n_halve r r_halve : Std.I64), n_halve.val = (n.val + 1) / 2 →
      Aegis.MinOperations.min_operations n = ok r →
      Aegis.MinOperations.min_operations n_halve = ok r_halve → r.val = 1 + r_halve.val) := by
  sorry

/-- Whenever the function returns a result r, r ≤ 2·C(n), where C(n) is the number of maximal runs of consecutive 1-bits in the binary expansion of n.
  Preconditions: 1 ≤ n ≤ 100000. -/
theorem spec_15 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      r.val ≤ 2 * (bitRuns n.val.toNat : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000), ∀ r : Std.I64, Aegis.MinOperations.min_operations n = ok r →
      r.val ≤ 2 * (bitRuns n.val.toNat : Int)) := by
  sorry

end AegisSpec.MinOperations
