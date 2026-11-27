import Aegis.CreateSortedArray.Code.Funs

/-!
# Specifications of `Aegis.CreateSortedArray.create_sorted_array`

LeetCode problem `create-sorted-array-through-instructions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CreateSortedArray (create_sorted_array)

namespace AegisSpec.CreateSortedArray

def slen (instructions : Slice Std.I64) : Nat := instructions.val.length

def sget (instructions : Slice Std.I64) (i : Nat) : Int :=
  (instructions.val.getD i 0#i64).val

def lessCount (instructions : Slice Std.I64) (i : Nat) : Nat :=
  ((List.range i).filter (fun j => sget instructions j < sget instructions i)).length

def greaterCount (instructions : Slice Std.I64) (i : Nat) : Nat :=
  ((List.range i).filter (fun j => sget instructions i < sget instructions j)).length

def totalCost (instructions : Slice Std.I64) : Nat :=
  ((List.range (slen instructions)).map
      (fun i => min (lessCount instructions i) (greaterCount instructions i))).sum

def reducedCost (instructions : Slice Std.I64) : Int :=
  (totalCost instructions : Int) % 1000000007

def Pre (instructions : Slice Std.I64) : Prop :=
  1 ≤ slen instructions ∧ slen instructions ≤ 100000 ∧
    ∀ i, i < slen instructions →
      1 ≤ sget instructions i ∧ sget instructions i ≤ 100000

def strictlyBetween (a x b : Int) : Prop := (a < x ∧ x < b) ∨ (b < x ∧ x < a)

/-- Let n = len(instructions). For each i with 0 <= i < n, let L_i be the number of indices j with 0 <= j < i and instructions[j] < instructions[i], and let G_i be the number of indices j with 0 <= j < i and instructions[j] > instructions[i]. The function returns a result r, and r = (sum_{i=0}^{n-1} min(L_i, G_i)) mod 1000000007, where the modulo result is the unique integer in [0, 1000000006] congruent to the sum modulo 1000000007.
  Preconditions: 1 <= len(instructions) <= 100000, and for every i with 0 <= i < len(instructions), 1 <= instructions[i] <= 100000. -/
theorem spec_1 (instructions : Slice Std.I64) (h : Pre instructions) :
    ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ r.val = reducedCost instructions := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (instructions : Slice Std.I64) (h : Pre instructions), ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ r.val = reducedCost instructions) := by
  sorry

/-- The function returns a result r; it does not fail by arithmetic overflow, panic, or out-of-bounds access.
  Preconditions: 1 <= len(instructions) <= 100000, and for every i with 0 <= i < len(instructions), 1 <= instructions[i] <= 100000. -/
theorem spec_2 (instructions : Slice Std.I64) (h : Pre instructions) :
    ∃ r : Std.I64, create_sorted_array instructions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (instructions : Slice Std.I64) (h : Pre instructions), ∃ r : Std.I64, create_sorted_array instructions = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= 1000000006.
  Preconditions: 1 <= len(instructions) <= 100000, and for every i with 0 <= i < len(instructions), 1 <= instructions[i] <= 100000. -/
theorem spec_3 (instructions : Slice Std.I64) (h : Pre instructions) :
    ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (instructions : Slice Std.I64) (h : Pre instructions), ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- The function returns r = 0.
  Preconditions: len(instructions) = 1 and 1 <= instructions[0] <= 100000. -/
theorem spec_4 (instructions : Slice Std.I64) (hlen : slen instructions = 1)
    (h0 : 1 ≤ sget instructions 0 ∧ sget instructions 0 ≤ 100000) :
    ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (instructions : Slice Std.I64) (hlen : slen instructions = 1)
    (h0 : 1 ≤ sget instructions 0 ∧ sget instructions 0 ≤ 100000), ∃ r : Std.I64, create_sorted_array instructions = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r and r = 1 exactly when instructions[2] is strictly between instructions[0] and instructions[1], meaning (instructions[0] < instructions[2] and instructions[2] < instructions[1]) or (instructions[1] < instructions[2] and instructions[2] < instructions[0]); otherwise r = 0.
  Preconditions: len(instructions) = 3, and 1 <= instructions[0], instructions[1], instructions[2] <= 100000. -/
theorem spec_5 (instructions : Slice Std.I64) (hlen : slen instructions = 3)
    (h0 : 1 ≤ sget instructions 0 ∧ sget instructions 0 ≤ 100000)
    (h1 : 1 ≤ sget instructions 1 ∧ sget instructions 1 ≤ 100000)
    (h2 : 1 ≤ sget instructions 2 ∧ sget instructions 2 ≤ 100000) :
    ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        (r.val = 1 ↔
          strictlyBetween (sget instructions 0) (sget instructions 2) (sget instructions 1)) ∧
        (¬ strictlyBetween (sget instructions 0) (sget instructions 2) (sget instructions 1) →
          r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (instructions : Slice Std.I64) (hlen : slen instructions = 3)
    (h0 : 1 ≤ sget instructions 0 ∧ sget instructions 0 ≤ 100000)
    (h1 : 1 ≤ sget instructions 1 ∧ sget instructions 1 ≤ 100000)
    (h2 : 1 ≤ sget instructions 2 ∧ sget instructions 2 ≤ 100000), ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        (r.val = 1 ↔
          strictlyBetween (sget instructions 0) (sget instructions 2) (sget instructions 1)) ∧
        (¬ strictlyBetween (sget instructions 0) (sget instructions 2) (sget instructions 1) →
          r.val = 0)) := by
  sorry

/-- Whenever create_sorted_array(A) returns rA and create_sorted_array(B) returns rB, we have rA = rB.
  Preconditions: Let A be a slice with 1 <= len(A) <= 99999 and 1 <= A[j] <= 100000 for every j. Let x be an integer with 1 <= x <= 100000 such that either x <= A[j] for every j, or x >= A[j] for every j. Let B be the slice obtained by appending x to A, so len(B) = len(A) + 1. -/
theorem spec_6 (A B : Slice Std.I64) (x rA rB : Std.I64)
    (hlenA : 1 ≤ slen A ∧ slen A ≤ 99999)
    (hboundsA : ∀ j, j < slen A → 1 ≤ sget A j ∧ sget A j ≤ 100000)
    (hx : 1 ≤ x.val ∧ x.val ≤ 100000)
    (hxext : (∀ j, j < slen A → x.val ≤ sget A j) ∨ (∀ j, j < slen A → sget A j ≤ x.val))
    (hBapp : B.val = A.val ++ [x])
    (hAret : create_sorted_array A = ok rA) (hBret : create_sorted_array B = ok rB) :
    rA = rB := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (A B : Slice Std.I64) (x rA rB : Std.I64)
    (hlenA : 1 ≤ slen A ∧ slen A ≤ 99999)
    (hboundsA : ∀ j, j < slen A → 1 ≤ sget A j ∧ sget A j ≤ 100000)
    (hx : 1 ≤ x.val ∧ x.val ≤ 100000)
    (hxext : (∀ j, j < slen A → x.val ≤ sget A j) ∨ (∀ j, j < slen A → sget A j ≤ x.val))
    (hBapp : B.val = A.val ++ [x])
    (hAret : create_sorted_array A = ok rA) (hBret : create_sorted_array B = ok rB), rA = rB) := by
  sorry

/-- Let n = len(instructions), and let T = sum_{i=0}^{n-1} min(L_i, G_i), with L_i and G_i defined as in spec_1. The function returns r with r = T mod 1000000007, and moreover T <= floor(((n-1)^2)/4).
  Preconditions: 1 <= len(instructions) <= 100000, and for every i with 0 <= i < len(instructions), 1 <= instructions[i] <= 100000. -/
theorem spec_7 (instructions : Slice Std.I64) (h : Pre instructions) :
    ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        r.val = reducedCost instructions ∧
        totalCost instructions ≤ (slen instructions - 1) ^ 2 / 4 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (instructions : Slice Std.I64) (h : Pre instructions), ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        r.val = reducedCost instructions ∧
        totalCost instructions ≤ (slen instructions - 1) ^ 2 / 4) := by
  sorry

/-- Let n = len(instructions), and let T = sum_{i=0}^{n-1} min(L_i, G_i), with L_i and G_i defined as in spec_1. The function returns r with r = T mod 1000000007. Also, T = 0 if and only if for every i with 0 <= i < n, either (for every j with 0 <= j < i, instructions[j] <= instructions[i]) or (for every j with 0 <= j < i, instructions[j] >= instructions[i]).
  Preconditions: 1 <= len(instructions) <= 100000, and for every i with 0 <= i < len(instructions), 1 <= instructions[i] <= 100000. -/
theorem spec_8 (instructions : Slice Std.I64) (h : Pre instructions) :
    ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        r.val = reducedCost instructions ∧
        (totalCost instructions = 0 ↔
          ∀ i, i < slen instructions →
            (∀ j, j < i → sget instructions j ≤ sget instructions i) ∨
              (∀ j, j < i → sget instructions j ≥ sget instructions i)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (instructions : Slice Std.I64) (h : Pre instructions), ∃ r : Std.I64,
      create_sorted_array instructions = ok r ∧
        r.val = reducedCost instructions ∧
        (totalCost instructions = 0 ↔
          ∀ i, i < slen instructions →
            (∀ j, j < i → sget instructions j ≤ sget instructions i) ∨
              (∀ j, j < i → sget instructions j ≥ sget instructions i))) := by
  sorry

end AegisSpec.CreateSortedArray
