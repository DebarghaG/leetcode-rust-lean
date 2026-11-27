import Aegis.GetRow.Code.Funs

/-!
# Specifications of `Aegis.GetRow.get_row`

LeetCode problem `pascals-triangle-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetRow

def entry? (r : alloc.vec.Vec Std.I64) (j : Nat) : Option Int :=
  (r.val[j]?).map (fun x => x.val)

def entry (r : alloc.vec.Vec Std.I64) (j : Nat) : Int :=
  (entry? r j).getD 0

def rowSum (r : alloc.vec.Vec Std.I64) (n : Nat) : Int :=
  ((List.range (n + 1)).map (entry r)).sum

def rowAltSum (r : alloc.vec.Vec Std.I64) (n : Nat) : Int :=
  ((List.range (n + 1)).map (fun j => (-1 : Int) ^ j * entry r j)).sum

def binom (n j : Nat) : Int := (Nat.choose n j : Int)

/-- get_row rowIndex returns Result.ok r (so it does not fail) for a vector r of length rowIndex + 1 such that, for every j with 0 <= j <= rowIndex, r[j] is the binomial coefficient C(rowIndex, j) = rowIndex! / (j! * (rowIndex - j)!), equivalently the number of j-element subsets of a rowIndex-element set. Thus r is exactly the 0-indexed rowIndex-th row of Pascal's triangle, with columns numbered from 0.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_1 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r ∧
        r.val.length = rowIndex.val.toNat + 1 ∧
        ∀ j : Nat, j ≤ rowIndex.val.toNat →
          entry? r j = some (binom rowIndex.val.toNat j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r ∧
        r.val.length = rowIndex.val.toNat + 1 ∧
        ∀ j : Nat, j ≤ rowIndex.val.toNat →
          entry? r j = some (binom rowIndex.val.toNat j)) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r, len(r) = rowIndex + 1.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_2 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r → r.val.length = rowIndex.val.toNat + 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r → r.val.length = rowIndex.val.toNat + 1) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the first entry is 1: r[0] = 1.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_3 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 → entry? r 0 = some 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 → entry? r 0 = some 1) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the last entry is 1: r[rowIndex] = 1.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_4 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          entry? r rowIndex.val.toNat = some 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          entry? r rowIndex.val.toNat = some 1) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the row is symmetric: for every j with 0 <= j <= rowIndex, r[j] = r[rowIndex - j].
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_5 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat, j ≤ rowIndex.val.toNat →
            entry? r j = entry? r (rowIndex.val.toNat - j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat, j ≤ rowIndex.val.toNat →
            entry? r j = entry? r (rowIndex.val.toNat - j)) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the sum of its entries is 2^rowIndex: sum_{j=0}^{rowIndex} r[j] = 2^rowIndex, using mathematical integer sum and exponentiation.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_6 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          rowSum r rowIndex.val.toNat = 2 ^ rowIndex.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          rowSum r rowIndex.val.toNat = 2 ^ rowIndex.val.toNat) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, its alternating sum is sum_{j=0}^{rowIndex} (-1)^j * r[j] = (if rowIndex = 0 then 1 else 0).
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_7 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          rowAltSum r rowIndex.val.toNat = if rowIndex.val = 0 then 1 else 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          rowAltSum r rowIndex.val.toNat = if rowIndex.val = 0 then 1 else 0) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, every entry is positive: for every j with 0 <= j <= rowIndex, r[j] >= 1.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_8 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat, j ≤ rowIndex.val.toNat → 1 ≤ entry r j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat, j ≤ rowIndex.val.toNat → 1 ≤ entry r j) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the center entry is a maximum: for every j with 0 <= j <= rowIndex, r[j] <= r[floor(rowIndex/2)], where floor is integer division.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_9 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j ≤ rowIndex.val.toNat → entry r j ≤ entry r (rowIndex.val.toNat / 2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j ≤ rowIndex.val.toNat → entry r j ≤ entry r (rowIndex.val.toNat / 2)) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the row is nondecreasing up to its center: for every j with 0 <= j < rowIndex and 2*j + 1 <= rowIndex, r[j] <= r[j+1].
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_10 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              2 * j + 1 ≤ rowIndex.val.toNat → entry r j ≤ entry r (j + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              2 * j + 1 ≤ rowIndex.val.toNat → entry r j ≤ entry r (j + 1)) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, the row is nonincreasing after its center: for every j with 0 <= j < rowIndex and 2*j + 1 >= rowIndex, r[j] >= r[j+1].
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_11 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              rowIndex.val.toNat ≤ 2 * j + 1 → entry r (j + 1) ≤ entry r j := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              rowIndex.val.toNat ≤ 2 * j + 1 → entry r (j + 1) ≤ entry r j) := by
  sorry

/-- Whenever get_row rowIndex returns Result.ok r with len(r) = rowIndex + 1, adjacent entries satisfy the Pascal ratio relation: for every j with 0 <= j < rowIndex, r[j] * (rowIndex - j) = r[j+1] * (j + 1).
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_12 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              entry r j * (rowIndex.val - (j : Int)) =
                entry r (j + 1) * ((j : Int) + 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.GetRow.get_row rowIndex = Result.ok r →
        r.val.length = rowIndex.val.toNat + 1 →
          ∀ j : Nat,
            j < rowIndex.val.toNat →
              entry r j * (rowIndex.val - (j : Int)) =
                entry r (j + 1) * ((j : Int) + 1)) := by
  sorry

/-- For every rowIndex satisfying 0 <= rowIndex <= 33, get_row rowIndex returns some Result.ok r; in particular it does not fail due to integer overflow, out-of-bounds access, or panic.
  Preconditions: rowIndex is an integer satisfying 0 <= rowIndex <= 33. -/
theorem spec_13 (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.GetRow.get_row rowIndex = Result.ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (rowIndex : Std.I64) (h0 : 0 ≤ rowIndex.val) (h33 : rowIndex.val ≤ 33), ∃ r : alloc.vec.Vec Std.I64, Aegis.GetRow.get_row rowIndex = Result.ok r) := by
  sorry

end AegisSpec.GetRow
