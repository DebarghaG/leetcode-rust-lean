import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-array-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def initArr (n : ℕ) : Fin n → ℤ := fun i => 2 * (i : ℤ) + 1

def initArrVal (n : ℕ) : List ℤ := (List.range n).map (fun i => 2 * (i : ℤ) + 1)

def applyOp {n : ℕ} (a : Fin n → ℤ) (xy : Fin n × Fin n) : Fin n → ℤ :=
  let a₁ := Function.update a xy.1 (a xy.1 - 1)
  Function.update a₁ xy.2 (a₁ xy.2 + 1)

def runOps {n : ℕ} (a : Fin n → ℤ) (ops : List (Fin n × Fin n)) : Fin n → ℤ :=
  ops.foldl (fun a xy => applyOp a xy) a

def AllEqual {n : ℕ} (a : Fin n → ℤ) : Prop := ∃ c : ℤ, ∀ i, a i = c

def ReachableIn {n : ℕ} (a : Fin n → ℤ) (k : ℕ) : Prop :=
  ∃ ops : List (Fin n × Fin n), ops.length = k ∧ AllEqual (runOps a ops)

def IsMinOps {n : ℕ} (a : Fin n → ℤ) (k : ℕ) : Prop :=
  ReachableIn a k ∧ ∀ j : ℕ, ReachableIn a j → k ≤ j

def IsQuarterFloor (m r : ℤ) : Prop := 4 * r ≤ m ∧ m < 4 * (r + 1)

def sumExcess (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, max 0 (2 * (i : ℤ) + 1 - (n : ℤ))

def sumDeficit (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, max 0 ((n : ℤ) - (2 * (i : ℤ) + 1))

def sumAbsDev (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, |2 * (i : ℤ) + 1 - (n : ℤ)|

def sumFloorHalf (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, ((i : ℤ) / 2)

def pred (n : I64) : I64 := ⟨BitVec.ofInt 64 (n.val - 1)⟩

/-- Let arr be the array of length n with arr[i] = 2*i + 1 for every i with 0 <= i < n. Whenever min_operations n returns a result r, r is the minimum number of operations needed to make all entries of arr equal, where one operation chooses indices x and y with 0 <= x,y < n and performs arr[x] := arr[x] - 1 and arr[y] := arr[y] + 1. Equivalently, r is the unique integer satisfying 4*r <= n*n < 4*(r+1).
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_1 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    IsMinOps (initArr n.val.toNat) r.val.toNat ∧
      IsQuarterFloor (n.val * n.val) r.val ∧
      (∀ r' : ℤ, IsQuarterFloor (n.val * n.val) r' → r' = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), IsMinOps (initArr n.val.toNat) r.val.toNat ∧
      IsQuarterFloor (n.val * n.val) r.val ∧
      (∀ r' : ℤ, IsQuarterFloor (n.val * n.val) r' → r' = r.val)) := by
  sorry

/-- For every integer n with 1 <= n <= 10000, min_operations n returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_2 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∃ r : I64, Aegis.MinOperations.min_operations n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∃ r : I64, Aegis.MinOperations.min_operations n = ok r) := by
  sorry

/-- Whenever min_operations n returns a result r, 0 <= r <= 25000000.
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_3 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    0 ≤ r.val ∧ r.val ≤ 25000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), 0 ≤ r.val ∧ r.val ≤ 25000000) := by
  sorry

/-- Whenever min_operations n returns a result r, r = k*k.
  Preconditions: n is an even integer with 1 <= n <= 10000. Let k = n/2, using integer division. -/
theorem spec_4 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (heven : ∃ k : ℤ, n.val = 2 * k)
    (r : I64) (hr : Aegis.MinOperations.min_operations n = ok r) :
    r.val = (n.val / 2) * (n.val / 2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (heven : ∃ k : ℤ, n.val = 2 * k)
    (r : I64) (hr : Aegis.MinOperations.min_operations n = ok r), r.val = (n.val / 2) * (n.val / 2)) := by
  sorry

/-- Whenever min_operations n returns a result r, r = k*(k+1).
  Preconditions: n is an odd integer with 1 <= n <= 10000. Let k = (n-1)/2, so n = 2*k + 1. -/
theorem spec_5 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hodd : ∃ k : ℤ, n.val = 2 * k + 1)
    (r : I64) (hr : Aegis.MinOperations.min_operations n = ok r) :
    r.val = ((n.val - 1) / 2) * ((n.val - 1) / 2 + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hodd : ∃ k : ℤ, n.val = 2 * k + 1)
    (r : I64) (hr : Aegis.MinOperations.min_operations n = ok r), r.val = ((n.val - 1) / 2) * ((n.val - 1) / 2 + 1)) := by
  sorry

/-- Whenever min_operations n returns a result r, r = sum_{i=0}^{n-1} max(0, (2*i + 1) - n).
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_6 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    r.val = sumExcess n.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), r.val = sumExcess n.val.toNat) := by
  sorry

/-- Whenever min_operations n returns a result r, r = sum_{i=0}^{n-1} max(0, n - (2*i + 1)).
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_7 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    r.val = sumDeficit n.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), r.val = sumDeficit n.val.toNat) := by
  sorry

/-- Whenever min_operations n returns a result r, 2*r = sum_{i=0}^{n-1} abs((2*i + 1) - n).
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_8 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    2 * r.val = sumAbsDev n.val.toNat := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), 2 * r.val = sumAbsDev n.val.toNat) := by
  sorry

/-- Let arr be the array of length n with arr[i] = 2*i + 1 for every i with 0 <= i < n. Whenever min_operations n returns a result r, for every integer k with 0 <= k < r, there is no sequence of exactly k operations that makes all entries of arr equal.
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_9 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    ∀ k : ℕ, (k : ℤ) < r.val → ¬ ReachableIn (initArr n.val.toNat) k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), ∀ k : ℕ, (k : ℤ) < r.val → ¬ ReachableIn (initArr n.val.toNat) k) := by
  sorry

/-- Let arr be the array of length n with arr[i] = 2*i + 1 for every i with 0 <= i < n. Whenever min_operations n returns a result r, there exists a sequence of exactly r operations that makes all entries of arr equal.
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_10 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    ReachableIn (initArr n.val.toNat) r.val.toNat := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), ReachableIn (initArr n.val.toNat) r.val.toNat) := by
  sorry

/-- If min_operations n returns a result r_n and min_operations m returns a result r_m, then r_n <= r_m.
  Preconditions: n and m are integers with 1 <= n <= m <= 10000. -/
theorem spec_11 (n m : I64) (hn : 1 ≤ n.val ∧ n.val ≤ m.val) (hm : m.val ≤ 10000)
    (r_n r_m : I64) (h_n : Aegis.MinOperations.min_operations n = ok r_n)
    (h_m : Aegis.MinOperations.min_operations m = ok r_m) :
    r_n.val ≤ r_m.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n m : I64) (hn : 1 ≤ n.val ∧ n.val ≤ m.val) (hm : m.val ≤ 10000)
    (r_n r_m : I64) (h_n : Aegis.MinOperations.min_operations n = ok r_n)
    (h_m : Aegis.MinOperations.min_operations m = ok r_m), r_n.val ≤ r_m.val) := by
  sorry

/-- If min_operations n returns a result r_n and min_operations (n-1) returns a result r_{n-1}, then r_n = r_{n-1} + floor(n/2), where floor(n/2) is integer division of n by 2.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_12 (n : I64) (hn : 2 ≤ n.val ∧ n.val ≤ 10000)
    (r_n r_prev : I64) (h_n : Aegis.MinOperations.min_operations n = ok r_n)
    (h_prev : Aegis.MinOperations.min_operations (pred n) = ok r_prev) :
    r_n.val = r_prev.val + n.val / 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (hn : 2 ≤ n.val ∧ n.val ≤ 10000)
    (r_n r_prev : I64) (h_n : Aegis.MinOperations.min_operations n = ok r_n)
    (h_prev : Aegis.MinOperations.min_operations (pred n) = ok r_prev), r_n.val = r_prev.val + n.val / 2) := by
  sorry

/-- Whenever min_operations n returns a result r, r = sum_{i=1}^{n} floor(i/2), where floor(i/2) is integer division of i by 2.
  Preconditions: n is an integer with 1 <= n <= 10000. -/
theorem spec_13 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r) :
    r.val = sumFloorHalf n.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (r : I64)
    (hr : Aegis.MinOperations.min_operations n = ok r), r.val = sumFloorHalf n.val.toNat) := by
  sorry

end AegisSpec.MinOperations
