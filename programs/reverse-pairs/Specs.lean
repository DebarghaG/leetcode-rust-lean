import Aegis.ReversePairs.Code.Funs

/-!
# Specifications of `Aegis.ReversePairs.reverse_pairs`

LeetCode problem `reverse-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ReversePairs

namespace AegisSpec.ReversePairs

def vals (nums : Slice Std.I64) : List ℤ :=
  nums.val.map (fun x => x.val)

def get (nums : Slice Std.I64) (i : Nat) : ℤ :=
  (vals nums).getD i 0

def elemsInI32Range (nums : Slice Std.I64) : Prop :=
  ∀ i : Nat, i < (Slice.len nums).val → -2147483648 ≤ get nums i ∧ get nums i ≤ 2147483647

def pairCount (nums : Slice Std.I64) : Nat :=
  (Finset.filter (fun p : Nat × Nat => p.1 < p.2 ∧ get nums p.1 > 2 * get nums p.2)
      ((Finset.range (Slice.len nums).val).product (Finset.range (Slice.len nums).val))).card

def countAfter (nums : Slice Std.I64) (i : Nat) : Nat :=
  (Finset.filter (fun j : Nat => i < j ∧ get nums i > 2 * get nums j)
      (Finset.range (Slice.len nums).val)).card

def countBefore (nums : Slice Std.I64) (j : Nat) : Nat :=
  (Finset.filter (fun i : Nat => get nums i > 2 * get nums j) (Finset.range j)).card

/-- Whenever reverse_pairs returns a result r, r is exactly the number of index pairs (i, j) such that 0 <= i < j < n and nums[i] > 2 * nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val = (pairCount nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val = (pairCount nums : ℤ)) := by
  sorry

/-- For every nums satisfying the preconditions, reverse_pairs returns a result; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_2 (nums : Slice Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums) :
    ∃ r : Std.I64, reverse_pairs nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums), ∃ r : Std.I64, reverse_pairs nums = ok r) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r <= n * (n - 1) / 2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val ≤ (((Slice.len nums).val * ((Slice.len nums).val - 1)) / 2 : Nat) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val ≤ (((Slice.len nums).val * ((Slice.len nums).val - 1)) / 2 : Nat)) := by
  sorry

/-- Whenever reverse_pairs returns a result r, 0 <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r = 0.
  Preconditions: Let n = len(nums). Assume n = 1 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 1)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 1)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val = 0) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r = 1 if nums[0] > 2 * nums[1], and r = 0 if nums[0] <= 2 * nums[1].
  Preconditions: Let n = len(nums). Assume n = 2 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 2)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    (get nums 0 > 2 * get nums 1 → r.val = (1 : ℤ)) ∧
      (get nums 0 ≤ 2 * get nums 1 → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 2)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), (get nums 0 > 2 * get nums 1 → r.val = (1 : ℤ)) ∧
      (get nums 0 ≤ 2 * get nums 1 → r.val = 0)) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r = sum over j from 0 to n-1 of (if nums[j] < 0 then j else 0).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000, for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647, for every i,j with 0 <= i < j < n, nums[i] >= nums[j], and for every i with 0 <= i < n, nums[i] <= 0. -/
theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (hsorted : ∀ i j : Nat, i < j → j < (Slice.len nums).val → get nums i ≥ get nums j)
    (hnonpos : ∀ i : Nat, i < (Slice.len nums).val → get nums i ≤ 0)
    (h : reverse_pairs nums = ok r) :
    r.val = Finset.sum (Finset.range (Slice.len nums).val)
      (fun j : Nat => if get nums j < 0 then (j : ℤ) else 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (hsorted : ∀ i j : Nat, i < j → j < (Slice.len nums).val → get nums i ≥ get nums j)
    (hnonpos : ∀ i : Nat, i < (Slice.len nums).val → get nums i ≤ 0)
    (h : reverse_pairs nums = ok r), r.val = Finset.sum (Finset.range (Slice.len nums).val)
      (fun j : Nat => if get nums j < 0 then (j : ℤ) else 0)) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r = sum over i from 0 to n-1 of (the number of indices j such that i < j < n and nums[i] > 2 * nums[j]).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val = ((Finset.sum (Finset.range (Slice.len nums).val)
      (fun i : Nat => countAfter nums i) : Nat) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val = ((Finset.sum (Finset.range (Slice.len nums).val)
      (fun i : Nat => countAfter nums i) : Nat) : ℤ)) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r = sum over j from 0 to n-1 of (the number of indices i such that 0 <= i < j and nums[i] > 2 * nums[j]).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_9 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val = ((Finset.sum (Finset.range (Slice.len nums).val)
      (fun j : Nat => countBefore nums j) : Nat) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val = ((Finset.sum (Finset.range (Slice.len nums).val)
      (fun j : Nat => countBefore nums j) : Nat) : ℤ)) := by
  sorry

/-- Whenever reverse_pairs returns a result r, r > 0 if and only if there exist indices i and j such that 0 <= i < j < n and nums[i] > 2 * nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000 and for every i with 0 <= i < n, -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_10 (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r) :
    r.val > 0 ↔ ∃ i j : Nat, i < j ∧ j < (Slice.len nums).val ∧ get nums i > 2 * get nums j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (h1 : 1 ≤ (Slice.len nums).val) (h2 : (Slice.len nums).val ≤ 50000)
    (hb : elemsInI32Range nums)
    (h : reverse_pairs nums = ok r), r.val > 0 ↔ ∃ i j : Nat, i < j ∧ j < (Slice.len nums).val ∧ get nums i > 2 * get nums j) := by
  sorry

end AegisSpec.ReversePairs
