import Aegis.Rob.Code.Funs

/-!
# Specifications of `Aegis.Rob.rob`

LeetCode problem `house-robber`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Rob

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def size (nums : Slice I64) : ℕ := nums.val.length

def elemAt (nums : Slice I64) (i : ℕ) : ℤ := (vals nums).getD i 0

def total (nums : Slice I64) : ℤ := (vals nums).sum

def Indep (S : Finset ℕ) : Prop := ∀ i ∈ S, ∀ j ∈ S, i ≠ j → i + 1 ≠ j ∧ j + 1 ≠ i

def Valid (nums : Slice I64) (S : Finset ℕ) : Prop :=
  Indep S ∧ S ⊆ Finset.range (size nums)

def sumS (nums : Slice I64) (S : Finset ℕ) : ℤ := ∑ i ∈ S, elemAt nums i

def MaximalIndep (nums : Slice I64) (S : Finset ℕ) : Prop :=
  ∀ i, i < size nums → i ∉ S → ∃ j ∈ S, i + 1 = j ∨ j + 1 = i

def IsMaxSum (nums : Slice I64) (r : ℤ) : Prop :=
  (∃ S : Finset ℕ, Valid nums S ∧ sumS nums S = r) ∧
    ∀ S : Finset ℕ, Valid nums S → sumS nums S ≤ r

def IsMaxSumAvoiding (nums : Slice I64) (k : ℕ) (r : ℤ) : Prop :=
  (∃ S : Finset ℕ, Valid nums S ∧ k ∉ S ∧ sumS nums S = r) ∧
    ∀ S : Finset ℕ, Valid nums S → k ∉ S → sumS nums S ≤ r

def evenSum (nums : Slice I64) : ℤ :=
  ∑ i ∈ (Finset.range (size nums)).filter (fun i => i % 2 = 0), elemAt nums i

def oddSum (nums : Slice I64) : ℤ :=
  ∑ i ∈ (Finset.range (size nums)).filter (fun i => i % 2 = 1), elemAt nums i

/-- Whenever the function returns a result r, r is the maximum of the set of all sums of the form sum_{i in S} nums[i], where S is any subset of {0, 1, ..., len(nums)-1} such that no two distinct indices in S are adjacent, i.e., for all i, j in S, |i - j| != 1. Equivalently, (a) there exists such an independent set S with sum_{i in S} nums[i] = r, and (b) for every independent set S, sum_{i in S} nums[i] <= r.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_1 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → IsMaxSum nums r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r → IsMaxSum nums r.val) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or access an out-of-bounds index).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_2 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∃ r : I64, Aegis.Rob.rob nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∃ r : I64, Aegis.Rob.rob nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_3 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val ≤ total nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val ≤ total nums) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r >= nums[i].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_4 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → ∀ i, i < size nums → elemAt nums i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r → ∀ i, i < size nums → elemAt nums i ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400, and len(nums) = 1. -/
theorem spec_5 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h1 : size nums = 1) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = elemAt nums 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h1 : size nums = 1), ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = elemAt nums 0) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0], nums[1]).
  Preconditions: 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400, and len(nums) = 2. -/
theorem spec_6 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h2 : size nums = 2) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = max (elemAt nums 0) (elemAt nums 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h2 : size nums = 2), ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = max (elemAt nums 0) (elemAt nums 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = 0.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_7 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r →
      (r.val = 0 ↔ ∀ i, i < size nums → elemAt nums i = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r →
      (r.val = 0 ↔ ∀ i, i < size nums → elemAt nums i = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = c * ((len(nums) + 1) / 2), where / denotes integer division (i.e., c * ceil(len(nums)/2)).
  Preconditions: 1 <= len(nums) <= 100, 0 <= nums[i] <= 400 for all i, and there exists c with 0 <= c <= 400 such that for every i, nums[i] = c. -/
theorem spec_8 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (c : ℤ) (hc0 : 0 ≤ c) (hc400 : c ≤ 400)
    (hconst : ∀ i, i < size nums → elemAt nums i = c) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = c * (((size nums + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (c : ℤ) (hc0 : 0 ≤ c) (hc400 : c ≤ 400)
    (hconst : ∀ i, i < size nums → elemAt nums i = c), ∀ r : I64, Aegis.Rob.rob nums = ok r → r.val = c * (((size nums + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i, j with 0 <= i < j < len(nums) and j >= i + 2, r >= nums[i] + nums[j].
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_9 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∀ i j, i < j → j < size nums → i + 2 ≤ j →
        elemAt nums i + elemAt nums j ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∀ i j, i < j → j < size nums → i + 2 ≤ j →
        elemAt nums i + elemAt nums j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let E = sum of nums[i] over all even i with 0 <= i < len(nums), and O = sum of nums[i] over all odd i with 0 <= i < len(nums). Then r >= E and r >= O.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_10 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r → evenSum nums ≤ r.val ∧ oddSum nums ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r → evenSum nums ≤ r.val ∧ oddSum nums ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset S of {0, 1, ..., len(nums)-1} such that (i) S is independent (no two distinct elements of S are adjacent), (ii) sum_{i in S} nums[i] = r, and (iii) S is maximal independent, meaning that for every index i not in S there exists j in S with |i - j| = 1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_11 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∃ S : Finset ℕ, Valid nums S ∧ sumS nums S = r.val ∧ MaximalIndep nums S := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∃ S : Finset ℕ, Valid nums S ∧ sumS nums S = r.val ∧ MaximalIndep nums S) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums) and nums[i] = 0, r is also the maximum of the set of sums sum_{j in S} nums[j] over all independent sets S that do not contain i (i.e., S is a subset of {0, ..., len(nums)-1} minus {i}).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400. -/
theorem spec_12 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∀ i, i < size nums → elemAt nums i = 0 → IsMaxSumAvoiding nums i r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400), ∀ r : I64, Aegis.Rob.rob nums = ok r →
      ∀ i, i < size nums → elemAt nums i = 0 → IsMaxSumAvoiding nums i r.val) := by
  sorry

/-- Whenever the function returns a result r, r = max(nums[0] + nums[2], nums[1]).
  Preconditions: 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 400, and len(nums) = 3. -/
theorem spec_13 (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h3 : size nums = 3) :
    ∀ r : I64, Aegis.Rob.rob nums = ok r →
      r.val = max (elemAt nums 0 + elemAt nums 2) (elemAt nums 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (hlen1 : 1 ≤ size nums) (hlen : size nums ≤ 100)
    (hval : ∀ i, i < size nums → 0 ≤ elemAt nums i ∧ elemAt nums i ≤ 400)
    (h3 : size nums = 3), ∀ r : I64, Aegis.Rob.rob nums = ok r →
      r.val = max (elemAt nums 0 + elemAt nums 2) (elemAt nums 1)) := by
  sorry

end AegisSpec.Rob
