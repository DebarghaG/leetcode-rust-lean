import Aegis.CountMaxOrSubsets.Code.Funs

/-!
# Specifications of `Aegis.CountMaxOrSubsets.count_max_or_subsets`

LeetCode problem `count-number-of-maximum-bitwise-or-subsets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountMaxOrSubsets

namespace AegisSpec.CountMaxOrSubsets

def vals (nums : Slice Std.I64) : List Nat := nums.val.map (fun x => x.val.toNat)

def orOn (l : List Nat) (I : Finset Nat) : Nat :=
  ((List.range l.length).map (fun i => if i ∈ I then l[i]! else 0)).foldl (· ||| ·) 0

def fullIdx (l : List Nat) : Finset Nat := Finset.range l.length

def orAll (l : List Nat) : Nat := l.foldl (· ||| ·) 0

def maxOr (l : List Nat) : Nat := ((fullIdx l).powerset.filter (fun I => I ≠ ∅)).sup (orOn l)

def countOrEq (l : List Nat) (M : Nat) : Nat :=
  ((fullIdx l).powerset.filter (fun I => I ≠ ∅ ∧ orOn l I = M)).card

def countEqOrAll (l : List Nat) : Nat := (l.filter (fun x => x = orAll l)).length

abbrev submask (a b : Nat) : Prop := a ||| b = b

def ind (P : Prop) [Decidable P] : Int := if P then 1 else 0

/-- Let n = len(nums). For a non-empty finite set S ⊆ {0,1,...,n-1}, let or(S) be the bitwise OR of the values nums[i] for i ∈ S, using the usual bitwise OR on the 64-bit representations (all nums[i] are between 1 and 100000, so this coincides with the usual bitwise OR on non-negative integers). Let M = max { or(S) | S ⊆ {0,1,...,n-1}, S ≠ ∅ }. The function returns a result r and r equals the number of non-empty sets S ⊆ {0,1,...,n-1} such that or(S) = M.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
    ∃ r, count_max_or_subsets nums = ok r ∧
      r.val = ((countOrEq (vals nums) (maxOr (vals nums)) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∃ r, count_max_or_subsets nums = ok r ∧
      r.val = ((countOrEq (vals nums) (maxOr (vals nums)) : Nat) : Int)) := by
  sorry

/-- The function returns a result r (i.e., it does not panic, overflow, or go out of bounds) for every input satisfying the preconditions.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
    ∃ r, count_max_or_subsets nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∃ r, count_max_or_subsets nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have r ≥ 1.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
    ∀ r, count_max_or_subsets nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∀ r, count_max_or_subsets nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r ≤ 2^{len(nums)} - 1.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
    ∀ r, count_max_or_subsets nums = ok r → r.val ≤ ((2 ^ nums.val.length - 1 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∀ r, count_max_or_subsets nums = ok r → r.val ≤ ((2 ^ nums.val.length - 1 : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r = 2^{len(nums)} - 1.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. Additionally, there exists an integer c such that for every i with 0 ≤ i < n, nums[i] = c. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (heq : ∃ c : Int, ∀ i, i < nums.val.length → (nums.val[i]!).val = c) :
    ∃ r, count_max_or_subsets nums = ok r ∧ r.val = ((2 ^ nums.val.length - 1 : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (heq : ∃ c : Int, ∀ i, i < nums.val.length → (nums.val[i]!).val = c), ∃ r, count_max_or_subsets nums = ok r ∧ r.val = ((2 ^ nums.val.length - 1 : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. Additionally, for every i, j with 0 ≤ i < j < n, the bitwise AND (nums[i] & nums[j]) equals 0. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hdisj : ∀ i j, i < j → j < nums.val.length → ((vals nums)[i]! &&& (vals nums)[j]!) = 0) :
    ∃ r, count_max_or_subsets nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hdisj : ∀ i j, i < j → j < nums.val.length → ((vals nums)[i]! &&& (vals nums)[j]!) = 0), ∃ r, count_max_or_subsets nums = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r = 2^{len(nums)-1}.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. Additionally, there exists an index k with 0 ≤ k < n such that nums[k] = M, where M = nums[0] | nums[1] | ... | nums[n-1], and the bitwise OR of the values nums[i] for all i with 0 ≤ i < n and i ≠ k is strictly less than M. (By convention, the OR of the empty set is 0; this condition is automatically satisfied when n = 1.) -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hk : ∃ k, k < nums.val.length ∧ (vals nums)[k]! = orAll (vals nums) ∧
      orOn (vals nums) ((fullIdx (vals nums)).erase k) < orAll (vals nums)) :
    ∃ r, count_max_or_subsets nums = ok r ∧ r.val = ((2 ^ (nums.val.length - 1) : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hk : ∃ k, k < nums.val.length ∧ (vals nums)[k]! = orAll (vals nums) ∧
      orOn (vals nums) ((fullIdx (vals nums)).erase k) < orAll (vals nums)), ∃ r, count_max_or_subsets nums = ok r ∧ r.val = ((2 ^ (nums.val.length - 1) : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r = 1 + [nums[1] is a bitwise submask of nums[0]] + [nums[0] is a bitwise submask of nums[1]], where [P] is 1 if P is true and 0 otherwise, and 'x is a bitwise submask of y' means (x | y) = y (equivalently, every bit set in x is also set in y).
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. Additionally, len(nums) = 2. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen2 : nums.val.length = 2) :
    ∃ r, count_max_or_subsets nums = ok r ∧
      r.val = 1 + ind (submask (vals nums)[1]! (vals nums)[0]!)
        + ind (submask (vals nums)[0]! (vals nums)[1]!) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen2 : nums.val.length = 2), ∃ r, count_max_or_subsets nums = ok r ∧
      r.val = 1 + ind (submask (vals nums)[1]! (vals nums)[0]!)
        + ind (submask (vals nums)[0]! (vals nums)[1]!)) := by
  sorry

/-- The function returns results r and r' on nums and nums' respectively, and r = r'.
  Preconditions: Let nums and nums' be two slices of 64-bit signed integers, both satisfying the general constraints (so both have length n with 1 ≤ n ≤ 16 and all elements between 1 and 100000). Suppose nums' is a permutation of nums, i.e., there exists a bijection σ : {0,...,n-1} → {0,...,n-1} such that nums'[i] = nums[σ(i)] for every 0 ≤ i < n. -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hperm : nums'.val.Perm nums.val) :
    ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hperm : nums'.val.Perm nums.val), ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧ r = r') := by
  sorry

/-- Let M = nums[0] | nums[1] | ... | nums[n-1] (the maximum possible OR). Let k be the number of indices i with 0 ≤ i < n such that nums[i] = M. Whenever the function returns a result r, we have r ≥ 2^n - 2^{n-k}.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 ≤ n ≤ 16; for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 100000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
    ∀ r, count_max_or_subsets nums = ok r →
      ((2 ^ nums.val.length - 2 ^ (nums.val.length - countEqOrAll (vals nums)) : Nat) : Int) ≤ r.val
    := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∀ r, count_max_or_subsets nums = ok r →
      ((2 ^ nums.val.length - 2 ^ (nums.val.length - countEqOrAll (vals nums)) : Nat) : Int) ≤ r.val) := by
  sorry

/-- The function returns results r and r' on nums and nums' respectively, and r' = 2 * r.
  Preconditions: Let nums be a slice satisfying the general constraints, with n = len(nums). Let M = nums[0] | ... | nums[n-1]. Let v be an integer with 1 ≤ v ≤ 100000 such that v is a bitwise submask of every nums[i] (i.e., (v | nums[i]) = nums[i] for all i) and v < M. Let nums' be the slice of length n+1 obtained by appending v to nums (nums'[i] = nums[i] for i < n and nums'[n] = v). Assume nums' also satisfies the general constraints (i.e., n+1 ≤ 16, and v ≤ 100000). -/
theorem spec_11 (nums nums' : Slice Std.I64) (v : Nat)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hv1 : 1 ≤ v) (hv100000 : v ≤ 100000)
    (happ : vals nums' = vals nums ++ [v])
    (hsub : ∀ i, i < nums.val.length → submask v (vals nums)[i]!)
    (hlt : v < orAll (vals nums)) :
    ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧
      r'.val = 2 * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (v : Nat)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hv1 : 1 ≤ v) (hv100000 : v ≤ 100000)
    (happ : vals nums' = vals nums ++ [v])
    (hsub : ∀ i, i < nums.val.length → submask v (vals nums)[i]!)
    (hlt : v < orAll (vals nums)), ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧
      r'.val = 2 * r.val) := by
  sorry

/-- The function returns results r and r' on nums and nums' respectively, and r' = r + 2^n.
  Preconditions: nums is a slice of 64-bit signed integers with n = len(nums). The constraints are: 1 <= n <= 16; for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = nums[0] | ... | nums[n-1]. Let nums' be the slice of length n+1 with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = M. Assume n+1 <= 16 and M <= 100000, so nums' also satisfies the general constraints. -/
theorem spec_12 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hnext : nums.val.length + 1 ≤ 16)
    (hM : orAll (vals nums) ≤ 100000)
    (happ : vals nums' = vals nums ++ [orAll (vals nums)]) :
    ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧
      r'.val = r.val + ((2 ^ nums.val.length : Nat) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen16 : nums.val.length ≤ 16)
    (hval : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
    (hlen1' : 1 ≤ nums'.val.length) (hlen16' : nums'.val.length ≤ 16)
    (hval' : ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000)
    (hnext : nums.val.length + 1 ≤ 16)
    (hM : orAll (vals nums) ≤ 100000)
    (happ : vals nums' = vals nums ++ [orAll (vals nums)]), ∃ r r', count_max_or_subsets nums = ok r ∧ count_max_or_subsets nums' = ok r' ∧
      r'.val = r.val + ((2 ^ nums.val.length : Nat) : Int)) := by
  sorry

end AegisSpec.CountMaxOrSubsets
