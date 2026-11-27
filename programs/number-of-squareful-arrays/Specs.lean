import Aegis.NumSquarefulPerms.Code.Funs

/-!
# Specifications of `Aegis.NumSquarefulPerms.num_squareful_perms`

LeetCode problem `number-of-squareful-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.NumSquarefulPerms

def IsSquareInt (s : ℤ) : Prop := ∃ k : ℤ, 0 ≤ k ∧ k * k = s

def entries (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def occ (v : ℤ) : List ℤ → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + occ v xs

def IsRearrangement (ys xs : List ℤ) : Prop :=
  ys.length = xs.length ∧ ∀ v : ℤ, occ v ys = occ v xs

def IsSquarefulSeq (ys : List ℤ) : Prop :=
  ∀ (i : Nat) (_ : i + 1 < ys.length), IsSquareInt (ys[i] + ys[i + 1])

def IsSquarefulRearrangement (ys xs : List ℤ) : Prop :=
  IsRearrangement ys xs ∧ IsSquarefulSeq ys

noncomputable def squarefulRearrangements (xs : List ℤ) : Finset (List ℤ) :=
  (xs.permutations.filter (fun ys => decide (IsSquarefulSeq ys))).toFinset

noncomputable def numSquarefulRearrangements (xs : List ℤ) : Nat :=
  (squarefulRearrangements xs).card

def IsPalindromeList (ys : List ℤ) : Prop :=
  ∀ (i : Nat) (_ : i < ys.length), ys[i] = ys[ys.length - 1 - i]

noncomputable def palindromicSquarefulRearrangements (xs : List ℤ) : Finset (List ℤ) :=
  (squarefulRearrangements xs).filter (fun ys => IsPalindromeList ys)

noncomputable def palindromicSquarefulCount (xs : List ℤ) : Nat :=
  (palindromicSquarefulRearrangements xs).card

def multinomialCount (xs : List ℤ) : Nat :=
  Nat.factorial xs.length / xs.toFinset.prod (fun v => Nat.factorial (occ v xs))

def EntriesInRange (nums : Slice Std.I64) : Prop :=
  ∀ x ∈ entries nums, 0 ≤ x ∧ x ≤ 10 ^ 9

def CompatGraphDisconnected (nums : Slice Std.I64) : Prop :=
  ∃ s : Set Nat,
    (∃ i, i < (entries nums).length ∧ i ∈ s) ∧
    (∃ i, i < (entries nums).length ∧ i ∉ s) ∧
    ∀ (i : Nat) (_ : i < (entries nums).length)
      (j : Nat) (_ : j < (entries nums).length),
      i ∈ s → j ∉ s → ¬ IsSquareInt ((entries nums)[i] + (entries nums)[j])

/-- Let n = len(nums). A sequence ys of length n is a rearrangement of nums when len(ys)=n and, for every integer v, the number of indices i with ys[i]=v equals the number of indices i with nums[i]=v; two rearrangements are considered the same when they agree at every index. Call ys squareful when for every i with 0 <= i < n-1 the sum ys[i]+ys[i+1] is a perfect square, where an integer s is a perfect square iff there exists an integer k >= 0 with k*k = s. The function returns a result r, and r is the number of distinct squareful rearrangements of nums.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. These are the problem constraints. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      r.val = (numSquarefulRearrangements (entries nums) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      r.val = (numSquarefulRearrangements (entries nums) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r satisfies 0 <= r <= n! / (product over all values v occurring in nums of c_v!), where n = len(nums) and c_v is the number of occurrences of v in nums.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums) :
    ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (multinomialCount (entries nums) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums), ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (multinomialCount (entries nums) : ℤ)) := by
  sorry

/-- The function returns r = 1.
  Preconditions: nums is a slice of 64-bit integers with len(nums)=1 and 0 <= nums[0] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : nums.val.length = 1) (hrange : EntriesInRange nums) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 1) (hrange : EntriesInRange nums), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r determined as follows: if nums[0]=nums[1], then r=1 when 2*nums[0] is a perfect square and r=0 otherwise; if nums[0] != nums[1], then r=2 when nums[0]+nums[1] is a perfect square and r=0 otherwise.
  Preconditions: nums is a slice of 64-bit integers with len(nums)=2 and, for i=0,1, 0 <= nums[i] <= 10^9. A perfect square means an integer s for which there exists an integer k >= 0 with k*k = s. -/
theorem spec_5 (nums : Slice Std.I64) (x y : ℤ)
    (hlen : nums.val.length = 2) (hcontents : entries nums = [x, y])
    (hx : 0 ≤ x ∧ x ≤ 10 ^ 9) (hy : 0 ≤ y ∧ y ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      (x = y → IsSquareInt (2 * x) → r.val = 1) ∧
      (x = y → ¬ IsSquareInt (2 * x) → r.val = 0) ∧
      (x ≠ y → IsSquareInt (x + y) → r.val = 2) ∧
      (x ≠ y → ¬ IsSquareInt (x + y) → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (x y : ℤ)
    (hlen : nums.val.length = 2) (hcontents : entries nums = [x, y])
    (hx : 0 ≤ x ∧ x ≤ 10 ^ 9) (hy : 0 ≤ y ∧ y ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      (x = y → IsSquareInt (2 * x) → r.val = 1) ∧
      (x = y → ¬ IsSquareInt (2 * x) → r.val = 0) ∧
      (x ≠ y → IsSquareInt (x + y) → r.val = 2) ∧
      (x ≠ y → ¬ IsSquareInt (x + y) → r.val = 0)) := by
  sorry

/-- The function returns r = 1 when 2*x is a perfect square, and r = 0 otherwise.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 12, and there is an integer x with 0 <= x <= 10^9 such that nums[i]=x for every i with 0 <= i < len(nums). A perfect square means an integer s for which there exists an integer k >= 0 with k*k = s. -/
theorem spec_6 (nums : Slice Std.I64) (x : ℤ)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hx : 0 ≤ x ∧ x ≤ 10 ^ 9) (hall : ∀ y ∈ entries nums, y = x) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      (IsSquareInt (2 * x) → r.val = 1) ∧ (¬ IsSquareInt (2 * x) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (x : ℤ)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hx : 0 ≤ x ∧ x ≤ 10 ^ 9) (hall : ∀ y ∈ entries nums, y = x), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      (IsSquareInt (2 * x) → r.val = 1) ∧ (¬ IsSquareInt (2 * x) → r.val = 0)) := by
  sorry

/-- The function returns r = 0.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 12, 0 <= nums[i] <= 10^9 for all i, and there exists an index i with 0 <= i < len(nums) such that for every j with 0 <= j < len(nums) and j != i, nums[i]+nums[j] is not a perfect square, where perfect square means an integer s with some integer k >= 0 satisfying k*k = s. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hiso : ∃ i : Nat, ∃ _hi : i < (entries nums).length,
      ∀ (j : Nat) (_ : j < (entries nums).length), j ≠ i →
        ¬ IsSquareInt ((entries nums)[i] + (entries nums)[j])) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hiso : ∃ i : Nat, ∃ _hi : i < (entries nums).length,
      ∀ (j : Nat) (_ : j < (entries nums).length), j ≠ i →
        ¬ IsSquareInt ((entries nums)[i] + (entries nums)[j])), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists a sequence ys of length len(nums) that is a rearrangement of nums (same multiset of entries) and satisfies: for every i with 0 <= i < len(nums)-1, ys[i]+ys[i+1] is a perfect square.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. A perfect square means an integer s for which there exists an integer k >= 0 with k*k = s. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums) :
    ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      (0 < r.val ↔ ∃ ys : List ℤ, IsSquarefulRearrangement ys (entries nums)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums), ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      (0 < r.val ↔ ∃ ys : List ℤ, IsSquarefulRearrangement ys (entries nums))) := by
  sorry

/-- Whenever the function returns r on input nums and returns r' on input nums', we have r = r'.
  Preconditions: nums and nums' are slices of 64-bit integers, both satisfy 1 <= length <= 12 and all entries are between 0 and 10^9, and nums' is a rearrangement of nums, meaning len(nums')=len(nums) and for every integer v the number of occurrences of v in nums' equals the number of occurrences of v in nums. -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hlen_lb' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 12)
    (hrange' : EntriesInRange nums')
    (hperm : IsRearrangement (entries nums') (entries nums)) :
    ∀ r r' : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      Aegis.NumSquarefulPerms.num_squareful_perms nums' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hlen_lb' : 1 ≤ nums'.val.length) (hlen_ub' : nums'.val.length ≤ 12)
    (hrange' : EntriesInRange nums')
    (hperm : IsRearrangement (entries nums') (entries nums)), ∀ r r' : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      Aegis.NumSquarefulPerms.num_squareful_perms nums' = ok r' → r = r') := by
  sorry

/-- The function returns a result r, and r = n! / (product over all values v occurring in nums of c_v!), where n = len(nums) and c_v is the number of occurrences of v in nums.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and 0 <= nums[i] <= 10^9 for all i. For every pair of indices i,j with 0 <= i < j < len(nums), nums[i]+nums[j] is a perfect square, where perfect square means an integer s with some integer k >= 0 satisfying k*k = s. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hcomplete : ∀ (i : Nat) (_ : i < (entries nums).length)
      (j : Nat) (_ : j < (entries nums).length), i < j →
        IsSquareInt ((entries nums)[i] + (entries nums)[j])) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      r.val = (multinomialCount (entries nums) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hcomplete : ∀ (i : Nat) (_ : i < (entries nums).length)
      (j : Nat) (_ : j < (entries nums).length), i < j →
        IsSquareInt ((entries nums)[i] + (entries nums)[j])), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧
      r.val = (multinomialCount (entries nums) : ℤ)) := by
  sorry

/-- Whenever the function returns r, r mod 2 equals P mod 2, where P is the number of distinct squareful rearrangements ys of nums such that ys[i] = ys[len(nums)-1-i] for every i with 0 <= i < len(nums); squareful means that for every i with 0 <= i < len(nums)-1, ys[i]+ys[i+1] is a perfect square.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 12 and 0 <= nums[i] <= 10^9 for all i. A perfect square means an integer s with some integer k >= 0 satisfying k*k = s. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums) :
    ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      r.val % 2 = ((palindromicSquarefulCount (entries nums) : Nat) : ℤ) % 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums), ∀ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r →
      r.val % 2 = ((palindromicSquarefulCount (entries nums) : Nat) : ℤ) % 2) := by
  sorry

/-- The function returns a result r, and r = 0.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 12 and 0 <= nums[i] <= 10^9 for every i. Let G be the undirected graph on indices {0,...,len(nums)-1} with an edge between distinct i and j exactly when nums[i]+nums[j] is a perfect square, where perfect square means s=t*t for some integer t>=0. Assume G is disconnected. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hconn : CompatGraphDisconnected nums) :
    ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 12)
    (hrange : EntriesInRange nums)
    (hconn : CompatGraphDisconnected nums), ∃ r : Std.I64, Aegis.NumSquarefulPerms.num_squareful_perms nums = ok r ∧ r.val = 0) := by
  sorry

end AegisSpec.NumSquarefulPerms
