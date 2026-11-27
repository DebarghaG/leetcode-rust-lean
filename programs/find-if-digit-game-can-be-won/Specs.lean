import Aegis.CanAliceWin.Code.Funs

/-!
# Specifications of `Aegis.CanAliceWin.can_alice_win`

LeetCode problem `find-if-digit-game-can-be-won`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanAliceWin

def Constraints (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100 ∧ ∀ x, x ∈ nums.val → 1 ≤ x.val ∧ x.val ≤ 99

def singlePart (x : Std.I64) : ℤ := if x.val < 10 then x.val else 0

def doublePart (x : Std.I64) : ℤ := if x.val < 10 then 0 else x.val

def singleSum (nums : Slice Std.I64) : ℤ := (nums.val.map singlePart).sum

def doubleSum (nums : Slice Std.I64) : ℤ := (nums.val.map doublePart).sum

def totalSum (nums : Slice Std.I64) : ℤ := (nums.val.map fun x => x.val).sum

def IsPerm (nums nums2 : Slice Std.I64) : Prop := nums2.val.Perm nums.val

theorem Constraints.of_perm {nums nums2 : Slice Std.I64} (h : Constraints nums)
    (hp : IsPerm nums nums2) : Constraints nums2 := by
  obtain ⟨hlen1, hlen2, hmem⟩ := h
  have hlen : nums2.val.length = nums.val.length := hp.length_eq
  refine ⟨by omega, by omega, ?_⟩
  intro x hx
  exact hmem x (hp.mem_iff.mp hx)

/-- The function returns a result r, and r = true if and only if S1 != S2. Equivalently, Alice can win exactly when either S1 > S2 (take all single-digit numbers) or S2 > S1 (take all double-digit numbers).
  Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 99. Define S1 = sum of nums[i] over indices i with nums[i] <= 9, and S2 = sum of nums[i] over indices i with nums[i] >= 10; under these constraints S1 is the single-digit sum and S2 is the double-digit sum. -/
theorem spec_1 (nums : Slice Std.I64) (h : Constraints nums) :
    ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      (r = true ↔ singleSum nums ≠ doubleSum nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums), ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      (r = true ↔ singleSum nums ≠ doubleSum nums)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access out of bounds.
  Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 99. -/
theorem spec_2 (nums : Slice Std.I64) (h : Constraints nums) :
    ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums), ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r) := by
  sorry

/-- The function returns a result r and r = false.
  Preconditions: nums satisfies the problem constraints, and S1 = S2, where S1 is the sum of single-digit entries and S2 is the sum of entries >= 10. -/
theorem spec_3 (nums : Slice Std.I64) (h : Constraints nums)
    (hs : singleSum nums = doubleSum nums) :
    ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums)
    (hs : singleSum nums = doubleSum nums), ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧ r = false) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: nums satisfies the problem constraints, and the total sum T = sum_{i=0}^{len(nums)-1} nums[i] is odd. -/
theorem spec_4 (nums : Slice Std.I64) (h : Constraints nums)
    (hT : Odd (totalSum nums)) :
    ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums)
    (hT : Odd (totalSum nums)), ∃ r, Aegis.CanAliceWin.can_alice_win nums = ok r ∧ r = true) := by
  sorry

/-- Whenever the function returns a result r with r = false, we have S1 = S2.
  Preconditions: nums satisfies the problem constraints. Let S1 be the sum of single-digit entries and spec_2 be the sum of entries >= 10. -/
theorem spec_5 (nums : Slice Std.I64) (h : Constraints nums) (r : Bool)
    (hr : Aegis.CanAliceWin.can_alice_win nums = ok r) (hf : r = false) :
    singleSum nums = doubleSum nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums) (r : Bool)
    (hr : Aegis.CanAliceWin.can_alice_win nums = ok r) (hf : r = false), singleSum nums = doubleSum nums) := by
  sorry

/-- Whenever the function returns a result r with r = true, at least one of S1 > S2 or S2 > S1 holds.
  Preconditions: nums satisfies the problem constraints. Let S1 be the sum of single-digit entries and spec_2 be the sum of entries >= 10. -/
theorem spec_6 (nums : Slice Std.I64) (h : Constraints nums) (r : Bool)
    (hr : Aegis.CanAliceWin.can_alice_win nums = ok r) (ht : r = true) :
    singleSum nums > doubleSum nums ∨ doubleSum nums > singleSum nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Constraints nums) (r : Bool)
    (hr : Aegis.CanAliceWin.can_alice_win nums = ok r) (ht : r = true), singleSum nums > doubleSum nums ∨ doubleSum nums > singleSum nums) := by
  sorry

/-- If S1(nums) = S1(nums2) and S2(nums) = S2(nums2), then the function returns results r and r2 for nums and nums2 respectively, with r = r2.
  Preconditions: nums and nums2 both satisfy the problem constraints. Define S1(x) as the sum of single-digit entries of x and S2(x) as the sum of entries >= 10 of x. -/
theorem spec_7 (nums nums2 : Slice Std.I64) (h1 : Constraints nums) (h2 : Constraints nums2)
    (hS1 : singleSum nums = singleSum nums2) (hS2 : doubleSum nums = doubleSum nums2) :
    ∃ r r2, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      Aegis.CanAliceWin.can_alice_win nums2 = ok r2 ∧ r = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (h1 : Constraints nums) (h2 : Constraints nums2)
    (hS1 : singleSum nums = singleSum nums2) (hS2 : doubleSum nums = doubleSum nums2), ∃ r r2, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      Aegis.CanAliceWin.can_alice_win nums2 = ok r2 ∧ r = r2) := by
  sorry

/-- The function returns results r and r2 for nums and nums2 respectively, with r = r2.
  Preconditions: nums satisfies the problem constraints, and nums2 is a permutation of nums (same length and same multiset of entries); hence nums2 also satisfies the constraints. -/
theorem spec_8 (nums nums2 : Slice Std.I64) (h : Constraints nums)
    (hp : IsPerm nums nums2) :
    ∃ r r2, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      Aegis.CanAliceWin.can_alice_win nums2 = ok r2 ∧ r = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (h : Constraints nums)
    (hp : IsPerm nums nums2), ∃ r r2, Aegis.CanAliceWin.can_alice_win nums = ok r ∧
      Aegis.CanAliceWin.can_alice_win nums2 = ok r2 ∧ r = r2) := by
  sorry

end AegisSpec.CanAliceWin
