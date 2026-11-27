import Aegis.Search.Code.Funs

/-!
# Specifications of `Aegis.Search.search`

LeetCode problem `binary-search`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Search

def entry (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) : ℤ :=
  (nums.val.get ⟨i, h⟩).val

def SortedStrict (nums : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < nums.val.length),
    entry nums i (Nat.lt_trans (Nat.lt_succ_self i) h) < entry nums (i + 1) h

def Occurs (nums : Slice Std.I64) (target : Std.I64) : Prop :=
  ∃ (i : ℕ) (h : i < nums.val.length), entry nums i h = target.val

def Pre (nums : Slice Std.I64) (target : Std.I64) : Prop :=
  1 ≤ nums.val.length ∧
  nums.val.length ≤ 10000 ∧
  SortedStrict nums ∧
  (∀ (i : ℕ) (h : i < nums.val.length),
      -10000 ≤ entry nums i h ∧ entry nums i h ≤ 10000) ∧
  -10000 ≤ target.val ∧
  target.val ≤ 10000

/-- The function returns a result r and the following holds. If there exists an index i with 0 <= i < len(nums) and nums[i] = target, then 0 <= r < len(nums) and nums[r] = target. If no such index exists, then r = -1.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_1 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∃ r, Aegis.Search.search nums target = ok r ∧
      (Occurs nums target →
        0 ≤ r.val ∧ r.val < (nums.val.length : ℤ) ∧
          (∀ (h : r.val.toNat < nums.val.length),
            entry nums r.val.toNat h = target.val)) ∧
      (¬ Occurs nums target → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∃ r, Aegis.Search.search nums target = ok r ∧
      (Occurs nums target →
        0 ≤ r.val ∧ r.val < (nums.val.length : ℤ) ∧
          (∀ (h : r.val.toNat < nums.val.length),
            entry nums r.val.toNat h = target.val)) ∧
      (¬ Occurs nums target → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_2 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∃ r, Aegis.Search.search nums target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∃ r, Aegis.Search.search nums target = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(nums).
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_3 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r and r != -1, then 0 <= r < len(nums) and nums[r] = target.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_4 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r → r.val ≠ -1 →
      0 ≤ r.val ∧ r.val < (nums.val.length : ℤ) ∧
        (∀ (h : r.val.toNat < nums.val.length),
          entry nums r.val.toNat h = target.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r → r.val ≠ -1 →
      0 ≤ r.val ∧ r.val < (nums.val.length : ℤ) ∧
        (∀ (h : r.val.toNat < nums.val.length),
          entry nums r.val.toNat h = target.val)) := by
  sorry

/-- Whenever the function returns a result r and target does not occur in nums, i.e. for every i with 0 <= i < len(nums), nums[i] != target, then r = -1.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_5 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r →
      (∀ (i : ℕ) (h : i < nums.val.length), entry nums i h ≠ target.val) →
      r.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r →
      (∀ (i : ℕ) (h : i < nums.val.length), entry nums i h ≠ target.val) →
      r.val = -1) := by
  sorry

/-- Whenever the function returns a result r and r = -1, then target does not occur in nums, i.e. for every i with 0 <= i < len(nums), nums[i] != target.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_6 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r → r.val = -1 →
      ∀ (i : ℕ) (h : i < nums.val.length), entry nums i h ≠ target.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r → r.val = -1 →
      ∀ (i : ℕ) (h : i < nums.val.length), entry nums i h ≠ target.val) := by
  sorry

/-- Whenever the function returns a result r, target occurs in nums (there exists i with 0 <= i < len(nums) and nums[i] = target) if and only if r != -1.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_7 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r → (Occurs nums target ↔ r.val ≠ -1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r → (Occurs nums target ↔ r.val ≠ -1)) := by
  sorry

/-- Whenever the function returns a result r and target occurs in nums, then for every i with 0 <= i < len(nums), if nums[i] = target then r = i.
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_8 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r → Occurs nums target →
      ∀ (i : ℕ) (h : i < nums.val.length), entry nums i h = target.val → r.val = (i : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r → Occurs nums target →
      ∀ (i : ℕ) (h : i < nums.val.length), entry nums i h = target.val → r.val = (i : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with 0 <= r < len(nums), then for every i with 0 <= i < r, nums[i] < target, and for every i with r < i < len(nums), target < nums[i].
  Preconditions: 1 <= len(nums) <= 10000; nums is sorted in strictly ascending order, i.e. for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so all entries are distinct); and every entry nums[i] and target satisfy -10000 <= nums[i] <= 10000 and -10000 <= target <= 10000. -/
theorem spec_9 (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target) :
    ∀ r, Aegis.Search.search nums target = ok r →
      0 ≤ r.val → r.val < (nums.val.length : ℤ) →
      (∀ (i : ℕ) (hir : i < r.val.toNat) (h : i < nums.val.length),
        entry nums i h < target.val) ∧
      (∀ (i : ℕ) (hri : r.val.toNat < i) (h : i < nums.val.length),
        target.val < entry nums i h) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (hpre : Pre nums target), ∀ r, Aegis.Search.search nums target = ok r →
      0 ≤ r.val → r.val < (nums.val.length : ℤ) →
      (∀ (i : ℕ) (hir : i < r.val.toNat) (h : i < nums.val.length),
        entry nums i h < target.val) ∧
      (∀ (i : ℕ) (hri : r.val.toNat < i) (h : i < nums.val.length),
        target.val < entry nums i h)) := by
  sorry

end AegisSpec.Search
