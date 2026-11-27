import Aegis.MinSubArrayLen.Code.Funs

/-!
# Specifications of `Aegis.MinSubArrayLen.min_sub_array_len`

LeetCode problem `minimum-size-subarray-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinSubArrayLen

def contents (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def len (nums : Slice I64) : Nat := nums.val.length

def gap (l r : Nat) : Int := (r : Int) - (l : Int)

def subSum (nums : Slice I64) (l r : Nat) : Int :=
  ((contents nums).drop l).take (r - l) |>.sum

def occurs (nums : Slice I64) (x : Int) : Prop := x ∈ contents nums

def hasLargeEntry (nums : Slice I64) (t : Int) : Prop :=
  ∃ i : Nat, ∃ h : i < nums.val.length, t ≤ (nums.val[i]'h).val

/-- Let n = len(nums), and for 0 <= l <= r <= n let S(l,r) = sum_{k=l}^{r-1} nums[k]. The function returns a result ans such that: (1) if there is no pair (l,r) with 0 <= l < r <= n and S(l,r) >= target, then ans = 0; (2) if there is such a pair, then ans >= 1, there exists a pair (l0,r0) with 0 <= l0 < r0 <= n, r0-l0 = ans, and S(l0,r0) >= target, and for every pair (l,r) with 0 <= l < r <= n and S(l,r) >= target, r-l >= ans.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_1 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000) :
    ∃ ans : I64,
      Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans ∧
      (¬ (∃ l r : Nat, l < r ∧ r ≤ len nums ∧ target.val ≤ subSum nums l r) →
        ans.val = 0) ∧
      ((∃ l r : Nat, l < r ∧ r ≤ len nums ∧ target.val ≤ subSum nums l r) →
        1 ≤ ans.val ∧
        (∃ l0 r0 : Nat, l0 < r0 ∧ r0 ≤ len nums ∧ gap l0 r0 = ans.val ∧
          target.val ≤ subSum nums l0 r0) ∧
        (∀ l r : Nat, l < r → r ≤ len nums → target.val ≤ subSum nums l r →
          ans.val ≤ gap l r)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000), ∃ ans : I64,
      Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans ∧
      (¬ (∃ l r : Nat, l < r ∧ r ≤ len nums ∧ target.val ≤ subSum nums l r) →
        ans.val = 0) ∧
      ((∃ l r : Nat, l < r ∧ r ≤ len nums ∧ target.val ≤ subSum nums l r) →
        1 ≤ ans.val ∧
        (∃ l0 r0 : Nat, l0 < r0 ∧ r0 ≤ len nums ∧ gap l0 r0 = ans.val ∧
          target.val ≤ subSum nums l0 r0) ∧
        (∀ l r : Nat, l < r → r ≤ len nums → target.val ≤ subSum nums l r →
          ans.val ≤ gap l r))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a successful result ans; in particular, it does not fail due to overflow, out-of-bounds access, or a panic.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_2 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000) :
    ∃ ans : I64, Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000), ∃ ans : I64, Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, 0 <= ans <= len(nums).
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_3 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans) :
    0 ≤ ans.val ∧ ans.val ≤ (len nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans), 0 ≤ ans.val ∧ ans.val ≤ (len nums : Int)) := by
  sorry

/-- Whenever the function returns a result ans, ans = 0 if and only if sum_{k=0}^{len(nums)-1} nums[k] < target.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_4 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans) :
    ans.val = 0 ↔ subSum nums 0 (len nums) < target.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans), ans.val = 0 ↔ subSum nums 0 (len nums) < target.val) := by
  sorry

/-- Whenever the function returns a result ans and ans > 0, there exists a pair (l,r) with 0 <= l < r <= len(nums), r-l = ans, and sum_{k=l}^{r-1} nums[k] >= target.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_5 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hpos : 0 < ans.val) :
    ∃ l r : Nat, l < r ∧ r ≤ len nums ∧ gap l r = ans.val ∧
      target.val ≤ subSum nums l r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hpos : 0 < ans.val), ∃ l r : Nat, l < r ∧ r ≤ len nums ∧ gap l r = ans.val ∧
      target.val ≤ subSum nums l r) := by
  sorry

/-- Whenever the function returns a result ans and ans > 0, for every pair (l,r) with 0 <= l < r <= len(nums) and sum_{k=l}^{r-1} nums[k] >= target, we have r-l >= ans.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_6 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hpos : 0 < ans.val) :
    ∀ l r : Nat, l < r → r ≤ len nums → target.val ≤ subSum nums l r →
      ans.val ≤ gap l r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hpos : 0 < ans.val), ∀ l r : Nat, l < r → r ≤ len nums → target.val ≤ subSum nums l r →
      ans.val ≤ gap l r) := by
  sorry

/-- Whenever the function returns a result ans and ans = 0, for every pair (l,r) with 0 <= l < r <= len(nums), sum_{k=l}^{r-1} nums[k] < target.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_7 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hzero : ans.val = 0) :
    ∀ l r : Nat, l < r → r ≤ len nums → subSum nums l r < target.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans)
    (hzero : ans.val = 0), ∀ l r : Nat, l < r → r ≤ len nums → subSum nums l r < target.val) := by
  sorry

/-- Whenever the function returns a result ans, ans = 1 if and only if there exists an index i with 0 <= i < len(nums) and nums[i] >= target.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_8 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans) :
    ans.val = 1 ↔ hasLargeEntry nums target.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans), ans.val = 1 ↔ hasLargeEntry nums target.val) := by
  sorry

/-- Whenever the function returns a result ans, ans = len(nums) if and only if sum_{k=0}^{len(nums)-1} nums[k] >= target and for every pair (l,r) with 0 <= l < r <= len(nums) and (l,r) != (0,len(nums)), sum_{k=l}^{r-1} nums[k] < target.
  Preconditions: target and nums satisfy the problem constraints: 1 <= target <= 10^9; 1 <= len(nums) <= 10^5; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_9 (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans) :
    ans.val = (len nums : Int) ↔
      (target.val ≤ subSum nums 0 (len nums) ∧
        ∀ l r : Nat, l < r → r ≤ len nums → ¬ (l = 0 ∧ r = len nums) →
          subSum nums l r < target.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target : I64) (nums : Slice I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (ans : I64) (hans : Aegis.MinSubArrayLen.min_sub_array_len target nums = ok ans), ans.val = (len nums : Int) ↔
      (target.val ≤ subSum nums 0 (len nums) ∧
        ∀ l r : Nat, l < r → r ≤ len nums → ¬ (l = 0 ∧ r = len nums) →
          subSum nums l r < target.val)) := by
  sorry

/-- Let ans1 and ans2 be the results returned by min_sub_array_len on (target1, nums) and (target2, nums), respectively. Whenever these results are returned, the following holds: if ans1 = 0 then ans2 = 0; and if ans2 > 0 then ans1 > 0 and ans1 <= ans2.
  Preconditions: All mentioned inputs satisfy the problem constraints: 1 <= target1 <= 10^9 and 1 <= target2 <= 10^9; the shared slice nums satisfies 1 <= len(nums) <= 10^5 and 1 <= nums[i] <= 10^4 for every 0 <= i < len(nums); and target1 <= target2. All Std.I64 values are interpreted as mathematical integers in their range. -/
theorem spec_10 (target1 target2 : I64) (nums : Slice I64)
    (ht1lo : 1 ≤ target1.val) (ht1hi : target1.val ≤ 1000000000)
    (ht2lo : 1 ≤ target2.val) (ht2hi : target2.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hle : target1.val ≤ target2.val)
    (ans1 ans2 : I64)
    (hans1 : Aegis.MinSubArrayLen.min_sub_array_len target1 nums = ok ans1)
    (hans2 : Aegis.MinSubArrayLen.min_sub_array_len target2 nums = ok ans2) :
    (ans1.val = 0 → ans2.val = 0) ∧ (0 < ans2.val → 0 < ans1.val ∧ ans1.val ≤ ans2.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target1 target2 : I64) (nums : Slice I64)
    (ht1lo : 1 ≤ target1.val) (ht1hi : target1.val ≤ 1000000000)
    (ht2lo : 1 ≤ target2.val) (ht2hi : target2.val ≤ 1000000000)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 100000)
    (hne : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hle : target1.val ≤ target2.val)
    (ans1 ans2 : I64)
    (hans1 : Aegis.MinSubArrayLen.min_sub_array_len target1 nums = ok ans1)
    (hans2 : Aegis.MinSubArrayLen.min_sub_array_len target2 nums = ok ans2), (ans1.val = 0 → ans2.val = 0) ∧ (0 < ans2.val → 0 < ans1.val ∧ ans1.val ≤ ans2.val)) := by
  sorry

end AegisSpec.MinSubArrayLen
