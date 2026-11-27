import Aegis.LongestConsecutive.Code.Funs

/-!
# Specifications of `Aegis.LongestConsecutive.longest_consecutive`

LeetCode problem `longest-consecutive-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestConsecutive

open Aeneas.Std.Result

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def occurs (nums : Slice Std.I64) (v : Int) : Prop := v ∈ vals nums

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def numsMin (nums : Slice Std.I64) : Int := listMin (vals nums)

def numsMax (nums : Slice Std.I64) : Int := listMax (vals nums)

def HasConsecutiveRun (nums : Slice Std.I64) (a k : Int) : Prop :=
  ∀ j : Int, 0 ≤ j → j < k → occurs nums (a + j)

def IsRunLength (nums : Slice Std.I64) (k : Int) : Prop :=
  0 ≤ k ∧ ∃ a : Int, HasConsecutiveRun nums a k

/-- The function returns a result r, and r is the largest integer k with k >= 0 such that there exists an integer a for which every integer j with 0 <= j < k satisfies: the value a + j occurs at least once among nums[0], ..., nums[len(nums)-1]. For k = 0 the condition is vacuous; when len(nums) = 0 the largest such k is 0.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r ∧
      IsRunLength nums r.val ∧ ∀ k : Int, IsRunLength nums k → k ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r ∧
      IsRunLength nums r.val ∧ ∀ k : Int, IsRunLength nums k → k ≤ r.val) := by
  sorry

/-- For every slice nums satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = 0 then r = 0.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      nums.val.length = 0 → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      nums.val.length = 0 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) > 0 then 1 <= r.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      0 < nums.val.length → 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      0 < nums.val.length → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exists an integer a such that for every integer j with 0 <= j < r, the value a + j occurs at least once among nums[0], ..., nums[len(nums)-1].
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < r.val →
      ∃ a : Int, HasConsecutiveRun nums a r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < r.val →
      ∃ a : Int, HasConsecutiveRun nums a r.val) := by
  sorry

/-- Whenever the function returns a result r, there is no integer a such that every integer j with 0 <= j <= r satisfies: the value a + j occurs at least once among nums[0], ..., nums[len(nums)-1].
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      ¬ ∃ a : Int, ∀ j : Int, 0 ≤ j → j ≤ r.val → occurs nums (a + j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      ¬ ∃ a : Int, ∀ j : Int, 0 ≤ j → j ≤ r.val → occurs nums (a + j)) := by
  sorry

/-- For all such slices xs and ys, if for every integer v, v occurs among xs[0], ..., xs[len(xs)-1] if and only if v occurs among ys[0], ..., ys[len(ys)-1], then whenever the calls longest_consecutive(xs) and longest_consecutive(ys) return results r_xs and r_ys respectively, r_xs = r_ys.
  Preconditions: For slices xs and ys, len(xs) <= 100000, len(ys) <= 100000, and every element of xs and every element of ys is between -1000000000 and 1000000000 inclusive. -/
theorem spec_8 (xs ys : Slice Std.I64)
    (hxlen : xs.val.length ≤ 100000)
    (hylen : ys.val.length ≤ 100000)
    (hxbnd : ∀ x ∈ xs.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
    (hybnd : ∀ y ∈ ys.val, -1000000000 ≤ y.val ∧ y.val ≤ 1000000000)
    (hocc : ∀ v : Int, occurs xs v ↔ occurs ys v) :
    ∀ rxs rys, Aegis.LongestConsecutive.longest_consecutive xs = ok rxs →
      Aegis.LongestConsecutive.longest_consecutive ys = ok rys → rxs.val = rys.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (xs ys : Slice Std.I64)
    (hxlen : xs.val.length ≤ 100000)
    (hylen : ys.val.length ≤ 100000)
    (hxbnd : ∀ x ∈ xs.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
    (hybnd : ∀ y ∈ ys.val, -1000000000 ≤ y.val ∧ y.val ≤ 1000000000)
    (hocc : ∀ v : Int, occurs xs v ↔ occurs ys v), ∀ rxs rys, Aegis.LongestConsecutive.longest_consecutive xs = ok rxs →
      Aegis.LongestConsecutive.longest_consecutive ys = ok rys → rxs.val = rys.val) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) > 0 and every integer v with min(nums) <= v <= max(nums) occurs at least once among nums[0], ..., nums[len(nums)-1], then r = max(nums) - min(nums) + 1, where min(nums) and max(nums) are the least and greatest entries of nums.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      (∀ v : Int, numsMin nums ≤ v → v ≤ numsMax nums → occurs nums v) →
      r.val = numsMax nums - numsMin nums + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      (∀ v : Int, numsMin nums ≤ v → v ≤ numsMax nums → occurs nums v) →
      r.val = numsMax nums - numsMin nums + 1) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) > 0 and no two distinct values occurring in nums differ by exactly 1, then r = 1.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      (∀ v w : Int, occurs nums v → occurs nums w → v + 1 ≠ w) → r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      (∀ v w : Int, occurs nums v → occurs nums w → v + 1 ≠ w) → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = n > 0, then r = n if and only if the n entries nums[0], ..., nums[n-1] are pairwise distinct and max(nums) - min(nums) + 1 = n, where min(nums) and max(nums) are the least and greatest entries of nums.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64) (n : ℕ)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
    (hn : nums.val.length = n)
    (hnpos : 0 < n) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      (r.val = (n : Int) ↔
        (vals nums).Nodup ∧ numsMax nums - numsMin nums + 1 = (n : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
    (hn : nums.val.length = n)
    (hnpos : 0 < n), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      (r.val = (n : Int) ↔
        (vals nums).Nodup ∧ numsMax nums - numsMin nums + 1 = (n : Int))) := by
  sorry

/-- Whenever the function returns a result r, r <= |{ nums[i] : 0 <= i < len(nums) }|, the number of distinct values occurring in nums.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      r.val ≤ ((vals nums).toFinset.card : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      r.val ≤ ((vals nums).toFinset.card : Int)) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) > 0 then r <= max(nums) - min(nums) + 1, where min(nums) and max(nums) are the least and greatest entries of nums.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      r.val ≤ numsMax nums - numsMin nums + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r → 0 < nums.val.length →
      r.val ≤ numsMax nums - numsMin nums + 1) := by
  sorry

/-- Whenever the function returns a result r, if there exist indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), and nums[i] + 1 = nums[j], then r >= 2.
  Preconditions: len(nums) <= 100000 and for every index i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      (∃ (i j : Fin nums.val.length), (nums.val.get i).val + 1 = (nums.val.get j).val) →
      2 ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length ≤ 100000)
    (hbnd : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, Aegis.LongestConsecutive.longest_consecutive nums = ok r →
      (∃ (i j : Fin nums.val.length), (nums.val.get i).val + 1 = (nums.val.get j).val) →
      2 ≤ r.val) := by
  sorry

end AegisSpec.LongestConsecutive
