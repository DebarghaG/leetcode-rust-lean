import Aegis.ReductionOperations.Code.Funs

/-!
# Specifications of `Aegis.ReductionOperations.reduction_operations`

LeetCode problem `reduction-operations-to-make-the-array-elements-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ReductionOperations (reduction_operations)

  namespace AegisSpec.ReductionOperations

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def Occurs (l : List Int) (v : Int) : Prop := v ∈ l

  def distinctOf (l : List Int) : List Int := l.dedup

  def distinctCount (l : List Int) : Nat := (distinctOf l).length

  def minOf : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def countGe (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (v ≤ x))).length

  def countEq (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (x = v))).length

  def countGt (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (v < x))).length

  def lessCount (l : List Int) (x : Int) : Nat :=
    ((distinctOf l).filter (fun v => decide (v < x))).length

  def opsCount (l : List Int) : Int :=
    ((((distinctOf l).filter (fun v => decide (minOf l < v))).map (fun v => (countGe l v : Int))).sum)

  def lessCountSum (l : List Int) : Int := (l.map (fun x => (lessCount l x : Int))).sum

  def AllEqual (l : List Int) : Prop := ∀ x ∈ l, x = l.headD 0

  def Bounds (l : List Int) : Prop := ∀ x ∈ l, 1 ≤ x ∧ x ≤ 50000

  def ValidInput (nums : Slice Std.I64) : Prop :=
    Bounds (vals nums) ∧ 1 ≤ nums.val.length ∧ nums.val.length ≤ 50000

  /-- The function returns a result r, and r = sum_{v in D, v > min(nums)} C(v), where D = {v | there exists i with 0 <= i < len(nums) and nums[i] = v}, min(nums) is the least value occurring in nums, and for each v, C(v) = #{i | 0 <= i < len(nums) and nums[i] >= v}. This sum is exactly the number of operations performed by the deterministic process in the problem statement before all elements become equal.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_1 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∃ r : Std.I64, reduction_operations nums = ok r ∧ r.val = opsCount (vals nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∃ r : Std.I64, reduction_operations nums = ok r ∧ r.val = opsCount (vals nums)) := by
    sorry

  /-- The function returns successfully with some result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_2 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∃ r : Std.I64, reduction_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∃ r : Std.I64, reduction_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_3 (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
      (hr : reduction_operations nums = ok r) : 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
        (hr : reduction_operations nums = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) * (d - 1), where d is the number of distinct values occurring in nums, i.e. d = #{v | there exists i with 0 <= i < len(nums) and nums[i] = v}.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_4 (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
      (hr : reduction_operations nums = ok r) :
      r.val ≤ (nums.val.length : Int) * ((distinctCount (vals nums) : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
        (hr : reduction_operations nums = ok r), r.val ≤ (nums.val.length : Int) * ((distinctCount (vals nums) : Int) - 1)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 1 <= len(nums) <= 50000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000, and for every i with 0 <= i < len(nums), nums[i] = nums[0]. -/
  theorem spec_5 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (hall : AllEqual (vals nums)) :
      ∃ r : Std.I64, reduction_operations nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (hall : AllEqual (vals nums)), ∃ r : Std.I64, reduction_operations nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = #{i | 0 <= i < len(nums) and nums[i] = b}, where b is the larger element of D.
    Preconditions: 1 <= len(nums) <= 50000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000, and there exist integers a and b with a < b such that D = {a, b}, where D = {v | there exists i with 0 <= i < len(nums) and nums[i] = v}. -/
  theorem spec_6 (nums : Slice Std.I64) (a b : Int) (hpre : ValidInput nums)
      (hab : a < b) (hD : ∀ v : Int, Occurs (vals nums) v ↔ v = a ∨ v = b) :
      ∃ r : Std.I64,
        reduction_operations nums = ok r ∧ r.val = (countEq (vals nums) b : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (a b : Int) (hpre : ValidInput nums)
        (hab : a < b) (hD : ∀ v : Int, Occurs (vals nums) v ↔ v = a ∨ v = b), ∃ r : Std.I64,
          reduction_operations nums = ok r ∧ r.val = (countEq (vals nums) b : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if all elements of nums are equal, i.e. for every i with 0 <= i < len(nums), nums[i] = nums[0].
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_7 (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
      (hr : reduction_operations nums = ok r) : r.val = 0 ↔ AllEqual (vals nums) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
        (hr : reduction_operations nums = ok r), r.val = 0 ↔ AllEqual (vals nums)) := by
    sorry

  /-- The function returns a result r and r = len(nums) * (len(nums) - 1) / 2.
    Preconditions: 1 <= len(nums) <= 50000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000, and for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (hnd : (vals nums).Nodup) :
      ∃ r : Std.I64,
        reduction_operations nums = ok r ∧
          r.val = ((nums.val.length : Int) * ((nums.val.length : Int) - 1)) / 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (hnd : (vals nums).Nodup), ∃ r : Std.I64,
          reduction_operations nums = ok r ∧
            r.val = ((nums.val.length : Int) * ((nums.val.length : Int) - 1)) / 2) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums)-1} L(nums[i]), where for each integer x, L(x) = #{v | v occurs in nums and v < x}.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_9 (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
      (hr : reduction_operations nums = ok r) : r.val = lessCountSum (vals nums) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
        (hr : reduction_operations nums = ok r), r.val = lessCountSum (vals nums)) := by
    sorry

  /-- Whenever reduction_operations nums returns a result r and reduction_operations nums2 returns a result r2, r = r2.
    Preconditions: nums and nums2 are slices of i64 such that both satisfy 1 <= len <= 50000 and 1 <= element <= 50000, and for every integer v, #{i | 0 <= i < len(nums) and nums[i] = v} = #{j | 0 <= j < len(nums2) and nums2[j] = v}. -/
  theorem spec_10 (nums nums2 : Slice Std.I64) (hpre : ValidInput nums)
      (hpre2 : ValidInput nums2)
      (hcounts : ∀ v : Int, countEq (vals nums) v = countEq (vals nums2) v)
      (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
      (hr2 : reduction_operations nums2 = ok r2) : r.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (hpre : ValidInput nums)
        (hpre2 : ValidInput nums2)
        (hcounts : ∀ v : Int, countEq (vals nums) v = countEq (vals nums2) v)
        (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
        (hr2 : reduction_operations nums2 = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= N, where N = #{i | 0 <= i < len(nums) and nums[i] > min(nums)} and min(nums) is the least value occurring in nums.
    Preconditions: 1 <= len(nums) <= 50000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50000. -/
  theorem spec_11 (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
      (hr : reduction_operations nums = ok r) :
      (countGt (vals nums) (minOf (vals nums)) : Int) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (r : Std.I64)
        (hr : reduction_operations nums = ok r), (countGt (vals nums) (minOf (vals nums)) : Int) ≤ r.val) := by
    sorry

  /-- If reduction_operations nums returns a result r and reduction_operations nums2 returns a result r2, then r2 = r + d, where d = #{v | there exists i with 0 <= i < len(nums) and nums[i] = v}.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 49999 and 1 <= nums[i] <= 50000 for all i with 0 <= i < len(nums); M is an integer with 1 <= M <= 50000 and M > nums[i] for every i with 0 <= i < len(nums); nums2 is the slice of length len(nums)+1 such that nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = M. -/
  theorem spec_12 (nums nums2 : Slice Std.I64) (M : Int) (hpre : ValidInput nums)
      (hlen : nums.val.length ≤ 49999) (hM1 : 1 ≤ M) (hM2 : M ≤ 50000)
      (hM : ∀ x ∈ vals nums, x < M) (hcat : vals nums2 = vals nums ++ [M])
      (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
      (hr2 : reduction_operations nums2 = ok r2) :
      r2.val = r.val + (distinctCount (vals nums) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (M : Int) (hpre : ValidInput nums)
        (hlen : nums.val.length ≤ 49999) (hM1 : 1 ≤ M) (hM2 : M ≤ 50000)
        (hM : ∀ x ∈ vals nums, x < M) (hcat : vals nums2 = vals nums ++ [M])
        (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
        (hr2 : reduction_operations nums2 = ok r2), r2.val = r.val + (distinctCount (vals nums) : Int)) := by
    sorry

  /-- If reduction_operations nums returns a result r and reduction_operations nums2 returns a result r2, then r2 = r + #{v | v occurs in nums and v < x}.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 49999 and 1 <= nums[i] <= 50000 for all i with 0 <= i < len(nums); x is an integer with 1 <= x <= 50000 that occurs in nums; nums2 is the slice of length len(nums)+1 such that nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = x. -/
  theorem spec_13 (nums nums2 : Slice Std.I64) (x : Int) (hpre : ValidInput nums)
      (hlen : nums.val.length ≤ 49999) (hx1 : 1 ≤ x) (hx2 : x ≤ 50000)
      (hx : Occurs (vals nums) x) (hcat : vals nums2 = vals nums ++ [x])
      (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
      (hr2 : reduction_operations nums2 = ok r2) :
      r2.val = r.val + (lessCount (vals nums) x : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (x : Int) (hpre : ValidInput nums)
        (hlen : nums.val.length ≤ 49999) (hx1 : 1 ≤ x) (hx2 : x ≤ 50000)
        (hx : Occurs (vals nums) x) (hcat : vals nums2 = vals nums ++ [x])
        (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
        (hr2 : reduction_operations nums2 = ok r2), r2.val = r.val + (lessCount (vals nums) x : Int)) := by
    sorry

  /-- If reduction_operations nums returns a result r and reduction_operations nums2 returns a result r2, then r2 = r + len(nums).
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 49999 and 1 <= nums[i] <= 50000 for all i with 0 <= i < len(nums); M is an integer with 1 <= M <= 50000 and M < nums[i] for every i with 0 <= i < len(nums); nums2 is the slice of length len(nums)+1 such that nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = M. -/
  theorem spec_14 (nums nums2 : Slice Std.I64) (M : Int) (hpre : ValidInput nums)
      (hlen : nums.val.length ≤ 49999) (hM1 : 1 ≤ M) (hM2 : M ≤ 50000)
      (hM : ∀ x ∈ vals nums, M < x) (hcat : vals nums2 = vals nums ++ [M])
      (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
      (hr2 : reduction_operations nums2 = ok r2) :
      r2.val = r.val + (nums.val.length : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (M : Int) (hpre : ValidInput nums)
        (hlen : nums.val.length ≤ 49999) (hM1 : 1 ≤ M) (hM2 : M ≤ 50000)
        (hM : ∀ x ∈ vals nums, M < x) (hcat : vals nums2 = vals nums ++ [M])
        (r r2 : Std.I64) (hr : reduction_operations nums = ok r)
        (hr2 : reduction_operations nums2 = ok r2), r2.val = r.val + (nums.val.length : Int)) := by
    sorry

  end AegisSpec.ReductionOperations
