import Aegis.IsConsecutive.Code.Funs

/-!
# Specifications of `Aegis.IsConsecutive.is_consecutive`

LeetCode problem `check-if-an-array-is-consecutive`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.IsConsecutive (is_consecutive)

  namespace AegisSpec.IsConsecutive

  def values (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun a b => if b < a then b else a) x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun a b => if a < b then b else a) x

  def minVal (nums : Slice Std.I64) : Int := listMin (values nums)

  def maxVal (nums : Slice Std.I64) : Int := listMax (values nums)

  def spanVal (nums : Slice Std.I64) : Int := maxVal nums - minVal nums

  def sumVal (nums : Slice Std.I64) : Int := (values nums).sum

  def countVal (nums : Slice Std.I64) (v : Int) : Nat :=
    ((values nums).filter (fun x => x = v)).length

  def Occurs (nums : Slice Std.I64) (v : Int) : Prop :=
    ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = v

  def PairwiseDistinct (nums : Slice Std.I64) : Prop :=
    ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
      (nums.val[i]'(by omega)).val ≠ (nums.val[j]'(by omega)).val

  /-- Let n = len(nums) and let mn be the minimum of nums, i.e. the integer x with x = nums[i] for some i, 0 <= i < n, and x <= nums[j] for all j, 0 <= j < n (such an x exists because n >= 1). Whenever the function returns a result r, r = true if and only if for every integer k with 0 <= k < n there is an index i with 0 <= i < n such that nums[i] = mn + k. In particular r = false exactly when some value mn + k with 0 <= k < n does not occur in nums.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) :
      (r = true ↔
        ∀ (k : Int), 0 ≤ k → k < (nums.val.length : Int) → Occurs nums (minVal nums + k)) ∧
      (r = false ↔
        ∃ (k : Int), 0 ≤ k ∧ k < (nums.val.length : Int) ∧ ¬ Occurs nums (minVal nums + k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r), (r = true ↔
          ∀ (k : Int), 0 ≤ k → k < (nums.val.length : Int) → Occurs nums (minVal nums + k)) ∧
        (r = false ↔
          ∃ (k : Int), 0 ≤ k ∧ k < (nums.val.length : Int) ∧ ¬ Occurs nums (minVal nums + k))) := by
    sorry

  /-- The function returns a result r (it does not fail: no panic, no out-of-bounds access, no arithmetic overflow).
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
      ∃ r : Bool, is_consecutive nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : Bool, is_consecutive nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r = true, the entries of nums are pairwise distinct: for every i and j with 0 <= i < j < n, nums[i] != nums[j].
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true) :
      PairwiseDistinct nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true), PairwiseDistinct nums) := by
    sorry

  /-- Whenever the function returns a result r with r = true, max(nums) - min(nums) = len(nums) - 1, i.e. max(nums) = min(nums) + n - 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true) :
      spanVal nums = (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true), spanVal nums = (nums.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r with r = true, every entry lies in the interval [min(nums), min(nums) + n - 1]: for every i with 0 <= i < n, min(nums) <= nums[i] <= min(nums) + n - 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true) :
      ∀ (i : Nat) (hi : i < nums.val.length),
        minVal nums ≤ (nums.val[i]).val ∧
          (nums.val[i]).val ≤ minVal nums + (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true), ∀ (i : Nat) (hi : i < nums.val.length),
          minVal nums ≤ (nums.val[i]).val ∧
            (nums.val[i]).val ≤ minVal nums + (nums.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r with r = true, the sum of all entries of nums equals n * min(nums) + n * (n - 1) / 2, where n = len(nums).
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true) :
      sumVal nums = (nums.val.length : Int) * minVal nums +
        (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true), sumVal nums = (nums.val.length : Int) * minVal nums +
          (nums.val.length : Int) * ((nums.val.length : Int) - 1) / 2) := by
    sorry

  /-- If the entries of nums are pairwise distinct (for every i, j with 0 <= i < j < n, nums[i] != nums[j]) and max(nums) - min(nums) = n - 1, then whenever the function returns a result r, r = true.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_distinct : PairwiseDistinct nums)
      (h_span : spanVal nums = (nums.val.length : Int) - 1)
      (r : Bool) (hr : is_consecutive nums = ok r) :
      r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_distinct : PairwiseDistinct nums)
        (h_span : spanVal nums = (nums.val.length : Int) - 1)
        (r : Bool) (hr : is_consecutive nums = ok r), r = true) := by
    sorry

  /-- Whenever the function returns a result r with r = false, at least one of the following two witnesses exists: (a) there are indices i, j with 0 <= i < j < n and nums[i] = nums[j]; or (b) max(nums) - min(nums) > n - 1.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_false : r = false) :
      (∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
        (nums.val[i]'(by omega)).val = (nums.val[j]'(by omega)).val) ∨
        spanVal nums > (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_false : r = false), (∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]'(by omega)).val = (nums.val[j]'(by omega)).val) ∨
          spanVal nums > (nums.val.length : Int) - 1) := by
    sorry

  /-- Whenever is_consecutive(nums) returns a result r and is_consecutive(nums2) returns a result r2, r = r2.
    Preconditions: Both arrays satisfy the constraints: len(nums) >= 1, len(nums) <= 100000, all entries of nums in [0, 100000]; the same for nums2. Moreover nums2 is a permutation of nums: len(nums2) = len(nums) and for every integer v, the number of indices i with nums[i] = v equals the number of indices i with nums2[i] = v. -/
  theorem spec_9 (nums nums2 : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_n2_ge : 1 ≤ nums2.val.length) (h_n2_le : nums2.val.length ≤ 100000)
      (h_entries2 : ∀ (i : Nat) (hi : i < nums2.val.length),
        0 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100000)
      (h_perm : nums2.val.length = nums.val.length ∧
        ∀ (v : Int), countVal nums v = countVal nums2 v)
      (r r2 : Bool) (hr : is_consecutive nums = ok r)
      (hr2 : is_consecutive nums2 = ok r2) :
      r = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_n2_ge : 1 ≤ nums2.val.length) (h_n2_le : nums2.val.length ≤ 100000)
        (h_entries2 : ∀ (i : Nat) (hi : i < nums2.val.length),
          0 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100000)
        (h_perm : nums2.val.length = nums.val.length ∧
          ∀ (v : Int), countVal nums v = countVal nums2 v)
        (r r2 : Bool) (hr : is_consecutive nums = ok r)
        (hr2 : is_consecutive nums2 = ok r2), r = r2) := by
    sorry

  /-- Whenever the function returns a result r with r = true, for every integer v the number of indices i with 0 <= i < n and nums[i] = v equals 1 if min(nums) <= v <= min(nums) + n - 1, and equals 0 otherwise.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
      (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true) :
      ∀ (v : Int),
        countVal nums v =
          (if minVal nums ≤ v ∧ v ≤ minVal nums + (nums.val.length : Int) - 1
           then 1 else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_n_ge : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100000)
        (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Bool) (hr : is_consecutive nums = ok r) (hr_true : r = true), ∀ (v : Int),
          countVal nums v =
            (if minVal nums ≤ v ∧ v ≤ minVal nums + (nums.val.length : Int) - 1
             then 1 else 0)) := by
    sorry

  end AegisSpec.IsConsecutive
