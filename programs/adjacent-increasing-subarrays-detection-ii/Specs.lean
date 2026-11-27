import Aegis.MaxIncreasingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.MaxIncreasingSubarrays.max_increasing_subarrays`

LeetCode problem `adjacent-increasing-subarrays-detection-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxIncreasingSubarrays

  def toList (nums : Slice Std.I64) : List Std.I64 := nums.val

  def slot (nums : Slice Std.I64) (i : Int) : Int :=
    match (toList nums)[i.toNat]? with
    | some x => x.val
    | none => 0

  def lenI (nums : Slice Std.I64) : Int := (nums.val.length : Int)

  theorem slot_of_mem (nums : Slice Std.I64) (i : Int) (h0 : 0 ≤ i) (h1 : i < lenI nums) :
      slot nums i = (nums.val[i.toNat]'(by unfold lenI at h1; omega)).val := by
    unfold slot toList
    rw [List.getElem?_eq_getElem (by unfold lenI at h1; omega)]

  def IncWindow (nums : Slice Std.I64) (a k : Int) : Prop :=
    ∀ t : Int, 0 ≤ t → t < k - 1 → slot nums (a + t) < slot nums (a + t + 1)

  def AdjacentIncWindows (nums : Slice Std.I64) (a k : Int) : Prop :=
    IncWindow nums a k ∧ IncWindow nums (a + k) k

  def Feasible (nums : Slice Std.I64) (k : Int) : Prop :=
    1 ≤ k ∧ 2 * k ≤ lenI nums ∧
      ∃ a : Int, 0 ≤ a ∧ a + 2 * k ≤ lenI nums ∧ AdjacentIncWindows nums a k

  def IsLongestIncreasingLen (nums : Slice Std.I64) (L : Int) : Prop :=
    1 ≤ L ∧
      (∃ a : Int, 0 ≤ a ∧ a + L ≤ lenI nums ∧ IncWindow nums a L) ∧
      (∀ l : Int, 1 ≤ l →
        (∃ a : Int, 0 ≤ a ∧ a + l ≤ lenI nums ∧ IncWindow nums a l) → l ≤ L)

  /-- Whenever the function returns a result r, r is the maximum integer k such that: (1) k >= 1; (2) 2*k <= len(nums); and (3) there exists an integer a with 0 <= a and a + 2*k <= len(nums) for which both adjacent length-k blocks are strictly increasing. Explicitly, the first block condition is: for every t with 0 <= t < k-1, nums[a+t] < nums[a+t+1]. The second block condition is: for every t with 0 <= t < k-1, nums[a+k+t] < nums[a+k+t+1]. For k=1 both conditions are vacuous.
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      Feasible nums r.val ∧ ∀ k : Int, Feasible nums k → k ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), Feasible nums r.val ∧ ∀ k : Int, Feasible nums k → k ≤ r.val) := by
    sorry

  /-- The function returns a result r rather than failing; equivalently, there exists an integer r such that max_increasing_subarrays nums = Result.ok r.
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000), ∃ r : Std.I64, Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 1 <= r and 2*r <= len(nums).
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      1 ≤ r.val ∧ 2 * r.val ≤ lenI nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), 1 ≤ r.val ∧ 2 * r.val ≤ lenI nums) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer a with 0 <= a and a + 2*r <= len(nums) such that for every t with 0 <= t < r-1, nums[a+t] < nums[a+t+1], and for every t with 0 <= t < r-1, nums[a+r+t] < nums[a+r+t+1].
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      ∃ a : Int, 0 ≤ a ∧ a + 2 * r.val ≤ lenI nums ∧
        AdjacentIncWindows nums a r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), ∃ a : Int, 0 ≤ a ∧ a + 2 * r.val ≤ lenI nums ∧
          AdjacentIncWindows nums a r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with k > r and 2*k <= len(nums), there is no integer a with 0 <= a and a + 2*k <= len(nums) such that both adjacent length-k blocks nums[a..a+k-1] and nums[a+k..a+2*k-1] are strictly increasing. Here strictly increasing means every adjacent pair inside the block is increasing.
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      ∀ k : Int, r.val < k → 2 * k ≤ lenI nums →
        ¬ ∃ a : Int, 0 ≤ a ∧ a + 2 * k ≤ lenI nums ∧ AdjacentIncWindows nums a k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), ∀ k : Int, r.val < k → 2 * k ≤ lenI nums →
          ¬ ∃ a : Int, 0 ≤ a ∧ a + 2 * k ≤ lenI nums ∧ AdjacentIncWindows nums a k) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 if nums[0] < nums[1] and nums[2] < nums[3], and r = 1 otherwise.
    Preconditions: len(nums) = 4 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : lenI nums = 4)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      ((slot nums 0 < slot nums 1 ∧ slot nums 2 < slot nums 3) → r.val = 2) ∧
        (¬ (slot nums 0 < slot nums 1 ∧ slot nums 2 < slot nums 3) → r.val = 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : lenI nums = 4)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), ((slot nums 0 < slot nums 1 ∧ slot nums 2 < slot nums 3) → r.val = 2) ∧
          (¬ (slot nums 0 < slot nums 1 ∧ slot nums 2 < slot nums 3) → r.val = 1)) := by
    sorry

  /-- If for every i with 0 <= i < len(nums)-1 we have nums[i] < nums[i+1], then whenever the function returns a result r, 2*r <= len(nums) and len(nums) < 2*(r+1).
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hinc : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 → slot nums i < slot nums (i + 1))
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      2 * r.val ≤ lenI nums ∧ lenI nums < 2 * (r.val + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hinc : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 → slot nums i < slot nums (i + 1))
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), 2 * r.val ≤ lenI nums ∧ lenI nums < 2 * (r.val + 1)) := by
    sorry

  /-- If for every i with 0 <= i < len(nums)-1 we have nums[i] >= nums[i+1], then whenever the function returns a result r, r = 1.
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hdec : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 → slot nums (i + 1) ≤ slot nums i)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hdec : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 → slot nums (i + 1) ≤ slot nums i)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k <= r there exists an integer a with 0 <= a and a + 2*k <= len(nums) such that for every t with 0 <= t < k-1, nums[a+t] < nums[a+t+1], and for every t with 0 <= t < k-1, nums[a+k+t] < nums[a+k+t+1].
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      ∀ k : Int, 1 ≤ k → k ≤ r.val →
        ∃ a : Int, 0 ≤ a ∧ a + 2 * k ≤ lenI nums ∧ AdjacentIncWindows nums a k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), ∀ k : Int, 1 ≤ k → k ≤ r.val →
          ∃ a : Int, 0 ≤ a ∧ a + 2 * k ≤ lenI nums ∧ AdjacentIncWindows nums a k) := by
    sorry

  /-- For any two slices nums and other satisfying the preconditions, if for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] if and only if other[i] < other[i+1], then whenever max_increasing_subarrays nums returns a result r and max_increasing_subarrays other returns a result r', we have r = r'.
    Preconditions: 2 <= len(nums) <= 200000, len(other) = len(nums), and every element of nums and of other lies in [-1000000000, 1000000000]. -/
  theorem spec_10 (nums other : Slice Std.I64) (r r' : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hlen_other : lenI other = lenI nums)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hbound' : ∀ i : Int, 0 ≤ i → i < lenI other →
        -1000000000 ≤ slot other i ∧ slot other i ≤ 1000000000)
      (hcmp : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 →
        (slot nums i < slot nums (i + 1) ↔ slot other i < slot other (i + 1)))
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r)
      (hres' : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays other = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums other : Slice Std.I64) (r r' : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hlen_other : lenI other = lenI nums)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hbound' : ∀ i : Int, 0 ≤ i → i < lenI other →
          -1000000000 ≤ slot other i ∧ slot other i ≤ 1000000000)
        (hcmp : ∀ i : Int, 0 ≤ i → i < lenI nums - 1 →
          (slot nums i < slot nums (i + 1) ↔ slot other i < slot other (i + 1)))
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r)
        (hres' : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays other = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= L, where L is the length of a longest contiguous strictly increasing subarray of nums: L = max { l | 1 <= l <= len(nums), there exists a with 0 <= a and a+l <= len(nums), and for every t with 0 <= t < l-1, nums[a+t] < nums[a+t+1] }.
    Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
      (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
        -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
      (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r) :
      ∀ L : Int, IsLongestIncreasingLen nums L → r.val ≤ L := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_low : 2 ≤ lenI nums) (hlen_high : lenI nums ≤ 200000)
        (hbound : ∀ i : Int, 0 ≤ i → i < lenI nums →
          -1000000000 ≤ slot nums i ∧ slot nums i ≤ 1000000000)
        (hres : Aegis.MaxIncreasingSubarrays.max_increasing_subarrays nums = ok r), ∀ L : Int, IsLongestIncreasingLen nums L → r.val ≤ L) := by
    sorry

  end AegisSpec.MaxIncreasingSubarrays
