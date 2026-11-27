import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `count-subarrays-of-length-three-with-a-condition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSubarrays

  namespace AegisSpec.CountSubarrays

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def entry (s : Slice Std.I64) (i : ℕ) : Option ℤ := (s.val[i]?).map (fun x => x.val)

  def windowOk (l : List ℤ) (i : ℕ) : Bool :=
    match l[i]?, l[i + 1]?, l[i + 2]? with
    | some a, some b, some c => decide (2 * (a + c) = b)
    | _, _, _ => false

  def WindowOk (l : List ℤ) (i : ℕ) : Prop := windowOk l i = true

  def winInd (l : List ℤ) (i : ℕ) : ℤ := if windowOk l i then 1 else 0

  /-- The function returns a result r, and r is the number of integers i such that 0 <= i <= n-3 and 2 * (nums[i] + nums[i+2]) = nums[i+1]. Thus r counts the contiguous length-3 windows (nums[i], nums[i+1], nums[i+2]) for which the sum of the first and third entries is exactly half of the second entry; overlapping windows are counted separately.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧
        r.val = (((List.range (n - 2)).countP (windowOk (vals nums)) : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, count_subarrays nums = ok r ∧
          r.val = (((List.range (n - 2)).countP (windowOk (vals nums)) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n-2.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, count_subarrays nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 2) := by
    sorry

  /-- The function returns a result on nums; in particular, it does not fail, panic, access an out-of-bounds index, or overflow a 64-bit integer operation.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, count_subarrays nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, count_subarrays nums = ok r) := by
    sorry

  /-- The function returns a result r, and r = 1 if 2 * (nums[0] + nums[2]) = nums[1], and r = 0 otherwise.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), n = 3, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : n = 3)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧ r.val = winInd (vals nums) 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : n = 3)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, count_subarrays nums = ok r ∧ r.val = winInd (vals nums) 0) := by
    sorry

  /-- The function returns a result r, and r > 0 if and only if there exists an integer i with 0 <= i <= n-3 such that 2 * (nums[i] + nums[i+2]) = nums[i+1].
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧
        (0 < r.val ↔ ∃ i : ℕ, i ≤ n - 3 ∧ WindowOk (vals nums) i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100), ∃ r : Std.I64, count_subarrays nums = ok r ∧
          (0 < r.val ↔ ∃ i : ℕ, i ≤ n - 3 ∧ WindowOk (vals nums) i)) := by
    sorry

  /-- When called on nums the function returns r, and when called on rev it returns r_rev; then r_rev = r.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. Define rev by len(rev) = n and rev[i] = nums[n-1-i] for every 0 <= i < n. -/
  theorem spec_6 (nums rev : Slice Std.I64) (n : ℕ) (r r_rev : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
      (hrev_len : rev.val.length = n)
      (hrev : ∀ i : ℕ, i < n → entry rev i = entry nums (n - 1 - i))
      (hr : count_subarrays nums = ok r) (hr_rev : count_subarrays rev = ok r_rev) :
      r_rev = r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (n : ℕ) (r r_rev : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
        (hrev_len : rev.val.length = n)
        (hrev : ∀ i : ℕ, i < n → entry rev i = entry nums (n - 1 - i))
        (hr : count_subarrays nums = ok r) (hr_rev : count_subarrays rev = ok r_rev), r_rev = r) := by
    sorry

  /-- When called on nums the function returns r, and when called on negnums it returns r_neg; then r_neg = r.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. Define negnums by negnums[i] = -nums[i] for every 0 <= i < n. -/
  theorem spec_7 (nums negnums : Slice Std.I64) (n : ℕ) (r r_neg : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
      (hneg_len : negnums.val.length = n)
      (hneg : ∀ i : ℕ, i < n → entry negnums i = (entry nums i).map (fun v => -v))
      (hr : count_subarrays nums = ok r) (hr_neg : count_subarrays negnums = ok r_neg) :
      r_neg = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums negnums : Slice Std.I64) (n : ℕ) (r r_neg : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
        (hneg_len : negnums.val.length = n)
        (hneg : ∀ i : ℕ, i < n → entry negnums i = (entry nums i).map (fun v => -v))
        (hr : count_subarrays nums = ok r) (hr_neg : count_subarrays negnums = ok r_neg), r_neg = r) := by
    sorry

  /-- When called on nums the function returns r, and when called on pre it returns r_pre. Let e = 1 if 2 * (nums[n-3] + nums[n-1]) = nums[n-2], and e = 0 otherwise. Then r = r_pre + e.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 4 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. Define pre by len(pre) = n-1 and pre[j] = nums[j] for every 0 <= j < n-1. -/
  theorem spec_8 (nums pre : Slice Std.I64) (n : ℕ) (r r_pre : Std.I64)
      (hn : n = nums.val.length) (h4 : 4 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
      (hpre_len : pre.val.length = n - 1)
      (hpre : ∀ j : ℕ, j < n - 1 → entry pre j = entry nums j)
      (hr : count_subarrays nums = ok r) (hr_pre : count_subarrays pre = ok r_pre) :
      r = r_pre + winInd (vals nums) (n - 3) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums pre : Slice Std.I64) (n : ℕ) (r r_pre : Std.I64)
        (hn : n = nums.val.length) (h4 : 4 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
        (hpre_len : pre.val.length = n - 1)
        (hpre : ∀ j : ℕ, j < n - 1 → entry pre j = entry nums j)
        (hr : count_subarrays nums = ok r) (hr_pre : count_subarrays pre = ok r_pre), r = r_pre + winInd (vals nums) (n - 3)) := by
    sorry

  /-- When called on nums the function returns r, and when called on suf it returns r_suf. Let e = 1 if 2 * (nums[0] + nums[2]) = nums[1], and e = 0 otherwise. Then r = r_suf + e.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 4 <= n <= 100, and for every i with 0 <= i < n, -100 <= nums[i] <= 100. Define suf by len(suf) = n-1 and suf[j] = nums[j+1] for every 0 <= j < n-1. -/
  theorem spec_9 (nums suf : Slice Std.I64) (n : ℕ) (r r_suf : Std.I64)
      (hn : n = nums.val.length) (h4 : 4 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
      (hsuf_len : suf.val.length = n - 1)
      (hsuf : ∀ j : ℕ, j < n - 1 → entry suf j = entry nums (j + 1))
      (hr : count_subarrays nums = ok r) (hr_suf : count_subarrays suf = ok r_suf) :
      r = r_suf + winInd (vals nums) 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums suf : Slice Std.I64) (n : ℕ) (r r_suf : Std.I64)
        (hn : n = nums.val.length) (h4 : 4 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
        (hsuf_len : suf.val.length = n - 1)
        (hsuf : ∀ j : ℕ, j < n - 1 → entry suf j = entry nums (j + 1))
        (hr : count_subarrays nums = ok r) (hr_suf : count_subarrays suf = ok r_suf), r = r_suf + winInd (vals nums) 0) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, for every i with 0 <= i < n, -100 <= nums[i] <= 100, and for every j with 1 <= j <= n-2, nums[j] is odd. -/
  theorem spec_10 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
      (hodd : ∀ (j : ℕ), 1 ≤ j → j ≤ n - 2 → ∀ v : ℤ, entry nums j = some v → Odd v) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hbounds : ∀ x : ℤ, x ∈ vals nums → -100 ≤ x ∧ x ≤ 100)
        (hodd : ∀ (j : ℕ), 1 ≤ j → j ≤ n - 2 → ∀ v : ℤ, entry nums j = some v → Odd v), ∃ r : Std.I64, count_subarrays nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = n-2 if c = 0, and r = 0 if c != 0.
    Preconditions: nums is a slice of 64-bit integers, n = len(nums), 3 <= n <= 100, and there is an integer c such that for every i with 0 <= i < n, nums[i] = c. -/
  theorem spec_11 (nums : Slice Std.I64) (c : ℤ) (n : ℕ)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
      (hc : ∀ x : ℤ, x ∈ vals nums → x = c) :
      ∃ r : Std.I64, count_subarrays nums = ok r ∧
        ((c = 0 ∧ r.val = (n : ℤ) - 2) ∨ (c ≠ 0 ∧ r.val = 0)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (c : ℤ) (n : ℕ)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100 : n ≤ 100)
        (hc : ∀ x : ℤ, x ∈ vals nums → x = c), ∃ r : Std.I64, count_subarrays nums = ok r ∧
          ((c = 0 ∧ r.val = (n : ℤ) - 2) ∨ (c ≠ 0 ∧ r.val = 0))) := by
    sorry

  end AegisSpec.CountSubarrays
