import Aegis.MaximumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumScore.maximum_score`

LeetCode problem `maximum-score-of-a-good-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumScore (maximum_score)

namespace AegisSpec.MaximumScore

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map fun x => x.val

def valAt (nums : Slice Std.I64) (t : ℕ) : ℤ := (vals nums).getD t 0

def kIdx (k : Std.I64) : ℕ := k.val.toNat

def listMin : List ℤ → ℤ
  | [] => 0
  | [x] => x
  | x :: y :: ys => min x (listMin (y :: ys))

def listMax : List ℤ → ℤ
  | [] => 0
  | [x] => x
  | x :: y :: ys => max x (listMax (y :: ys))

def segMin (nums : Slice Std.I64) (i j : ℕ) : ℤ :=
  listMin (((vals nums).drop i).take (j + 1 - i))

def windowScore (nums : Slice Std.I64) (i j : ℕ) : ℤ :=
  segMin nums i j * ((j : ℤ) - (i : ℤ) + 1)

def sliceMax (nums : Slice Std.I64) : ℤ := listMax (vals nums)

def prefixScore (nums : Slice Std.I64) (j : ℕ) : ℤ := valAt nums j * ((j : ℤ) + 1)

/-- The function returns a result r, and r = max { (min(nums[i], nums[i+1], ..., nums[j])) * (j - i + 1) : 0 <= i <= k <= j < len(nums) }, where k in this formula denotes the integer value of the Lean parameter k.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)) :
    ∃ r : Std.I64,
      maximum_score nums k = ok r ∧
      (∀ i j : ℕ, i ≤ kIdx k → kIdx k ≤ j → j < nums.length →
        windowScore nums i j ≤ r.val) ∧
      (∃ i j : ℕ, i ≤ kIdx k ∧ kIdx k ≤ j ∧ j < nums.length ∧
        windowScore nums i j = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)), ∃ r : Std.I64,
      maximum_score nums k = ok r ∧
      (∀ i j : ℕ, i ≤ kIdx k → kIdx k ≤ j → j < nums.length →
        windowScore nums i j ≤ r.val) ∧
      (∃ i j : ℕ, i ≤ kIdx k ∧ kIdx k ≤ j ∧ j < nums.length ∧
        windowScore nums i j = r.val)) := by
  sorry

/-- The function does not fail; it returns some result r. In particular, index k is accessed in bounds and no arithmetic overflow or panic occurs for these inputs.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)) :
    ∃ r : Std.I64, maximum_score nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)), ∃ r : Std.I64, maximum_score nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= (max(nums[0], nums[1], ..., nums[len(nums)-1])) * len(nums).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      r.val ≤ sliceMax nums * (nums.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)), ∀ r : Std.I64, maximum_score nums k = ok r →
      r.val ≤ sliceMax nums * (nums.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every pair (i, j) with 0 <= i <= k <= j < len(nums), we have (min(nums[i], nums[i+1], ..., nums[j])) * (j - i + 1) <= r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      ∀ i j : ℕ, i ≤ kIdx k → kIdx k ≤ j → j < nums.length →
        windowScore nums i j ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)), ∀ r : Std.I64, maximum_score nums k = ok r →
      ∀ i j : ℕ, i ≤ kIdx k → kIdx k ≤ j → j < nums.length →
        windowScore nums i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i <= k <= j < len(nums) and (min(nums[i], nums[i+1], ..., nums[j])) * (j - i + 1) = r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      ∃ i j : ℕ, i ≤ kIdx k ∧ kIdx k ≤ j ∧ j < nums.length ∧
        windowScore nums i j = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ)), ∀ r : Std.I64, maximum_score nums k = ok r →
      ∃ i j : ℕ, i ≤ kIdx k ∧ kIdx k ≤ j ∧ j < nums.length ∧
        windowScore nums i j = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = nums[k] * len(nums).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; 0 <= k < len(nums); and nums[k] <= nums[t] for every t with 0 <= t < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hmin : ∀ t, t < nums.length → valAt nums (kIdx k) ≤ valAt nums t) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      r.val = valAt nums (kIdx k) * (nums.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hmin : ∀ t, t < nums.length → valAt nums (kIdx k) ≤ valAt nums t), ∀ r : Std.I64, maximum_score nums k = ok r →
      r.val = valAt nums (kIdx k) * (nums.length : ℤ)) := by
  sorry

/-- Let n = len(nums). Let rev be the slice of length n with rev[t] = nums[n - 1 - t] for every t with 0 <= t < n, and let k' = n - 1 - k, using the integer value of k. Whenever maximum_score(nums, k) returns a result r, the call maximum_score(rev, k') returns the same result r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; and 0 <= k < len(nums), where k is interpreted by its integer value. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (rev : Slice Std.I64)
    (k' : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hrev_len : rev.length = nums.length)
    (hrev_val : ∀ t, t < nums.length → valAt rev t = valAt nums (nums.length - 1 - t))
    (hk' : k'.val = (nums.length : ℤ) - 1 - k.val) :
    ∀ r : Std.I64, maximum_score nums k = ok r → maximum_score rev k' = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (rev : Slice Std.I64)
    (k' : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hrev_len : rev.length = nums.length)
    (hrev_val : ∀ t, t < nums.length → valAt rev t = valAt nums (nums.length - 1 - t))
    (hk' : k'.val = (nums.length : ℤ) - 1 - k.val), ∀ r : Std.I64, maximum_score nums k = ok r → maximum_score rev k' = ok r) := by
  sorry

/-- Let scaled be the slice of length len(nums) with scaled[t] = c * nums[t] for every t with 0 <= t < len(nums). Whenever maximum_score(nums, k) returns a result r, the call maximum_score(scaled, k) returns c * r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; 0 <= k < len(nums); c is an integer with c >= 1; and c * nums[t] <= 20000 for every t with 0 <= t < len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (c : ℤ) (scaled : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hc_pos : 1 ≤ c)
    (hc_bound : ∀ t, t < nums.length → c * valAt nums t ≤ 20000)
    (hscaled_len : scaled.length = nums.length)
    (hscaled_val : ∀ t, t < nums.length → valAt scaled t = c * valAt nums t) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      ∃ r' : Std.I64, maximum_score scaled k = ok r' ∧ r'.val = c * r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (c : ℤ) (scaled : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hc_pos : 1 ≤ c)
    (hc_bound : ∀ t, t < nums.length → c * valAt nums t ≤ 20000)
    (hscaled_len : scaled.length = nums.length)
    (hscaled_val : ∀ t, t < nums.length → valAt scaled t = c * valAt nums t), ∀ r : Std.I64, maximum_score nums k = ok r →
      ∃ r' : Std.I64, maximum_score scaled k = ok r' ∧ r'.val = c * r.val) := by
  sorry

/-- Whenever the function returns a result r, r = max { nums[j] * (j + 1) : k <= j < len(nums) }.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every t with 0 <= t < len(nums), 1 <= nums[t] <= 20000; 0 <= k < len(nums); and for every t with 0 <= t < len(nums) - 1, nums[t] >= nums[t+1]. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hmono : ∀ t, t + 1 < nums.length → valAt nums (t + 1) ≤ valAt nums t) :
    ∀ r : Std.I64, maximum_score nums k = ok r →
      (∀ j : ℕ, kIdx k ≤ j → j < nums.length → prefixScore nums j ≤ r.val) ∧
      (∃ j : ℕ, kIdx k ≤ j ∧ j < nums.length ∧ prefixScore nums j = r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hentries : ∀ t, t < nums.length → 1 ≤ valAt nums t ∧ valAt nums t ≤ 20000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < (nums.length : ℤ))
    (hmono : ∀ t, t + 1 < nums.length → valAt nums (t + 1) ≤ valAt nums t), ∀ r : Std.I64, maximum_score nums k = ok r →
      (∀ j : ℕ, kIdx k ≤ j → j < nums.length → prefixScore nums j ≤ r.val) ∧
      (∃ j : ℕ, kIdx k ≤ j ∧ j < nums.length ∧ prefixScore nums j = r.val)) := by
  sorry

end AegisSpec.MaximumScore
