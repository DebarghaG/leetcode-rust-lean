import Aegis.MinSwaps.Code.Funs

/-!
# Specifications of `Aegis.MinSwaps.min_swaps`

LeetCode problem `minimum-swaps-to-group-all-1s-together-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinSwaps

namespace AegisSpec.MinSwaps

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : Nat := nums.val.length

def entryAt (l : List Int) (i : Nat) : Int := l.getD i 0

def onesCount (l : List Int) : Nat := (l.filter (fun x => decide (x = 1))).length

def windowCount (l : List Int) (k s : Nat) : Nat :=
  ((List.range k).filter (fun j => decide (entryAt l ((s + j) % l.length) = 1))).length

def maxWindowCount (l : List Int) (k : Nat) : Nat :=
  ((List.range l.length).map (fun s => windowCount l k s)).foldr max 0

def rotateVals (l : List Int) (t : Nat) : List Int :=
  (List.range l.length).map (fun i => entryAt l ((i + t) % l.length))

/-- Let k be the number of indices i with 0 <= i < n and nums[i] = 1. For each start s with 0 <= s < n, let c(s) be the number of j with 0 <= j < k and nums[(s + j) mod n] = 1. Let M = max { c(s) | 0 <= s < n }. Whenever min_swaps(nums) returns a result r, r = k - M.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    r.val = (onesCount (vals nums) : Int) -
      (maxWindowCount (vals nums) (onesCount (vals nums)) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r), r.val = (onesCount (vals nums) : Int) -
      (maxWindowCount (vals nums) (onesCount (vals nums)) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, min_swaps(nums) returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1) :
    ∃ r : Std.I64, min_swaps nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1), ∃ r : Std.I64, min_swaps nums = ok r) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < n and nums[i] = 1. Whenever min_swaps(nums) returns a result r, 0 <= r <= min(k, n - k).
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    0 ≤ r.val ∧ r.val ≤
      ((min (onesCount (vals nums)) (len nums - onesCount (vals nums)) : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r), 0 ≤ r.val ∧ r.val ≤
      ((min (onesCount (vals nums)) (len nums - onesCount (vals nums)) : Nat) : Int)) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < n and nums[i] = 1. For each start s with 0 <= s < n, let c(s) be the number of j with 0 <= j < k and nums[(s + j) mod n] = 1. Whenever min_swaps(nums) returns a result r, there exists s with 0 <= s < n such that c(s) = k - r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    ∃ s, s < len nums ∧
      (windowCount (vals nums) (onesCount (vals nums)) s : Int) =
        (onesCount (vals nums) : Int) - r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r), ∃ s, s < len nums ∧
      (windowCount (vals nums) (onesCount (vals nums)) s : Int) =
        (onesCount (vals nums) : Int) - r.val) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < n and nums[i] = 1. For each start s with 0 <= s < n, let c(s) be the number of j with 0 <= j < k and nums[(s + j) mod n] = 1. Whenever min_swaps(nums) returns a result r, for every s with 0 <= s < n, c(s) <= k - r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    ∀ s, s < len nums →
      (windowCount (vals nums) (onesCount (vals nums)) s : Int) ≤
        (onesCount (vals nums) : Int) - r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r), ∀ s, s < len nums →
      (windowCount (vals nums) (onesCount (vals nums)) s : Int) ≤
        (onesCount (vals nums) : Int) - r.val) := by
  sorry

/-- For every integer t with 0 <= t < n, let rot be the length-n array defined by rot[i] = nums[(i + t) mod n] for 0 <= i < n. Whenever min_swaps(nums) returns r and min_swaps(rot) returns r_rot, r_rot = r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_6 (nums rot : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (t : Nat) (h_t : t < len nums)
    (h_rot : vals rot = rotateVals (vals nums) t)
    (r r_rot : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_rot : min_swaps rot = ok r_rot) :
    r_rot = r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums rot : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (t : Nat) (h_t : t < len nums)
    (h_rot : vals rot = rotateVals (vals nums) t)
    (r r_rot : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_rot : min_swaps rot = ok r_rot), r_rot = r) := by
  sorry

/-- Let rev be the length-n array defined by rev[i] = nums[n - 1 - i] for 0 <= i < n. Whenever min_swaps(nums) returns r and min_swaps(rev) returns r_rev, r_rev = r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_7 (nums rev : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_rev : vals rev = (vals nums).reverse)
    (r r_rev : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_rev : min_swaps rev = ok r_rev) :
    r_rev = r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_rev : vals rev = (vals nums).reverse)
    (r r_rev : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_rev : min_swaps rev = ok r_rev), r_rev = r) := by
  sorry

/-- Let comp be the length-n array defined by comp[i] = 1 - nums[i] for 0 <= i < n. Whenever min_swaps(nums) returns r and min_swaps(comp) returns r_comp, r_comp = r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_8 (nums comp : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_comp : vals comp = (vals nums).map (fun x => 1 - x))
    (r r_comp : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_comp : min_swaps comp = ok r_comp) :
    r_comp = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums comp : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_comp : vals comp = (vals nums).map (fun x => 1 - x))
    (r r_comp : Std.I64) (h_ret : min_swaps nums = ok r)
    (h_ret_comp : min_swaps comp = ok r_comp), r_comp = r) := by
  sorry

/-- Whenever min_swaps(nums) returns a result r, r <= k - 1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let k be the number of ones in nums; k > 0. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_pos : 0 < onesCount (vals nums))
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    r.val ≤ (onesCount (vals nums) : Int) - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_pos : 0 < onesCount (vals nums))
    (r : Std.I64) (h_ret : min_swaps nums = ok r), r.val ≤ (onesCount (vals nums) : Int) - 1) := by
  sorry

/-- Whenever min_swaps(nums) returns a result r, r <= n - k - 1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let k be the number of ones in nums; n - k > 0. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_pos : 0 < len nums - onesCount (vals nums))
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    r.val ≤ ((len nums - onesCount (vals nums) : Nat) : Int) - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (h_pos : 0 < len nums - onesCount (vals nums))
    (r : Std.I64) (h_ret : min_swaps nums = ok r), r.val ≤ ((len nums - onesCount (vals nums) : Nat) : Int) - 1) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < n and nums[i] = 1. Whenever min_swaps(nums) returns a result r, r = 0 if and only if there exists a start s with 0 <= s < n such that for every j with 0 <= j < k, nums[(s + j) mod n] = 1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r) :
    (r.val = 0 ↔ ∃ s, s < len nums ∧
      ∀ j, j < onesCount (vals nums) → entryAt (vals nums) ((s + j) % len nums) = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 1 ≤ len nums ∧ len nums ≤ 100000)
    (h_bits : ∀ i, i < len nums → entryAt (vals nums) i = 0 ∨ entryAt (vals nums) i = 1)
    (r : Std.I64) (h_ret : min_swaps nums = ok r), (r.val = 0 ↔ ∃ s, s < len nums ∧
      ∀ j, j < onesCount (vals nums) → entryAt (vals nums) ((s + j) % len nums) = 1)) := by
  sorry

end AegisSpec.MinSwaps
