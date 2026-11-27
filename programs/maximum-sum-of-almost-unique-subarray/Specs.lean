import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `maximum-sum-of-almost-unique-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSum

def natOf {ty : IScalarTy} (x : IScalar ty) : Nat := x.val.toNat

def sliceInts (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def sliceWindow (nums : Slice I64) (s k : Nat) : List Int :=
  ((sliceInts nums).drop s).take k

def distinctCount (l : List Int) : Nat := l.dedup.length

def windowSum (nums : Slice I64) (s k : Nat) : Int := (sliceWindow nums s k).sum

def totalSum (nums : Slice I64) : Int := (sliceInts nums).sum

def listMax : List Int → Int
  | [] => 0
  | x :: xs => max x (listMax xs)

def maxEntry (nums : Slice I64) : Int := listMax (sliceInts nums)

def starts (nums : Slice I64) (k : Nat) : List Nat :=
  List.range (nums.val.length - k + 1)

def Admissible (nums : Slice I64) (m k s : Nat) : Prop :=
  s + k ≤ nums.val.length ∧ m ≤ distinctCount (sliceWindow nums s k)

def maxWindowSum (nums : Slice I64) (k : Nat) : Int :=
  listMax ((starts nums k).map (fun s => windowSum nums s k))

def PairwiseDistinctWindow (nums : Slice I64) (k s : Nat) : Prop :=
  s + k ≤ nums.val.length ∧ (sliceWindow nums s k).Nodup

def maxDistinctWindowSum (nums : Slice I64) (k : Nat) : Int :=
  listMax
    ((starts nums k).filterMap
      (fun s => if (sliceWindow nums s k).Nodup then some (windowSum nums s k) else none))

/-- The function returns a result r. Call an integer s admissible if 0 <= s, s + k <= len(nums), and the values nums[s], nums[s+1], ..., nums[s+k-1] contain at least m distinct integers. If no admissible s exists, then r = 0. If at least one admissible s exists, then r is the maximum over all admissible s of the sum nums[s] + nums[s+1] + ... + nums[s+k-1].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. Interpret m and k as their nonnegative integer values. -/
theorem spec_1 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9) :
    ∃ r : I64, Aegis.MaxSum.max_sum nums m k = ok r ∧
      ((¬ ∃ s : Nat, Admissible nums (natOf m) (natOf k) s) → r.val = 0) ∧
      ((∃ s : Nat, Admissible nums (natOf m) (natOf k) s) →
        (∀ s : Nat, Admissible nums (natOf m) (natOf k) s →
          windowSum nums s (natOf k) ≤ r.val) ∧
        (∃ s : Nat, Admissible nums (natOf m) (natOf k) s ∧
          r.val = windowSum nums s (natOf k))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9), ∃ r : I64, Aegis.MaxSum.max_sum nums m k = ok r ∧
      ((¬ ∃ s : Nat, Admissible nums (natOf m) (natOf k) s) → r.val = 0) ∧
      ((∃ s : Nat, Admissible nums (natOf m) (natOf k) s) →
        (∀ s : Nat, Admissible nums (natOf m) (natOf k) s →
          windowSum nums s (natOf k) ≤ r.val) ∧
        (∃ s : Nat, Admissible nums (natOf m) (natOf k) s ∧
          r.val = windowSum nums s (natOf k)))) := by
  sorry

/-- The function returns a result r and does not fail (no panic, out-of-bounds access, or integer overflow) on any input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9) :
    ∃ r : I64, Aegis.MaxSum.max_sum nums m k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9), ∃ r : I64, Aegis.MaxSum.max_sum nums m k = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have r >= 0.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    r.val ≤ totalSum nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), r.val ≤ totalSum nums) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then r >= k.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    0 < r.val → (natOf k : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), 0 < r.val → (natOf k : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then r <= k * max_{0 <= i < len(nums)} nums[i].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    0 < r.val → r.val ≤ (natOf k : Int) * maxEntry nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), 0 < r.val → r.val ≤ (natOf k : Int) * maxEntry nums) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no integer s with 0 <= s, s + k <= len(nums), and at least m distinct values among nums[s], nums[s+1], ..., nums[s+k-1].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    (r.val = 0 ↔ ¬ ∃ s : Nat, Admissible nums (natOf m) (natOf k) s) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), (r.val = 0 ↔ ¬ ∃ s : Nat, Admissible nums (natOf m) (natOf k) s)) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists an integer s such that 0 <= s, s + k <= len(nums), the values nums[s], nums[s+1], ..., nums[s+k-1] contain at least m distinct integers, and r = nums[s] + nums[s+1] + ... + nums[s+k-1].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    0 < r.val → ∃ s : Nat, Admissible nums (natOf m) (natOf k) s ∧
      r.val = windowSum nums s (natOf k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), 0 < r.val → ∃ s : Nat, Admissible nums (natOf m) (natOf k) s ∧
      r.val = windowSum nums s (natOf k)) := by
  sorry

/-- Whenever the function returns a result r, for every integer s with 0 <= s, s + k <= len(nums), and at least m distinct values among nums[s], nums[s+1], ..., nums[s+k-1], we have r >= nums[s] + nums[s+1] + ... + nums[s+k-1].
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    ∀ s : Nat, Admissible nums (natOf m) (natOf k) s →
      windowSum nums s (natOf k) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), ∀ s : Nat, Admissible nums (natOf m) (natOf k) s →
      windowSum nums s (natOf k) ≤ r.val) := by
  sorry

/-- Whenever max_sum(nums, m1, k) returns r1 and max_sum(nums, m2, k) returns r2, we have r2 <= r1.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m1 <= m2 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_10 (nums : Slice I64) (m1 m2 k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm1_pos : 1 ≤ m1.val) (hm1m2 : m1.val ≤ m2.val) (hm2k : m2.val ≤ k.val)
    (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r1 r2 : I64) (hr1 : Aegis.MaxSum.max_sum nums m1 k = ok r1)
    (hr2 : Aegis.MaxSum.max_sum nums m2 k = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (m1 m2 k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm1_pos : 1 ≤ m1.val) (hm1m2 : m1.val ≤ m2.val) (hm2k : m2.val ≤ k.val)
    (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (r1 r2 : I64) (hr1 : Aegis.MaxSum.max_sum nums m1 k = ok r1)
    (hr2 : Aegis.MaxSum.max_sum nums m2 k = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Let rev be the array defined by rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever max_sum(nums, m, k) returns r and max_sum(rev, m, k) returns r_rev, we have r_rev = r.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_11 (nums rev : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hrev : rev.val = nums.val.reverse)
    (r r_rev : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r)
    (hr_rev : Aegis.MaxSum.max_sum rev m k = ok r_rev) :
    r_rev.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums rev : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hrev : rev.val = nums.val.reverse)
    (r r_rev : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r)
    (hr_rev : Aegis.MaxSum.max_sum rev m k = ok r_rev), r_rev.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r = 0.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; the number of distinct values in the whole array nums is less than m. -/
theorem spec_12 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hdist : (distinctCount (sliceInts nums) : Int) < m.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hdist : (distinctCount (sliceInts nums) : Int) < m.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if the whole array nums contains at least m distinct values then r = sum_{i=0}^{len(nums)-1} nums[i], and otherwise r = 0.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); k = len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_13 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hk : k.val = (nums.val.length : Int))
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    r.val = if m.val ≤ (distinctCount (sliceInts nums) : Int) then totalSum nums else 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hk : k.val = (nums.val.length : Int))
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), r.val = if m.val ≤ (distinctCount (sliceInts nums) : Int) then totalSum nums else 0) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= s <= len(nums)-k} (nums[s] + nums[s+1] + ... + nums[s+k-1]).
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); m = 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_14 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hm : m.val = 1)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    r.val = maxWindowSum nums (natOf k) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hm : m.val = 1)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), r.val = maxWindowSum nums (natOf k)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an integer s with 0 <= s, s + k <= len(nums), and nums[s], nums[s+1], ..., nums[s+k-1] are pairwise distinct, then r is the maximum of the sums nums[s] + nums[s+1] + ... + nums[s+k-1] over all such s; otherwise r = 0.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); m = k; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_15 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hm : m.val = k.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    ((∃ s : Nat, PairwiseDistinctWindow nums (natOf k) s) →
        r.val = maxDistinctWindowSum nums (natOf k)) ∧
      ((¬ ∃ s : Nat, PairwiseDistinctWindow nums (natOf k) s) → r.val = 0) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
    (hm : m.val = k.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), ((∃ s : Nat, PairwiseDistinctWindow nums (natOf k) s) →
        r.val = maxDistinctWindowSum nums (natOf k)) ∧
      ((¬ ∃ s : Nat, PairwiseDistinctWindow nums (natOf k) s) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, if m = 1 then r = k * c, and if m > 1 then r = 0.
  Preconditions: 1 <= len(nums) <= 2 * 10^4; 1 <= m <= k <= len(nums); there exists c with 1 <= c <= 10^9 such that nums[i] = c for every 0 <= i < len(nums). -/
theorem spec_16 (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (c : I64) (hc_pos : 1 ≤ c.val) (hc_le : c.val ≤ 10 ^ 9)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = c.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r) :
    (m.val = 1 → r.val = (natOf k : Int) * c.val) ∧ (1 < m.val → r.val = 0) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice I64) (m k : I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 4)
    (hm_pos : 1 ≤ m.val) (hmk : m.val ≤ k.val) (hk_len : k.val ≤ (nums.val.length : Int))
    (c : I64) (hc_pos : 1 ≤ c.val) (hc_le : c.val ≤ 10 ^ 9)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = c.val)
    (r : I64) (hr : Aegis.MaxSum.max_sum nums m k = ok r), (m.val = 1 → r.val = (natOf k : Int) * c.val) ∧ (1 < m.val → r.val = 0)) := by
  sorry

end AegisSpec.MaxSum
