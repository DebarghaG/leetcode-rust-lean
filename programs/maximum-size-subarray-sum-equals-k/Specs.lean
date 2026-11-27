import Aegis.MaxSubArrayLen.Code.Funs

/-!
# Specifications of `Aegis.MaxSubArrayLen.max_sub_array_len`

LeetCode problem `maximum-size-subarray-sum-equals-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSubArrayLen (max_sub_array_len)

namespace AegisSpec.MaxSubArrayLen

def elems (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : Nat := nums.val.length

def get (nums : Slice Std.I64) (i : Nat) : Int := (elems nums).getD i 0

def sum (nums : Slice Std.I64) (a b : Nat) : Int := ((elems nums).drop a).take (b - a) |>.sum

def WindowSum (nums : Slice Std.I64) (k : Std.I64) (a b : Nat) : Prop :=
  a ≤ b ∧ b ≤ len nums ∧ sum nums a b = k.val

def HasWindow (nums : Slice Std.I64) (k : Std.I64) : Prop :=
  ∃ a b, a < b ∧ WindowSum nums k a b

def IsMaxWindowLen (nums : Slice Std.I64) (k : Std.I64) (r : Int) : Prop :=
  (∀ a b, a < b → WindowSum nums k a b → (b - a : Int) ≤ r) ∧
    (r = 0 ∨ ∃ a b, a < b ∧ WindowSum nums k a b ∧ (b - a : Int) = r)

/-- For 0 <= a <= b <= n define sum(a,b) = nums[a] + nums[a+1] + ... + nums[b-1] (the empty sum is 0 when a=b). Whenever the function returns a result r, r is the maximum of the set { b-a | 0 <= a < b <= n and sum(a,b) = k }, with the maximum of the empty set defined to be 0. Equivalently, r is the greatest length of a non-empty contiguous subarray of nums whose elements sum to k, or 0 if no such subarray exists.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r → IsMaxWindowLen nums k r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r → IsMaxWindowLen nums k r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or encounter arithmetic overflow.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ r, max_sub_array_len nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∃ r, max_sub_array_len nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n, where n = len(nums).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r → 0 ≤ r.val ∧ r.val ≤ (len nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r → 0 ≤ r.val ∧ r.val ≤ (len nums : Int)) := by
  sorry

/-- For 0 <= a <= b <= n define sum(a,b) = nums[a] + nums[a+1] + ... + nums[b-1]. Whenever the function returns a result r with r > 0, there exist integers a and b such that 0 <= a < b <= n, b-a = r, and sum(a,b) = k.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r → 0 < r.val →
      ∃ a b, a < b ∧ b ≤ len nums ∧ sum nums a b = k.val ∧ (b - a : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r → 0 < r.val →
      ∃ a b, a < b ∧ b ≤ len nums ∧ sum nums a b = k.val ∧ (b - a : Int) = r.val) := by
  sorry

/-- For 0 <= a <= b <= n define sum(a,b) = nums[a] + nums[a+1] + ... + nums[b-1]. Whenever the function returns a result r, every non-empty subarray whose sum is k has length at most r: for every a,b with 0 <= a < b <= n and sum(a,b) = k, we have b-a <= r.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r →
      ∀ a b, a < b → b ≤ len nums → sum nums a b = k.val → (b - a : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r →
      ∀ a b, a < b → b ≤ len nums → sum nums a b = k.val → (b - a : Int) ≤ r.val) := by
  sorry

/-- For 0 <= a <= b <= n define sum(a,b) = nums[a] + nums[a+1] + ... + nums[b-1]. Whenever the function returns a result r, r = 0 if and only if there are no integers a,b with 0 <= a < b <= n and sum(a,b) = k.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r → (r.val = 0 ↔ ¬ HasWindow nums k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r → (r.val = 0 ↔ ¬ HasWindow nums k)) := by
  sorry

/-- For 0 <= a <= b <= n define sum(a,b) = nums[a] + nums[a+1] + ... + nums[b-1]. Whenever the function returns a result r, r = n if and only if sum(0,n) = k (that is, the sum of the entire array nums equals k).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r →
      (r.val = (len nums : Int) ↔ sum nums 0 (len nums) = k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r →
      (r.val = (len nums : Int) ↔ sum nums 0 (len nums) = k.val)) := by
  sorry

/-- Whenever the function returns a result r and n = 1, r = 1 if nums[0] = k and r = 0 otherwise.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r → len nums = 1 →
      (r.val = 1 ∧ get nums 0 = k.val) ∨ (r.val = 0 ∧ get nums 0 ≠ k.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r → len nums = 1 →
      (r.val = 1 ∧ get nums 0 = k.val) ∨ (r.val = 0 ∧ get nums 0 ≠ k.val)) := by
  sorry

/-- Whenever the function returns a result r, if k = 0 and all elements of nums have the same nonzero sign (either nums[i] > 0 for every 0 <= i < n, or nums[i] < 0 for every 0 <= i < n), then r = 0.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r →
      k.val = 0 →
        ((∀ i, i < len nums → 0 < get nums i) ∨ (∀ i, i < len nums → get nums i < 0)) →
          r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r →
      k.val = 0 →
        ((∀ i, i < len nums → 0 < get nums i) ∨ (∀ i, i < len nums → get nums i < 0)) →
          r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] = 0 for every 0 <= i < n, then r = n when k = 0, and r = 0 when k != 0.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r, max_sub_array_len nums k = ok r →
      (∀ i, i < len nums → get nums i = 0) →
        (k.val = 0 → r.val = (len nums : Int)) ∧ (k.val ≠ 0 → r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r, max_sub_array_len nums k = ok r →
      (∀ i, i < len nums → get nums i = 0) →
        (k.val = 0 → r.val = (len nums : Int)) ∧ (k.val ≠ 0 → r.val = 0)) := by
  sorry

/-- For any slice nums' of length n such that nums'[i] = nums[n-1-i] for every 0 <= i < n (so nums' also satisfies the element bounds), if the function returns r on (nums,k) and returns r' on (nums',k), then r = r'.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ nums', len nums' = len nums →
      (∀ i, i < len nums → get nums' i = get nums (len nums - 1 - i)) →
        ∀ r r', max_sub_array_len nums k = ok r → max_sub_array_len nums' k = ok r' →
          r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ nums', len nums' = len nums →
      (∀ i, i < len nums → get nums' i = get nums (len nums - 1 - i)) →
        ∀ r r', max_sub_array_len nums k = ok r → max_sub_array_len nums' k = ok r' →
          r = r') := by
  sorry

/-- For any slice nums' of length n and integer k' such that nums'[i] = -nums[i] for every 0 <= i < n and k' = -k, if the function returns r on (nums,k) and returns r' on (nums',k'), then r = r'.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; and -1000000000 <= k <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ (nums' : Slice Std.I64) (k' : Std.I64), len nums' = len nums →
      (∀ i, i < len nums → get nums' i = - get nums i) → k'.val = - k.val →
        ∀ r r', max_sub_array_len nums k = ok r → max_sub_array_len nums' k' = ok r' →
          r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len nums) (hn2 : len nums ≤ 200000)
    (hb : ∀ i, i < len nums → -10000 ≤ get nums i ∧ get nums i ≤ 10000)
    (hk : -1000000000 ≤ k.val ∧ k.val ≤ 1000000000), ∀ (nums' : Slice Std.I64) (k' : Std.I64), len nums' = len nums →
      (∀ i, i < len nums → get nums' i = - get nums i) → k'.val = - k.val →
        ∀ r r', max_sub_array_len nums k = ok r → max_sub_array_len nums' k' = ok r' →
          r = r') := by
  sorry

end AegisSpec.MaxSubArrayLen
