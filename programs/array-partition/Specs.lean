import Aegis.ArrayPairSum.Code.Funs

/-!
# Specifications of `Aegis.ArrayPairSum.array_pair_sum`

LeetCode problem `array-partition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ArrayPairSum

def sliceVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def valAt (nums : Slice Std.I64) (i : Nat) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def IsNondecreasingRearrange (nums : Slice Std.I64) (b : List ℤ) : Prop :=
  b.Pairwise (· ≤ ·) ∧ b.Perm (sliceVals nums)

def IsPerfectPairing (len : Nat) (P : List (Nat × Nat)) : Prop :=
  (∀ p ∈ P, p.1 < p.2 ∧ p.2 < len) ∧
    P.length = len / 2 ∧
      ∀ i, i < len → ∃! p, p ∈ P ∧ (p.1 = i ∨ p.2 = i)

def pairingSum (nums : Slice Std.I64) (P : List (Nat × Nat)) : ℤ :=
  (P.map (fun p => min (valAt nums p.1) (valAt nums p.2))).sum

def evenIndexSum : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | a :: _ :: rest => a + evenIndexSum rest

/-- The function returns a result r (it does not fail), and r is the maximum, over all perfect pairings P of the index set {0,1,...,len(nums)-1}, of the sum over {i,j} in P of min(nums[i], nums[j]). A perfect pairing is a set of n unordered pairs {i,j} with i < j such that every index in {0,...,len(nums)-1} occurs in exactly one pair.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000) :
    ∃ r : Std.I64, Aegis.ArrayPairSum.array_pair_sum nums = ok r ∧
      (∀ P : List (Nat × Nat), IsPerfectPairing nums.val.length P → pairingSum nums P ≤ r.val) ∧
        ∃ P : List (Nat × Nat), IsPerfectPairing nums.val.length P ∧ pairingSum nums P = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000), ∃ r : Std.I64, Aegis.ArrayPairSum.array_pair_sum nums = ok r ∧
      (∀ P : List (Nat × Nat), IsPerfectPairing nums.val.length P → pairingSum nums P ≤ r.val) ∧
        ∃ P : List (Nat × Nat), IsPerfectPairing nums.val.length P ∧ pairingSum nums P = r.val) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000) :
    ∃ r : Std.I64, Aegis.ArrayPairSum.array_pair_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000), ∃ r : Std.I64, Aegis.ArrayPairSum.array_pair_sum nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, if b[0] <= b[1] <= ... <= b[len(nums)-1] is a nondecreasing rearrangement of the entries of nums, then sum_{k=0}^{n-1} b[k] <= r <= sum_{k=n}^{2*n-1} b[k].
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (b : List ℤ) (hb : IsNondecreasingRearrange nums b) :
    (b.take n).sum ≤ r.val ∧ r.val ≤ (b.drop n).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (b : List ℤ) (hb : IsNondecreasingRearrange nums b), (b.take n).sum ≤ r.val ∧ r.val ≤ (b.drop n).sum) := by
  sorry

/-- Whenever the function returns a result r, 2*r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    2 * r.val ≤ (sliceVals nums).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), 2 * r.val ≤ (sliceVals nums).sum) := by
  sorry

/-- Whenever the function returns a result r, there exists a perfect pairing P of the index set {0,1,...,len(nums)-1} such that r = sum over {i,j} in P of min(nums[i], nums[j]).
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    ∃ P : List (Nat × Nat), IsPerfectPairing nums.val.length P ∧ pairingSum nums P = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), ∃ P : List (Nat × Nat), IsPerfectPairing nums.val.length P ∧ pairingSum nums P = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every perfect pairing P of the index set {0,1,...,len(nums)-1}, sum over {i,j} in P of min(nums[i], nums[j]) <= r.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    ∀ P : List (Nat × Nat), IsPerfectPairing nums.val.length P → pairingSum nums P ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), ∀ P : List (Nat × Nat), IsPerfectPairing nums.val.length P → pairingSum nums P ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if b[0] <= b[1] <= ... <= b[len(nums)-1] is a nondecreasing rearrangement of the entries of nums, then r = sum_{k=0}^{n-1} b[2*k].
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (b : List ℤ) (hb : IsNondecreasingRearrange nums b) :
    r.val = evenIndexSum b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (b : List ℤ) (hb : IsNondecreasingRearrange nums b), r.val = evenIndexSum b) := by
  sorry

/-- Whenever the function returns a result r for nums, for every permutation pi of the index set {0,1,...,len(nums)-1}, if nums_pi is the slice defined by nums_pi[i] = nums[pi(i)] for 0 <= i < len(nums), and the call on nums_pi returns r_pi, then r_pi = r.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums nums_pi : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (pi : Equiv.Perm (Fin nums.val.length))
    (hlen_pi : nums_pi.val.length = nums.val.length)
    (hpi : ∀ i : Fin nums.val.length, valAt nums_pi i.val = valAt nums (pi i).val)
    (r_pi : Std.I64) (hr_pi : Aegis.ArrayPairSum.array_pair_sum nums_pi = ok r_pi) :
    r_pi = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums_pi : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (pi : Equiv.Perm (Fin nums.val.length))
    (hlen_pi : nums_pi.val.length = nums.val.length)
    (hpi : ∀ i : Fin nums.val.length, valAt nums_pi i.val = valAt nums (pi i).val)
    (r_pi : Std.I64) (hr_pi : Aegis.ArrayPairSum.array_pair_sum nums_pi = ok r_pi), r_pi = r) := by
  sorry

/-- Whenever the function returns r for nums and also returns r_c for the slice nums_c defined by nums_c[i] = nums[i] + c, we have r_c = r + n*c.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, -10000 <= nums[i] <= 10000 for every i, and c is an integer such that -10000 <= nums[i] + c <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums nums_c : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (c : ℤ)
    (hcrange : ∀ i, i < nums.val.length →
      -10000 ≤ valAt nums i + c ∧ valAt nums i + c ≤ 10000)
    (hlen_c : nums_c.val.length = nums.val.length)
    (hc : ∀ i, i < nums.val.length → valAt nums_c i = valAt nums i + c)
    (r r_c : Std.I64)
    (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (hr_c : Aegis.ArrayPairSum.array_pair_sum nums_c = ok r_c) :
    r_c.val = r.val + (n : ℤ) * c := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums_c : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (c : ℤ)
    (hcrange : ∀ i, i < nums.val.length →
      -10000 ≤ valAt nums i + c ∧ valAt nums i + c ≤ 10000)
    (hlen_c : nums_c.val.length = nums.val.length)
    (hc : ∀ i, i < nums.val.length → valAt nums_c i = valAt nums i + c)
    (r r_c : Std.I64)
    (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (hr_c : Aegis.ArrayPairSum.array_pair_sum nums_c = ok r_c), r_c.val = r.val + (n : ℤ) * c) := by
  sorry

/-- Whenever the function returns r for nums and r2 for nums2, we have r <= r2.
  Preconditions: Let n = len(nums)/2 = len(nums2)/2. Both nums and nums2 satisfy 1 <= n <= 10000, len(nums) = len(nums2) = 2*n, and all their entries are in [-10000, 10000]. Also nums[i] <= nums2[i] for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums nums2 : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hn2 : n = nums2.val.length / 2)
    (hlen : nums.val.length = 2 * n) (hlen2 : nums2.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hnmax : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (hrange2 : ∀ i, i < nums2.val.length → -10000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000)
    (hle : ∀ i, i < nums.val.length → valAt nums i ≤ valAt nums2 i)
    (r r2 : Std.I64)
    (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (hr2 : Aegis.ArrayPairSum.array_pair_sum nums2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hn2 : n = nums2.val.length / 2)
    (hlen : nums.val.length = 2 * n) (hlen2 : nums2.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hnmax : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (hrange2 : ∀ i, i < nums2.val.length → -10000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000)
    (hle : ∀ i, i < nums.val.length → valAt nums i ≤ valAt nums2 i)
    (r r2 : Std.I64)
    (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r)
    (hr2 : Aegis.ArrayPairSum.array_pair_sum nums2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, r = min(nums[0], nums[1]).
  Preconditions: n = 1, len(nums)=2, and -10000 <= nums[0], nums[1] <= 10000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hrange : -10000 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000 ∧
      -10000 ≤ valAt nums 1 ∧ valAt nums 1 ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    r.val = min (valAt nums 0) (valAt nums 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hrange : -10000 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000 ∧
      -10000 ≤ valAt nums 1 ∧ valAt nums 1 ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), r.val = min (valAt nums 0) (valAt nums 1)) := by
  sorry

/-- Whenever the function returns a result r, r = n*c.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and there is an integer c with -10000 <= c <= 10000 such that nums[i] = c for every i with 0 <= i < len(nums). -/
theorem spec_12 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (c : ℤ) (hc1 : -10000 ≤ c) (hc2 : c ≤ 10000)
    (hconst : ∀ i, i < nums.val.length → valAt nums i = c)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    r.val = (n : ℤ) * c := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (c : ℤ) (hc1 : -10000 ≤ c) (hc2 : c ≤ 10000)
    (hconst : ∀ i, i < nums.val.length → valAt nums i = c)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), r.val = (n : ℤ) * c) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and 0 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_13 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → 0 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 0.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 0 for every i with 0 <= i < len(nums). -/
theorem spec_14 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 0)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    r.val ≤ 0 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 0)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), r.val ≤ 0) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset S of {0,1,...,len(nums)-1} with exactly n elements such that sum_{i in S} nums[i] = r.
  Preconditions: Let n = len(nums)/2. We require 1 <= n <= 10000, len(nums) = 2*n, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_15 (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r) :
    ∃ S : Finset (Fin nums.val.length), S.card = n ∧ S.sum (fun i => valAt nums i.val) = r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = nums.val.length / 2) (hlen : nums.val.length = 2 * n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
    (hrange : ∀ i, i < nums.val.length → -10000 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
    (r : Std.I64) (hr : Aegis.ArrayPairSum.array_pair_sum nums = ok r), ∃ S : Finset (Fin nums.val.length), S.card = n ∧ S.sum (fun i => valAt nums i.val) = r.val) := by
  sorry

end AegisSpec.ArrayPairSum
