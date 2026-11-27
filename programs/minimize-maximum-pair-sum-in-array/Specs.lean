import Aegis.MinPairSum.Code.Funs

/-!
# Specifications of `Aegis.MinPairSum.min_pair_sum`

LeetCode problem `minimize-maximum-pair-sum-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option maxHeartbeats 1000000

namespace AegisSpec.MinPairSum

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def ValidInput (nums : Slice Std.I64) : Prop :=
  let l := vals nums
  l.length % 2 = 0 ∧ 2 ≤ l.length ∧ l.length ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < l.length), 1 ≤ l.get ⟨i, hi⟩ ∧ l.get ⟨i, hi⟩ ≤ 100000

def IsPerfectPairing {n : ℕ} (pair : Fin n → Fin n) : Prop :=
  Function.Involutive pair ∧ ∀ i, pair i ≠ i

def AdmitsPairingAtMost (l : List Int) (M : Int) : Prop :=
  ∃ pair : Fin l.length → Fin l.length,
    IsPerfectPairing pair ∧ ∀ i : Fin l.length, l.get i + l.get (pair i) ≤ M

def IsMinMaxPairSum (l : List Int) (r : Int) : Prop :=
  AdmitsPairingAtMost l r ∧ ∀ M, AdmitsPairingAtMost l M → r ≤ M

def maxElem : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr max x

def minElem : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr min x

def total (l : List Int) : Int := l.foldr (· + ·) 0

def ceilDiv (T : Int) (k : ℕ) : Int := -Int.fdiv (-T) (k : Int)

def IsNonincreasingRearrangement (l b : List Int) : Prop :=
  b.Perm l ∧ b.Pairwise (fun x y => y ≤ x)

def IsNondecreasingRearrangement (l a : List Int) : Prop :=
  a.Perm l ∧ a.Pairwise (fun x y => x ≤ y)

def topTwoSum : List Int → Int
  | x :: y :: _ => x + y
  | _ => 0

def halfPairMax (a : List Int) : Int :=
  ((List.range (a.length / 2)).map
    (fun i => a.getD i 0 + a.getD (a.length - 1 - i) 0)).foldr max 0

/-- Whenever min_pair_sum nums returns a result r, r equals the minimized maximum pair sum of nums. Precisely, a perfect pairing of nums is a partition of the index set {0, ..., len(nums)-1} into len(nums)/2 unordered pairs {i,j} of distinct indices; the maximum pair sum of such a pairing is the largest value nums[i]+nums[j] over its pairs; and r is the least integer M for which there exists a perfect pairing of nums all of whose pair sums are <= M.
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    IsMinMaxPairSum (vals nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), IsMinMaxPairSum (vals nums) r.val) := by
  sorry

/-- For every nums satisfying the preconditions, min_pair_sum nums returns a result (it does not fail, overflow, or panic).
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∃ r : Std.I64, Aegis.MinPairSum.min_pair_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Std.I64, Aegis.MinPairSum.min_pair_sum nums = ok r) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r, r >= L + S, where L is the largest element of nums and S is the smallest element of nums.
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    maxElem (vals nums) + minElem (vals nums) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), maxElem (vals nums) + minElem (vals nums) ≤ r.val) := by
  sorry

/-- Let b0 >= b1 >= ... >= b_{len(nums)-1} be a nonincreasing rearrangement of nums, with duplicates counted separately. Whenever min_pair_sum nums returns a result r, r <= b0 + b1.
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (h : ValidInput nums) (b : List Int)
    (hb : IsNonincreasingRearrangement (vals nums) b) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    r.val ≤ topTwoSum b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (b : List Int)
    (hb : IsNonincreasingRearrangement (vals nums) b) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), r.val ≤ topTwoSum b) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r, r >= ceil(T / (len(nums)/2)), where T = sum_{i=0}^{len(nums)-1} nums[i] and ceil(x) is the least integer greater than or equal to x.
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    ceilDiv (total (vals nums)) ((vals nums).length / 2) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), ceilDiv (total (vals nums)) ((vals nums).length / 2) ≤ r.val) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r, there exists a perfect pairing P of nums, where a perfect pairing is a partition of {0, ..., len(nums)-1} into len(nums)/2 unordered pairs of distinct indices, such that every pair {i,j} in P satisfies nums[i]+nums[j] <= r, and at least one pair {i,j} in P satisfies nums[i]+nums[j] = r.
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    ∃ pair : Fin (vals nums).length → Fin (vals nums).length,
      IsPerfectPairing pair ∧
        (∀ i : Fin (vals nums).length, (vals nums).get i + (vals nums).get (pair i) ≤ r.val) ∧
        (∃ i : Fin (vals nums).length, (vals nums).get i + (vals nums).get (pair i) = r.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), ∃ pair : Fin (vals nums).length → Fin (vals nums).length,
      IsPerfectPairing pair ∧
        (∀ i : Fin (vals nums).length, (vals nums).get i + (vals nums).get (pair i) ≤ r.val) ∧
        (∃ i : Fin (vals nums).length, (vals nums).get i + (vals nums).get (pair i) = r.val)) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r and min_pair_sum nums' returns a result r', we have r' = r.
  Preconditions: nums and nums' are slices of 64-bit integers; both satisfy the problem constraints (even length between 2 and 100000 and all entries between 1 and 100000); len(nums') = len(nums); and there is a bijection sigma on {0, ..., len(nums)-1} such that nums'[i] = nums[sigma(i)] for every i. -/
theorem spec_7 (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hbij : ∃ σ : Equiv.Perm (Fin (vals nums).length),
      vals nums' = (List.finRange (vals nums).length).map (fun i => (vals nums).get (σ i)))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hbij : ∃ σ : Equiv.Perm (Fin (vals nums).length),
      vals nums' = (List.finRange (vals nums).length).map (fun i => (vals nums).get (σ i)))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r and min_pair_sum nums' returns a result r', we have r' = r + 2*c.
  Preconditions: nums and nums' are slices of 64-bit integers; both satisfy the problem constraints (even length between 2 and 100000 and all entries between 1 and 100000); len(nums') = len(nums); and there is an integer c such that nums'[i] = nums[i] + c for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length) (c : Int)
    (hc : vals nums' = (vals nums).map (fun x => x + c))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r') :
    r'.val = r.val + 2 * c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length) (c : Int)
    (hc : vals nums' = (vals nums).map (fun x => x + c))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r'), r'.val = r.val + 2 * c) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r and min_pair_sum nums' returns a result r', we have r' = k*r.
  Preconditions: nums and nums' are slices of 64-bit integers; both satisfy the problem constraints (even length between 2 and 100000 and all entries between 1 and 100000); len(nums') = len(nums); and there is a positive integer k such that nums'[i] = k*nums[i] for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length) (k : ℕ) (hk : 0 < k)
    (hmul : vals nums' = (vals nums).map (fun x => (k : Int) * x))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r') :
    r'.val = (k : Int) * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length) (k : ℕ) (hk : 0 < k)
    (hmul : vals nums' = (vals nums).map (fun x => (k : Int) * x))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r'), r'.val = (k : Int) * r.val) := by
  sorry

/-- Whenever min_pair_sum nums returns a result r and min_pair_sum nums' returns a result r', we have r' >= r.
  Preconditions: nums and nums' are slices of 64-bit integers; both satisfy the problem constraints (even length between 2 and 100000 and all entries between 1 and 100000); len(nums') = len(nums); and for every i with 0 <= i < len(nums), nums'[i] >= nums[i]. -/
theorem spec_10 (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hle : List.Forall₂ (fun x y => x ≤ y) (vals nums) (vals nums'))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hle : List.Forall₂ (fun x y => x ≤ y) (vals nums) (vals nums'))
    (r r' : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r)
    (hres' : Aegis.MinPairSum.min_pair_sum nums' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let a0 <= a1 <= ... <= a_{len(nums)-1} be a nondecreasing rearrangement of nums, with duplicates counted separately. Whenever min_pair_sum nums returns a result r, r = max_{0 <= i < len(nums)/2} (a_i + a_{len(nums)-1-i}).
  Preconditions: nums is a slice of 64-bit integers; len(nums) is even; 2 <= len(nums) <= 100000; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64) (h : ValidInput nums) (a : List Int)
    (ha : IsNondecreasingRearrangement (vals nums) a) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r) :
    r.val = halfPairMax a := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (a : List Int)
    (ha : IsNondecreasingRearrangement (vals nums) a) (r : Std.I64)
    (hres : Aegis.MinPairSum.min_pair_sum nums = ok r), r.val = halfPairMax a) := by
  sorry

end AegisSpec.MinPairSum
