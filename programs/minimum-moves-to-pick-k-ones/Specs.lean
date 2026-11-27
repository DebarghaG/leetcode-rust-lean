import Aegis.MinimumMoves.Code.Funs

/-!
# Specifications of `Aegis.MinimumMoves.minimum_moves`

LeetCode problem `minimum-moves-to-pick-k-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumMoves (minimum_moves)

  namespace AegisSpec.MinimumMoves

  def IsBinary (nums : Slice Std.I64) : Prop :=
    ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1

  def sumNums (nums : Slice Std.I64) : Int :=
    (nums.val.map (fun x => x.val)).sum

  def onePositions (nums : Slice Std.I64) : List Nat :=
    (nums.val.zipIdx.filter (fun p => p.1.val = 1)).map (fun p => p.2)

  def multisetAt (nums : Slice Std.I64) (maxChanges : Std.I64) (a : Nat) : List Int :=
    ((onePositions nums).map (fun p => |(p : Int) - (a : Int)|))
      ++ List.replicate maxChanges.val.toNat (2 : Int)

  def sumKSmallest (k : Nat) (l : List Int) : Int :=
    ((l.mergeSort (· ≤ ·)).take k).sum

  def S (nums : Slice Std.I64) (k maxChanges : Std.I64) (a : Nat) : Int :=
    sumKSmallest k.val.toNat (multisetAt nums maxChanges a)

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def costMin (nums : Slice Std.I64) (k maxChanges : Std.I64) : Int :=
    listMin ((List.range nums.val.length).map (fun a => S nums k maxChanges a))

  def costMinOne (nums : Slice Std.I64) (k maxChanges : Std.I64) : Int :=
    listMin ((onePositions nums).map (fun a => S nums k maxChanges a))

  /-- Whenever the function returns a result r, r equals min_{0 <= a < n} S(a), where for each index a, S(a) is defined as follows. Let M(a) be the multiset containing one copy of |p - a| for every p with 0 <= p < n and nums[p] = 1, and containing exactly maxChanges additional copies of the integer 2. Since |M(a)| = sum(nums) + maxChanges >= k, S(a) is the sum of the k smallest elements of M(a), counted with multiplicity.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k, where sum(nums) = sum_{i=0}^{n-1} nums[i]. -/
  theorem spec_1 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
        r.val = costMin nums k maxChanges := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
          r.val = costMin nums k maxChanges) := by
    sorry

  /-- The function returns a result r; it does not fail by out-of-bounds access, panic, or arithmetic overflow. Under these preconditions the value characterized in S1 is between 0 and 10000000000, which fits in Std.I64.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k, where sum(nums) = sum_{i=0}^{n-1} nums[i]. -/
  theorem spec_2 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val) :
      (∃ r : Std.I64, minimum_moves nums k maxChanges = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 10000000000)
        ∧ 0 ≤ costMin nums k maxChanges ∧ costMin nums k maxChanges ≤ 10000000000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val), (∃ r : Std.I64, minimum_moves nums k maxChanges = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 10000000000)
          ∧ 0 ≤ costMin nums k maxChanges ∧ costMin nums k maxChanges ≤ 10000000000) := by
    sorry

  /-- Whenever the function returns a result r, r >= k - 1.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k. -/
  theorem spec_3 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val ≥ k.val - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val ≥ k.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if sum(nums) >= 1, and r = 2 if sum(nums) = 0.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; k = 1; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= 1. -/
  theorem spec_4 (nums : Slice Std.I64) (maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ 1) :
      ∀ r : Std.I64, minimum_moves nums 1#i64 maxChanges = ok r →
        (sumNums nums ≥ 1 → r.val = 0) ∧ (sumNums nums = 0 → r.val = 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ 1), ∀ r : Std.I64, minimum_moves nums 1#i64 maxChanges = ok r →
          (sumNums nums ≥ 1 → r.val = 0) ∧ (sumNums nums = 0 → r.val = 2)) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 * k.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; maxChanges + sum(nums) >= k; and sum(nums) = 0. -/
  theorem spec_5 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val)
      (hzero : sumNums nums = 0) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val = 2 * k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val)
        (hzero : sumNums nums = 0), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val = 2 * k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if k = 1 and sum(nums) >= 1.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k. -/
  theorem spec_6 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
        (r.val = 0 ↔ k.val = 1 ∧ sumNums nums ≥ 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
          (r.val = 0 ↔ k.val = 1 ∧ sumNums nums ≥ 1)) := by
    sorry

  /-- Whenever the function returns r1 on input (nums, k1, maxChanges) and returns r2 on input (nums, k2, maxChanges), r2 >= r1 + (k2 - k1).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 0 <= maxChanges <= 100000; and 1 <= k1 < k2 <= 100000 with maxChanges + sum(nums) >= k2. -/
  theorem spec_7 (nums : Slice Std.I64) (k1 k2 maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val < k2.val) (hk2 : k2.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k2.val) :
      ∀ r1 r2 : Std.I64,
        minimum_moves nums k1 maxChanges = ok r1 →
        minimum_moves nums k2 maxChanges = ok r2 →
        r2.val ≥ r1.val + (k2.val - k1.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val < k2.val) (hk2 : k2.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k2.val), ∀ r1 r2 : Std.I64,
          minimum_moves nums k1 maxChanges = ok r1 →
          minimum_moves nums k2 maxChanges = ok r2 →
          r2.val ≥ r1.val + (k2.val - k1.val)) := by
    sorry

  /-- Whenever the function returns r1 on input (nums, k, c1) and returns r2 on input (nums, k, c2), r2 <= r1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; and 0 <= c1 <= c2 <= 100000 with c1 + sum(nums) >= k. -/
  theorem spec_8 (nums : Slice Std.I64) (k c1 c2 : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc1 : 0 ≤ c1.val) (hc12 : c1.val ≤ c2.val) (hc2 : c2.val ≤ 100000)
      (hsum : c1.val + sumNums nums ≥ k.val) :
      ∀ r1 r2 : Std.I64,
        minimum_moves nums k c1 = ok r1 →
        minimum_moves nums k c2 = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k c1 c2 : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc1 : 0 ≤ c1.val) (hc12 : c1.val ≤ c2.val) (hc2 : c2.val ≤ 100000)
        (hsum : c1.val + sumNums nums ≥ k.val), ∀ r1 r2 : Std.I64,
          minimum_moves nums k c1 = ok r1 →
          minimum_moves nums k c2 = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns r on input (nums, k, maxChanges) and returns r2 on input (nums2, k, maxChanges), r2 <= r.
    Preconditions: Let n = len(nums). Let nums2 be a binary array of length n with nums[i] <= nums2[i] for every 0 <= i < n. Assume 2 <= n <= 100000; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums) (hbin2 : IsBinary nums2)
      (hlen2 : nums2.val.length = nums.val.length)
      (hle : List.Forall₂ (fun a b => a.val ≤ b.val) nums.val nums2.val)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val) :
      ∀ r r2 : Std.I64,
        minimum_moves nums k maxChanges = ok r →
        minimum_moves nums2 k maxChanges = ok r2 →
        r2.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums) (hbin2 : IsBinary nums2)
        (hlen2 : nums2.val.length = nums.val.length)
        (hle : List.Forall₂ (fun a b => a.val ≤ b.val) nums.val nums2.val)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val), ∀ r r2 : Std.I64,
          minimum_moves nums k maxChanges = ok r →
          minimum_moves nums2 k maxChanges = ok r2 →
          r2.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns r on input (nums, k, maxChanges) and returns r_rev on input (rev, k, maxChanges), r = r_rev.
    Preconditions: Let n = len(nums). Let rev be the length-n array with rev[i] = nums[n-1-i] for every 0 <= i < n. Assume 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; and maxChanges + sum(nums) >= k. -/
  theorem spec_10 (nums rev : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val)
      (hrev : rev.val = nums.val.reverse) :
      ∀ r rrev : Std.I64,
        minimum_moves nums k maxChanges = ok r →
        minimum_moves rev k maxChanges = ok rrev →
        r.val = rrev.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val)
        (hrev : rev.val = nums.val.reverse), ∀ r rrev : Std.I64,
          minimum_moves nums k maxChanges = ok r →
          minimum_moves rev k maxChanges = ok rrev →
          r.val = rrev.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min_{0 <= a < n and nums[a]=1} S(a), where S(a) is defined as in spec_1: the multiset has one copy of |p-a| for each original 1 position p and maxChanges copies of 2, and S(a) is the sum of its k smallest elements.
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; maxChanges + sum(nums) >= k; and sum(nums) >= 1. -/
  theorem spec_11 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val)
      (hpos : sumNums nums ≥ 1) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
        r.val = costMinOne nums k maxChanges := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val)
        (hpos : sumNums nums ≥ 1), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r →
          r.val = costMinOne nums k maxChanges) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 * (k - 1).
    Preconditions: Let n = len(nums). The following hold: 2 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; maxChanges + sum(nums) >= k; and sum(nums) >= 1 and maxChanges >= k - 1. -/
  theorem spec_12 (nums : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val)
      (hpos : sumNums nums ≥ 1) (henough : maxChanges.val ≥ k.val - 1) :
      ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val ≤ 2 * (k.val - 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val)
        (hpos : sumNums nums ≥ 1) (henough : maxChanges.val ≥ k.val - 1), ∀ r : Std.I64, minimum_moves nums k maxChanges = ok r → r.val ≤ 2 * (k.val - 1)) := by
    sorry

  /-- Whenever the function returns r on input (nums, k, maxChanges) and returns r2 on input (nums2, k, maxChanges), r = r2.
    Preconditions: Let n = len(nums). Assume 3 <= n <= 100000; nums[i] is 0 or 1 for every 0 <= i < n; 1 <= k <= 100000; 0 <= maxChanges <= 100000; maxChanges + sum(nums) >= k; and nums[0] = 0. Let nums2 be the length n-1 array with nums2[i] = nums[i+1] for every 0 <= i < n-1. -/
  theorem spec_13 (nums nums2 : Slice Std.I64) (k maxChanges : Std.I64)
      (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbin : IsBinary nums)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
      (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
      (hsum : maxChanges.val + sumNums nums ≥ k.val)
      (h0 : nums.val[0]? = some (0#i64))
      (hnums2 : nums2.val = nums.val.tail) :
      ∀ r r2 : Std.I64,
        minimum_moves nums k maxChanges = ok r →
        minimum_moves nums2 k maxChanges = ok r2 →
        r.val = r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k maxChanges : Std.I64)
        (hlen : 3 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbin : IsBinary nums)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000)
        (hc : 0 ≤ maxChanges.val) (hc' : maxChanges.val ≤ 100000)
        (hsum : maxChanges.val + sumNums nums ≥ k.val)
        (h0 : nums.val[0]? = some (0#i64))
        (hnums2 : nums2.val = nums.val.tail), ∀ r r2 : Std.I64,
          minimum_moves nums k maxChanges = ok r →
          minimum_moves nums2 k maxChanges = ok r2 →
          r.val = r2.val) := by
    sorry

  end AegisSpec.MinimumMoves
