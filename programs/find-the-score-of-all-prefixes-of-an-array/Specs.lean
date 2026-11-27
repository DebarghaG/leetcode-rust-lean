import Aegis.FindPrefixScore.Code.Funs

/-!
# Specifications of `Aegis.FindPrefixScore.find_prefix_score`

LeetCode problem `find-the-score-of-all-prefixes-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindPrefixScore

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def getAt (l : List Int) (i : Nat) : Int := l.getD i 0

  def prefixSum (l : List Int) (i : Nat) : Int := (l.take (i + 1)).sum

  def prefixMax (l : List Int) (i : Nat) : Int :=
    match l.take (i + 1) with
    | [] => 0
    | x :: xs => xs.foldl (fun a b => max a b) x

  def prefixScore (l : List Int) (i : Nat) : Int :=
    ((List.range (i + 1)).map (fun k => getAt l k + prefixMax l k)).sum

  def Nondecreasing (l : List Int) : Prop :=
    ∀ j, ∀ (h1 : 1 ≤ j) (h2 : j < l.length),
      l[j - 1]'(by omega) ≤ l[j]'(by omega)

  /-- The function returns a result r and len(r) = n. For every i with 0 <= i < n, let M_i = max(nums[0], nums[1], ..., nums[i]); then r[i] = sum_{k=0}^{i} (nums[k] + M_k). In words, r[i] is the score of the prefix nums[0..i]: the sum over k <= i of nums[k] plus the maximum of nums[0..k].
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.FindPrefixScore.find_prefix_score nums = ok r ∧ r.val.length = n ∧
          ∀ i (hi : i < r.val.length), (r.val[i]'hi).val = prefixScore (vals nums) i := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.FindPrefixScore.find_prefix_score nums = ok r ∧ r.val.length = n ∧
            ∀ i (hi : i < r.val.length), (r.val[i]'hi).val = prefixScore (vals nums) i) := by
    sorry

  /-- The function returns a result r; it does not fail with overflow, out-of-bounds, or panic on any input satisfying the preconditions.
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPrefixScore.find_prefix_score nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, Aegis.FindPrefixScore.find_prefix_score nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] >= 2 * sum_{k=0}^{i} nums[k].
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi : i < n), 2 * prefixSum (vals nums) i ≤ (r.val[i]'(by omega)).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi : i < n), 2 * prefixSum (vals nums) i ≤ (r.val[i]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, letting M_i = max(nums[0], ..., nums[i]), r[i] <= 2 * (i + 1) * M_i.
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi : i < n),
        (r.val[i]'(by omega)).val ≤ 2 * ((i : Int) + 1) * prefixMax (vals nums) i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi : i < n),
          (r.val[i]'(by omega)).val ≤ 2 * ((i : Int) + 1) * prefixMax (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n, letting M_i = max(nums[0], ..., nums[i]), r[i] = r[i-1] + nums[i] + M_i.
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi1 : 1 ≤ i) (hi2 : i < n),
        (r.val[i]'(by omega)).val =
          (r.val[i - 1]'(by omega)).val + (nums.val[i]'(by omega)).val
            + prefixMax (vals nums) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi1 : 1 ≤ i) (hi2 : i < n),
          (r.val[i]'(by omega)).val =
            (r.val[i - 1]'(by omega)).val + (nums.val[i]'(by omega)).val
              + prefixMax (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n, r[i] >= r[i-1] + 2.
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi1 : 1 ≤ i) (hi2 : i < n),
        (r.val[i - 1]'(by omega)).val + 2 ≤ (r.val[i]'(by omega)).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi1 : 1 ≤ i) (hi2 : i < n),
          (r.val[i - 1]'(by omega)).val + 2 ≤ (r.val[i]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r and nums is nondecreasing (nums[j-1] <= nums[j] for every 1 <= j < n), for every i with 0 <= i < n, r[i] = 2 * sum_{k=0}^{i} nums[k].
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (hnd : Nondecreasing (vals nums))
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi : i < n), (r.val[i]'(by omega)).val = 2 * prefixSum (vals nums) i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (hnd : Nondecreasing (vals nums))
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi : i < n), (r.val[i]'(by omega)).val = 2 * prefixSum (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if nums[0] is a maximum of the prefix nums[0..i] (that is, nums[j] <= nums[0] for every 0 <= j <= i), then r[i] = (i + 1) * nums[0] + sum_{k=0}^{i} nums[k].
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi : i < n),
        (∀ j (hj : j ≤ i), (nums.val[j]'(by omega)).val ≤ (nums.val[0]'(by omega)).val) →
          (r.val[i]'(by omega)).val =
            ((i : Int) + 1) * (nums.val[0]'(by omega)).val + prefixSum (vals nums) i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi : i < n),
          (∀ j (hj : j ≤ i), (nums.val[j]'(by omega)).val ≤ (nums.val[0]'(by omega)).val) →
            (r.val[i]'(by omega)).val =
              ((i : Int) + 1) * (nums.val[0]'(by omega)).val + prefixSum (vals nums) i) := by
    sorry

  /-- For every i with 0 <= i < n and every array nums2 of length n2 with i < n2 <= 100000 and 1 <= nums2[j] <= 1000000000 for all 0 <= j < n2, if nums2[j] = nums[j] for every 0 <= j <= i, then whenever the call on nums returns r and the call on nums2 returns r2, r[i] = r2[i].
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (nums2 : Slice Std.I64) (n2 : Nat)
      (hn2' : nums2.val.length = n2) (hn2a : n2 ≤ 100000)
      (hlo2 : ∀ j (hj : j < n2), 1 ≤ (nums2.val[j]'(by omega)).val)
      (hhi2 : ∀ j (hj : j < n2), (nums2.val[j]'(by omega)).val ≤ 1000000000)
      (i : Nat) (hi : i < n) (hi2 : i < n2)
      (hagree : ∀ j (hj : j ≤ i), (nums2.val[j]'(by omega)).val = (nums.val[j]'(by omega)).val)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n)
      (r2 : alloc.vec.Vec Std.I64) (hr2 : Aegis.FindPrefixScore.find_prefix_score nums2 = ok r2)
      (hlen2 : r2.val.length = n2) :
      (r.val[i]'(by omega)).val = (r2.val[i]'(by omega)).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (nums2 : Slice Std.I64) (n2 : Nat)
        (hn2' : nums2.val.length = n2) (hn2a : n2 ≤ 100000)
        (hlo2 : ∀ j (hj : j < n2), 1 ≤ (nums2.val[j]'(by omega)).val)
        (hhi2 : ∀ j (hj : j < n2), (nums2.val[j]'(by omega)).val ≤ 1000000000)
        (i : Nat) (hi : i < n) (hi2 : i < n2)
        (hagree : ∀ j (hj : j ≤ i), (nums2.val[j]'(by omega)).val = (nums.val[j]'(by omega)).val)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n)
        (r2 : alloc.vec.Vec Std.I64) (hr2 : Aegis.FindPrefixScore.find_prefix_score nums2 = ok r2)
        (hlen2 : r2.val.length = n2), (r.val[i]'(by omega)).val = (r2.val[i]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n there exist indices p_0, p_1, ..., p_i such that 0 <= p_k <= k for every 0 <= k <= i, nums[p_k] = max(nums[0], ..., nums[k]), and r[i] = sum_{k=0}^{i} (nums[k] + nums[p_k]).
    Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
      (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
      (hlen : r.val.length = n) :
      ∀ i (hi : i < n), ∃ p : Nat → Nat,
        (∀ k (hk : k ≤ i), p k ≤ k) ∧
        (∀ k (hk : k ≤ i), getAt (vals nums) (p k) = prefixMax (vals nums) k) ∧
        (r.val[i]'(by omega)).val =
          ((List.range (i + 1)).map (fun k => getAt (vals nums) k + getAt (vals nums) (p k))).sum := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hlo : ∀ i (hi : i < n), 1 ≤ (nums.val[i]'(by omega)).val)
        (hhi : ∀ i (hi : i < n), (nums.val[i]'(by omega)).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.FindPrefixScore.find_prefix_score nums = ok r)
        (hlen : r.val.length = n), ∀ i (hi : i < n), ∃ p : Nat → Nat,
          (∀ k (hk : k ≤ i), p k ≤ k) ∧
          (∀ k (hk : k ≤ i), getAt (vals nums) (p k) = prefixMax (vals nums) k) ∧
          (r.val[i]'(by omega)).val =
            ((List.range (i + 1)).map (fun k => getAt (vals nums) k + getAt (vals nums) (p k))).sum) := by
    sorry

  end AegisSpec.FindPrefixScore
