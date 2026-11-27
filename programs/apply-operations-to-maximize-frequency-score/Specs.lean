import Aegis.MaxFrequencyScore.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequencyScore.max_frequency_score`

LeetCode problem `apply-operations-to-maximize-frequency-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxFrequencyScore

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def IsSortedVersion (sorted : List ℤ) (l : List ℤ) : Prop :=
    sorted.Pairwise (· ≤ ·) ∧ sorted.Perm l

  def occ (l : List ℤ) (v : ℤ) : ℕ := (l.filter fun x => x = v).length

  def maxOcc (l : List ℤ) : ℕ := (l.map fun v => occ l v).foldr max 0

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def totalCost (l : List ℤ) (t : ℤ) : ℤ := (l.map (fun x => |x - t|)).sum

  def windowCost (a : List ℤ) (s m : ℕ) (t : ℤ) : ℤ :=
    (((a.drop s).take m).map (fun x => |x - t|)).sum

  def Feasible (l : List ℤ) (m : ℕ) (k : ℤ) : Prop :=
    ∃ t : ℤ, ∃ S : Finset (Fin l.length), S.card = m ∧ S.sum (fun i => |l.get i - t|) ≤ k

  def WindowFeasible (a : List ℤ) (m : ℤ) (k : ℤ) : Prop :=
    ∃ s : ℕ, (s : ℤ) + m ≤ (a.length : ℤ) ∧ ∃ t : ℤ, windowCost a s m.toNat t ≤ k

  /-- Whenever max_frequency_score(nums, k) returns a result r, r is an integer satisfying: for every integer m >= 1, m <= r if and only if there exist an integer t and a set S of m distinct indices with 0 <= i < len(nums) such that the sum over i in S of |nums[i] - t| is at most k. Equivalently, r is the largest size of a subset of indices that can all be changed to one common integer value using at most k unit changes in total.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      ∀ m : ℕ, 1 ≤ m → ((m : ℤ) ≤ r.val ↔ Feasible (vals nums) m k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), ∀ m : ℕ, 1 ≤ m → ((m : ℤ) ≤ r.val ↔ Feasible (vals nums) m k.val)) := by
    sorry

  /-- max_frequency_score(nums, k) returns a result r (it does not fail by panic, out-of-bounds access, or arithmetic overflow) for every nums and k satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000) :
      ∃ r : I64, Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000), ∃ r : I64, Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, 1 <= r <= len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, r is at least the maximum, over all integers v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      (maxOcc (vals nums) : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), (maxOcc (vals nums) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever max_frequency_score(nums, 0) returns a result r, r equals the maximum, over all integers v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k = 0. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : k.val = 0)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      r.val = (maxOcc (vals nums) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : k.val = 0)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), r.val = (maxOcc (vals nums) : ℤ)) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, r = len(nums) if and only if there exists an integer t such that the sum over i from 0 to len(nums)-1 of |nums[i] - t| is at most k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      r.val = (nums.val.length : ℤ) ↔ ∃ t : ℤ, totalCost (vals nums) t ≤ k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), r.val = (nums.val.length : ℤ) ↔ ∃ t : ℤ, totalCost (vals nums) t ≤ k.val) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, r = 1 if and only if for every two distinct indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), |nums[i] - nums[j]| > k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      r.val = 1 ↔ ∀ i j : Fin (vals nums).length, i ≠ j →
        k.val < |(vals nums).get i - (vals nums).get j| := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), r.val = 1 ↔ ∀ i j : Fin (vals nums).length, i ≠ j →
          k.val < |(vals nums).get i - (vals nums).get j|) := by
    sorry

  /-- Whenever max_frequency_score(nums, k1) returns r1 and max_frequency_score(nums, k2) returns r2, r1 <= r2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k1 <= k2 <= 100000000000000. -/
  theorem spec_8 (nums : Slice I64) (k1 k2 : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk1 : 0 ≤ k1.val) (hle : k1.val ≤ k2.val) (hk2max : k2.val ≤ 100000000000000)
      (r1 r2 : I64)
      (hr1 : Aegis.MaxFrequencyScore.max_frequency_score nums k1 = ok r1)
      (hr2 : Aegis.MaxFrequencyScore.max_frequency_score nums k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (k1 k2 : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk1 : 0 ≤ k1.val) (hle : k1.val ≤ k2.val) (hk2max : k2.val ≤ 100000000000000)
        (r1 r2 : I64)
        (hr1 : Aegis.MaxFrequencyScore.max_frequency_score nums k1 = ok r1)
        (hr2 : Aegis.MaxFrequencyScore.max_frequency_score nums k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns r and max_frequency_score(nums2, k) returns r2, r = r2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000; len(nums2) = len(nums); nums2 is a permutation of nums (the same multiset of values); for every i with 0 <= i < len(nums2), 1 <= nums2[i] <= 1000000000. -/
  theorem spec_9 (nums nums2 : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hrange2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlen2 : nums2.val.length = nums.val.length)
      (hperm : (vals nums2).Perm (vals nums))
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r r2 : I64)
      (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r)
      (hr2 : Aegis.MaxFrequencyScore.max_frequency_score nums2 k = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hrange2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hlen2 : nums2.val.length = nums.val.length)
        (hperm : (vals nums2).Perm (vals nums))
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r r2 : I64)
        (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r)
        (hr2 : Aegis.MaxFrequencyScore.max_frequency_score nums2 k = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, if k is at least (len(nums) - 1) multiplied by (max over 0 <= i < len(nums) of nums[i] minus min over 0 <= i < len(nums) of nums[i]), then r = len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_10 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (hbig : ((nums.val.length : ℤ) - 1) * (listMax (vals nums) - listMin (vals nums)) ≤ k.val)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (hbig : ((nums.val.length : ℤ) - 1) * (listMax (vals nums) - listMin (vals nums)) ≤ k.val)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, there exist an index j with 0 <= j < len(nums) and a set S of r distinct indices with j in S such that the sum over i in S of |nums[i] - nums[j]| is at most k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      ∃ j : Fin (vals nums).length, ∃ S : Finset (Fin (vals nums).length),
        j ∈ S ∧ (S.card : ℤ) = r.val ∧
          S.sum (fun i => |(vals nums).get i - (vals nums).get j|) ≤ k.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), ∃ j : Fin (vals nums).length, ∃ S : Finset (Fin (vals nums).length),
          j ∈ S ∧ (S.card : ℤ) = r.val ∧
            S.sum (fun i => |(vals nums).get i - (vals nums).get j|) ≤ k.val) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, if r < len(nums), then for every index j with 0 <= j < len(nums) and every set S of r+1 distinct indices with j in S, the sum over i in S of |nums[i] - nums[j]| is greater than k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_12 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r)
      (hlt : r.val < (nums.val.length : ℤ)) :
      ∀ (j : Fin (vals nums).length) (S : Finset (Fin (vals nums).length)),
        j ∈ S → (S.card : ℤ) = r.val + 1 →
          k.val < S.sum (fun i => |(vals nums).get i - (vals nums).get j|) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r)
        (hlt : r.val < (nums.val.length : ℤ)), ∀ (j : Fin (vals nums).length) (S : Finset (Fin (vals nums).length)),
          j ∈ S → (S.card : ℤ) = r.val + 1 →
            k.val < S.sum (fun i => |(vals nums).get i - (vals nums).get j|)) := by
    sorry

  /-- Whenever max_frequency_score(nums, k) returns a result r, let a be the nondecreasing sorted version of nums. Then r equals the largest integer m with 1 <= m <= len(nums) for which there exist an index l with 0 <= l and l + m <= len(nums) and an integer t such that the sum over i from l to l + m - 1 of |a[i] - t| is at most k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 100000000000000. -/
  theorem spec_13 (nums : Slice I64) (k : I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
      (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r) :
      ∀ a : List ℤ, IsSortedVersion a (vals nums) →
        ∀ m : ℤ, 1 ≤ m → m ≤ (vals nums).length →
          (m ≤ r.val ↔ WindowFeasible a m k.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hrange : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk0 : 0 ≤ k.val) (hkmax : k.val ≤ 100000000000000)
        (r : I64) (hr : Aegis.MaxFrequencyScore.max_frequency_score nums k = ok r), ∀ a : List ℤ, IsSortedVersion a (vals nums) →
          ∀ m : ℤ, 1 ≤ m → m ≤ (vals nums).length →
            (m ≤ r.val ↔ WindowFeasible a m k.val)) := by
    sorry

  end AegisSpec.MaxFrequencyScore
