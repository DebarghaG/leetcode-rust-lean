import Aegis.MinimumDifference.Code.Funs

/-!
# Specifications of `Aegis.MinimumDifference.minimum_difference`

LeetCode problem `minimum-difference-between-highest-and-lowest-of-k-scores`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumDifference

  namespace AegisSpec.MinimumDifference

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def listMax : List Int → Int
    | [] => 0
    | a :: rest => rest.foldl max a

  def listMin : List Int → Int
    | [] => 0
    | a :: rest => rest.foldl min a

  def ksubsets (n k : Nat) : Finset (Finset Nat) :=
    (Finset.range n).powerset.filter (fun S => S.card = k)

  def spreadAt (l : List Int) (S : Finset Nat) : Int :=
    if h : S.Nonempty then
      S.sup' h (fun i => l.getD i 0) - S.inf' h (fun i => l.getD i 0)
    else 0

  def minSpread (l : List Int) (k : Nat) : Int :=
    if h : (ksubsets l.length k).Nonempty then
      (ksubsets l.length k).inf' h (fun S => spreadAt l S)
    else 0

  /-- Let M(nums,k) be the minimum, over all subsets S of {0,...,n-1} with |S| = k, of (max_{i in S} nums[i] - min_{i in S} nums[i]). The function returns a result r and r = M(nums,k).
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 10^5. The values k and nums[i] are 64-bit signed integers. All arithmetic used in the descriptions is mathematical integer arithmetic; the described answer is between 0 and 10^5, so it fits in Std.I64. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r : Std.I64, minimum_difference nums k = ok r ∧
        r.val = minSpread (contents nums) k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000), ∃ r : Std.I64, minimum_difference nums k = ok r ∧
          r.val = minSpread (contents nums) k.val.toNat) := by
    sorry

  /-- For every such nums and k, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r : Std.I64, minimum_difference nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000), ∃ r : Std.I64, minimum_difference nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r on such inputs, 0 <= r <= (max_{0 <= i < n} nums[i]) - (min_{0 <= i < n} nums[i]).
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (r : Std.I64) (hr : minimum_difference nums k = ok r) :
      0 ≤ r.val ∧ r.val ≤ listMax (contents nums) - listMin (contents nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (r : Std.I64) (hr : minimum_difference nums k = ok r), 0 ≤ r.val ∧ r.val ≤ listMax (contents nums) - listMin (contents nums)) := by
    sorry

  /-- Whenever the function returns a result r on such inputs, there exists a subset S of {0,...,n-1} with |S| = k such that r = (max_{i in S} nums[i]) - (min_{i in S} nums[i]).
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (r : Std.I64) (hr : minimum_difference nums k = ok r) :
      ∃ S ∈ ksubsets nums.val.length k.val.toNat,
        r.val = spreadAt (contents nums) S := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (r : Std.I64) (hr : minimum_difference nums k = ok r), ∃ S ∈ ksubsets nums.val.length k.val.toNat,
          r.val = spreadAt (contents nums) S) := by
    sorry

  /-- Whenever the function returns a result r on such inputs, for every subset S of {0,...,n-1} with |S| = k, (max_{i in S} nums[i]) - (min_{i in S} nums[i]) >= r.
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (r : Std.I64) (hr : minimum_difference nums k = ok r) :
      ∀ S ∈ ksubsets nums.val.length k.val.toNat,
        r.val ≤ spreadAt (contents nums) S := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (r : Std.I64) (hr : minimum_difference nums k = ok r), ∀ S ∈ ksubsets nums.val.length k.val.toNat,
          r.val ≤ spreadAt (contents nums) S) := by
    sorry

  /-- Whenever the function returns a result r on such inputs, r = 0 if and only if there exists a value v such that at least k indices i with 0 <= i < n satisfy nums[i] = v.
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (r : Std.I64) (hr : minimum_difference nums k = ok r) :
      r.val = 0 ↔ ∃ v : Int, k.val ≤ ((contents nums).count v : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (r : Std.I64) (hr : minimum_difference nums k = ok r), r.val = 0 ↔ ∃ v : Int, k.val ≤ ((contents nums).count v : Int)) := by
    sorry

  /-- If nums2 is a permutation of nums, meaning that for every value v the number of indices i with nums[i] = v equals the number of indices i with nums2[i] = v, and if minimum_difference(nums,k) returns r and minimum_difference(nums2,k) returns r2, then r = r2.
    Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. Let nums2 be another slice of length n satisfying the same element bounds. -/
  theorem spec_7 (nums nums2 : Slice Std.I64) (k : Std.I64)
      (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (hlen : nums2.val.length = nums.val.length)
      (hb2 : ∀ x ∈ nums2.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (hperm : ∀ v : Int, (contents nums).count v = (contents nums2).count v)
      (r r2 : Std.I64)
      (hr : minimum_difference nums k = ok r)
      (hr2 : minimum_difference nums2 k = ok r2) :
      r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
        (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (hlen : nums2.val.length = nums.val.length)
        (hb2 : ∀ x ∈ nums2.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (hperm : ∀ v : Int, (contents nums).count v = (contents nums2).count v)
        (r r2 : Std.I64)
        (hr : minimum_difference nums k = ok r)
        (hr2 : minimum_difference nums2 k = ok r2), r = r2) := by
    sorry

  /-- If minimum_difference(nums,k1) returns r1 and minimum_difference(nums,k2) returns r2, then r1 <= r2.
    Preconditions: Let n = len(nums). Assume 1 <= k1 <= k2 <= n <= 1000 and 0 <= nums[i] <= 10^5 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (h1 : 1 ≤ k1.val) (h12 : k1.val ≤ k2.val)
      (h2n : k2.val ≤ (nums.val.length : Int))
      (hn : nums.val.length ≤ 1000)
      (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
      (r1 r2 : Std.I64)
      (hr1 : minimum_difference nums k1 = ok r1)
      (hr2 : minimum_difference nums k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (h1 : 1 ≤ k1.val) (h12 : k1.val ≤ k2.val)
        (h2n : k2.val ≤ (nums.val.length : Int))
        (hn : nums.val.length ≤ 1000)
        (hb : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
        (r1 r2 : Std.I64)
        (hr1 : minimum_difference nums k1 = ok r1)
        (hr2 : minimum_difference nums k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinimumDifference
