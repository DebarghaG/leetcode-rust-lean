import Aegis.FindKDistantIndices.Code.Funs

/-!
# Specifications of `Aegis.FindKDistantIndices.find_k_distant_indices`

LeetCode problem `find-all-k-distant-indices-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindKDistantIndices

  def occursAt (nums : List Int) (key : Int) (j : Nat) : Prop :=
    ∃ (hj : j < nums.length), nums[j] = key

  def keyOccurs (nums : List Int) (key : Int) : Prop :=
    ∃ j : Nat, occursAt nums key j

  def isKDistant (nums : List Int) (key : Int) (k : Int) (i : Int) : Prop :=
    0 ≤ i ∧ i < (nums.length : Int) ∧
      ∃ (j : Nat) (hj : j < nums.length), nums[j] = key ∧ |i - (j : Int)| ≤ k

  def kDistantCount (nums : List Int) (key : Int) (k : Int) : Nat :=
    (Finset.univ.filter (fun i : Fin nums.length =>
      ∃ (j : Fin nums.length),
        nums.get j = key ∧ |(i.val : Int) - (j.val : Int)| ≤ k)).card

  /-- The function returns a result r and r is exactly the increasing list of all k-distant indices of nums. Define an index i to be k-distant when 0 <= i < len(nums) and there exists j with 0 <= j < len(nums), nums[j] = key, and |i - j| <= k. Then: (a) for every t with 0 <= t < len(r), r[t] is k-distant; (b) for every k-distant i there is exactly one t with 0 <= t < len(r) and r[t] = i; (c) for every t with 0 <= t + 1 < len(r), r[t] < r[t + 1]. These conditions characterize r completely.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). (The original statement says 1 <= k; k = 0 is also allowed here because the supplied examples use it.) -/
  theorem spec_1
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int)) :
      ∃ (r : alloc.vec.Vec Std.I64),
        Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r ∧
        (∀ (t : Nat) (ht : t < r.val.length),
          isKDistant nums.val key.val k.val (r.val[t]).val) ∧
        (∀ (i : Int), isKDistant nums.val key.val k.val i →
          ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = i ∧
            ∀ (t' : Nat) (ht' : t' < r.val.length), (r.val[t']).val = i → t' = t) ∧
        (∀ (t : Nat) (ht : t + 1 < r.val.length), (r.val[t]).val < (r.val[t + 1]).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int)), ∃ (r : alloc.vec.Vec Std.I64),
          Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r ∧
          (∀ (t : Nat) (ht : t < r.val.length),
            isKDistant nums.val key.val k.val (r.val[t]).val) ∧
          (∀ (i : Int), isKDistant nums.val key.val k.val i →
            ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = i ∧
              ∀ (t' : Nat) (ht' : t' < r.val.length), (r.val[t']).val = i → t' = t) ∧
          (∀ (t : Nat) (ht : t + 1 < r.val.length), (r.val[t]).val < (r.val[t + 1]).val)) := by
    sorry

  /-- The function returns a result r; in particular it does not fail, panic, index out of bounds, or overflow on any input satisfying the preconditions.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_2
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int)) :
      ∃ (r : alloc.vec.Vec Std.I64),
        Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int)), ∃ (r : alloc.vec.Vec Std.I64),
          Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t < len(r), 0 <= r[t] < len(nums). Thus every value in the returned vector is a valid 0-based index of nums.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_3
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      ∀ (t : Nat) (ht : t < r.val.length),
        0 ≤ (r.val[t]).val ∧ (r.val[t]).val < (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), ∀ (t : Nat) (ht : t < r.val.length),
          0 ≤ (r.val[t]).val ∧ (r.val[t]).val < (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t + 1 < len(r), r[t] < r[t + 1]. Hence r is strictly increasing.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_4
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      ∀ (t : Nat) (ht : t + 1 < r.val.length), (r.val[t]).val < (r.val[t + 1]).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), ∀ (t : Nat) (ht : t + 1 < r.val.length), (r.val[t]).val < (r.val[t + 1]).val) := by
    sorry

  /-- Whenever the function returns a result r, for every t with 0 <= t < len(r) there exists j with 0 <= j < len(nums), nums[j] = key, and |r[t] - j| <= k. Thus every returned index is k-distant.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_5
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      ∀ (t : Nat) (ht : t < r.val.length),
        ∃ (j : Nat) (hj : j < nums.val.length),
          nums.val[j] = key.val ∧ |(r.val[t]).val - (j : Int)| ≤ k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), ∀ (t : Nat) (ht : t < r.val.length),
          ∃ (j : Nat) (hj : j < nums.val.length),
            nums.val[j] = key.val ∧ |(r.val[t]).val - (j : Int)| ≤ k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if there exists j with 0 <= j < len(nums), nums[j] = key, and |i - j| <= k, then there exists t with 0 <= t < len(r) and r[t] = i. Thus every k-distant index is returned.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_6
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      ∀ (i : Nat) (hi : i < nums.val.length),
        (∃ (j : Nat) (hj : j < nums.val.length),
          nums.val[j] = key.val ∧ |(i : Int) - (j : Int)| ≤ k.val) →
          ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = (i : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), ∀ (i : Nat) (hi : i < nums.val.length),
          (∃ (j : Nat) (hj : j < nums.val.length),
            nums.val[j] = key.val ∧ |(i : Int) - (j : Int)| ≤ k.val) →
            ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) is the number of indices i with 0 <= i < len(nums) for which there exists j with 0 <= j < len(nums), nums[j] = key, and |i - j| <= k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_7
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      r.val.length = kDistantCount nums.val key.val k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), r.val.length = kDistantCount nums.val key.val k.val) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_8
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      1 ≤ r.val.length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), 1 ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(nums) and nums[j] = key, and for every i with max(0, j - k) <= i <= min(len(nums) - 1, j + k), there exists t with 0 <= t < len(r) and r[t] = i. Thus the entire k-neighborhood of every key occurrence is returned.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums, i.e. there exists j with 0 <= j < len(nums) and nums[j] = key; and 0 <= k <= len(nums). -/
  theorem spec_9
      (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r) :
      ∀ (j : Nat) (hj : j < nums.val.length), nums.val[j] = key.val →
        ∀ (i : Nat),
          max 0 ((j : Int) - k.val) ≤ (i : Int) →
          (i : Int) ≤ min ((nums.val.length : Int) - 1) ((j : Int) + k.val) →
            ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = (i : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums.val.length : Int))
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.FindKDistantIndices.find_k_distant_indices nums key k = ok r), ∀ (j : Nat) (hj : j < nums.val.length), nums.val[j] = key.val →
          ∀ (i : Nat),
            max 0 ((j : Int) - k.val) ≤ (i : Int) →
            (i : Int) ≤ min ((nums.val.length : Int) - 1) ((j : Int) + k.val) →
              ∃ (t : Nat) (ht : t < r.val.length), (r.val[t]).val = (i : Int)) := by
    sorry

  /-- Whenever find_k_distant_indices(nums1, key, k) returns r1 and find_k_distant_indices(nums2, key, k) returns r2, if for every j with 0 <= j < len(nums1), nums1[j] = key iff nums2[j] = key, then r1 = r2. Thus the answer depends only on the set of positions where the array equals key, not on the other values.
    Preconditions: For two arrays nums1 and nums2 and the same key and k: len(nums1) = len(nums2) >= 1; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000 and 1 <= nums2[i] <= 1000; key occurs in nums1; and 0 <= k <= len(nums1). -/
  theorem spec_10
      (nums1 : Slice Std.I64) (nums2 : Slice Std.I64) (key : Std.I64) (k : Std.I64)
      (hlen : nums1.val.length = nums2.val.length)
      (hlen1 : 1 ≤ nums1.val.length)
      (hval1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hval2 : ∀ (i : Nat) (hi : i < nums2.val.length),
        1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums1.val key.val)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums1.val.length : Int))
      (hpos : ∀ (j : Nat) (hj : j < nums1.val.length),
        ((nums1.val[j]).val = key.val ↔ (nums2.val[j]).val = key.val))
      (r1 : alloc.vec.Vec Std.I64) (r2 : alloc.vec.Vec Std.I64)
      (hr1 : Aegis.FindKDistantIndices.find_k_distant_indices nums1 key k = ok r1)
      (hr2 : Aegis.FindKDistantIndices.find_k_distant_indices nums2 key k = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 : Slice Std.I64) (nums2 : Slice Std.I64) (key : Std.I64) (k : Std.I64)
        (hlen : nums1.val.length = nums2.val.length)
        (hlen1 : 1 ≤ nums1.val.length)
        (hval1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hval2 : ∀ (i : Nat) (hi : i < nums2.val.length),
          1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums1.val key.val)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (nums1.val.length : Int))
        (hpos : ∀ (j : Nat) (hj : j < nums1.val.length),
          ((nums1.val[j]).val = key.val ↔ (nums2.val[j]).val = key.val))
        (r1 : alloc.vec.Vec Std.I64) (r2 : alloc.vec.Vec Std.I64)
        (hr1 : Aegis.FindKDistantIndices.find_k_distant_indices nums1 key k = ok r1)
        (hr2 : Aegis.FindKDistantIndices.find_k_distant_indices nums2 key k = ok r2), r1 = r2) := by
    sorry

  /-- Whenever find_k_distant_indices(nums, key, k1) returns r1 and find_k_distant_indices(nums, key, k2) returns r2, for every t with 0 <= t < len(r1) there exists u with 0 <= u < len(r2) and r2[u] = r1[t]. Thus increasing k can only add indices to the answer.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; key occurs in nums; and 0 <= k1 <= k2 <= len(nums). -/
  theorem spec_11
      (nums : Slice Std.I64) (key : Std.I64) (k1 : Std.I64) (k2 : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hkey : keyOccurs nums.val key.val)
      (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2 : k2.val ≤ (nums.val.length : Int))
      (r1 : alloc.vec.Vec Std.I64) (r2 : alloc.vec.Vec Std.I64)
      (hr1 : Aegis.FindKDistantIndices.find_k_distant_indices nums key k1 = ok r1)
      (hr2 : Aegis.FindKDistantIndices.find_k_distant_indices nums key k2 = ok r2) :
      ∀ (t : Nat) (ht : t < r1.val.length),
        ∃ (u : Nat) (hu : u < r2.val.length), (r2.val[u]).val = (r1.val[t]).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (key : Std.I64) (k1 : Std.I64) (k2 : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hkey : keyOccurs nums.val key.val)
        (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2 : k2.val ≤ (nums.val.length : Int))
        (r1 : alloc.vec.Vec Std.I64) (r2 : alloc.vec.Vec Std.I64)
        (hr1 : Aegis.FindKDistantIndices.find_k_distant_indices nums key k1 = ok r1)
        (hr2 : Aegis.FindKDistantIndices.find_k_distant_indices nums key k2 = ok r2), ∀ (t : Nat) (ht : t < r1.val.length),
          ∃ (u : Nat) (hu : u < r2.val.length), (r2.val[u]).val = (r1.val[t]).val) := by
    sorry

  end AegisSpec.FindKDistantIndices
