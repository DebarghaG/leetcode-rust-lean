import Aegis.TopKFrequent.Code.Funs

/-!
# Specifications of `Aegis.TopKFrequent.top_k_frequent`

LeetCode problem `top-k-frequent-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TopKFrequent

  def slElems (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def vecElems (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def freq (l : List ℤ) (v : ℤ) : ℕ := l.countP (fun x => decide (x = v))

  def freqN (s : Slice Std.I64) (v : ℤ) : ℕ := freq (slElems s) v

  def occurs (s : Slice Std.I64) (v : ℤ) : Prop := v ∈ slElems s

  def distinctCount (s : Slice Std.I64) : ℕ := (slElems s).dedup.length

  def freqMultiset (s : Slice Std.I64) : List ℕ := (slElems s).dedup.map (freqN s)

  def IsKLargest (k : ℕ) (M F : List ℕ) : Prop :=
    ∃ D : List ℕ, List.Perm (M ++ D) F ∧ M.length = k ∧ ∀ m ∈ M, ∀ d ∈ D, d ≤ m

  def IsTopKSet (nums : Slice Std.I64) (k : Std.I64) (S : Finset ℤ) : Prop :=
    (S.card : ℤ) = k.val ∧
      (∀ x ∈ S, occurs nums x) ∧
      (∀ x ∈ S, ∀ y : ℤ, occurs nums y → y ∉ S → freqN nums y ≤ freqN nums x)

  def AnswerUnique (nums : Slice Std.I64) (k : Std.I64) : Prop :=
    ∃! S : Finset ℤ, IsTopKSet nums k S

  def minEntryFreq (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64) : WithTop ℕ :=
    List.minimum ((vecElems r).map (freqN nums))

  /-- The function returns a result r and all of the following hold. Let freq(nums, v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. (a) len(r) = k. (b) For all i, j with 0 <= i < j < len(r), r[i] != r[j]. (c) For every i with 0 <= i < len(r) there is j with 0 <= j < len(nums) and nums[j] = r[i]. (d) For every entry x of r and every value y occurring in nums that is not equal to any entry of r, freq(nums, y) <= freq(nums, x). Thus r is exactly a set of k distinct values of nums with largest frequencies, in any order.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). The answer is unique: there is exactly one set S of k distinct values occurring in nums such that for every x in S and every y occurring in nums but not in S, freq(nums, x) >= freq(nums, y), where freq(nums, v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
      (huniq : AnswerUnique nums k) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.TopKFrequent.top_k_frequent nums k = ok r ∧
          (r.val.length : ℤ) = k.val ∧
          (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
            i < j → r.val[i] ≠ r.val[j]) ∧
          (∀ (i : ℕ) (hi : i < r.val.length),
            ∃ (j : ℕ) (hj : j < nums.val.length), nums.val[j].val = r.val[i].val) ∧
          (∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
            (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
            freqN nums y ≤ freqN nums x) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
        (huniq : AnswerUnique nums k), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.TopKFrequent.top_k_frequent nums k = ok r ∧
            (r.val.length : ℤ) = k.val ∧
            (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
              i < j → r.val[i] ≠ r.val[j]) ∧
            (∀ (i : ℕ) (hi : i < r.val.length),
              ∃ (j : ℕ) (hj : j < nums.val.length), nums.val[j].val = r.val[i].val) ∧
            (∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
              (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
              freqN nums y ≤ freqN nums x)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, panic, overflow, or perform an out-of-bounds access.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). The uniqueness guarantee is not needed for this claim. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∃ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = k (where k is interpreted as its mathematical integer value).
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TopKFrequent.top_k_frequent nums k = ok r → (r.val.length : ℤ) = k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TopKFrequent.top_k_frequent nums k = ok r → (r.val.length : ℤ) = k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices i, j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
          i < j → r.val[i] ≠ r.val[j] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
            i < j → r.val[i] ≠ r.val[j]) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r) there exists an index j with 0 <= j < len(nums) such that nums[j] = r[i].
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ (i : ℕ) (hi : i < r.val.length),
          ∃ (j : ℕ) (hj : j < nums.val.length), nums.val[j].val = r.val[i].val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ (i : ℕ) (hi : i < r.val.length),
            ∃ (j : ℕ) (hj : j < nums.val.length), nums.val[j].val = r.val[i].val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), -10000 <= r[i] <= 10000.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ (i : ℕ) (hi : i < r.val.length), -10000 ≤ r.val[i].val ∧ r.val[i].val ≤ 10000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ (i : ℕ) (hi : i < r.val.length), -10000 ≤ r.val[i].val ∧ r.val[i].val ≤ 10000) := by
    sorry

  /-- Whenever the function returns a result r, let freq(nums, v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Then for every entry x of r and every value y occurring in nums that is not equal to any entry of r, freq(nums, y) <= freq(nums, x).
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
          (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
          freqN nums y ≤ freqN nums x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
            (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
            freqN nums y ≤ freqN nums x) := by
    sorry

  /-- Whenever the function returns a result r, let freq(nums, v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Then for every entry x of r and every value y occurring in nums that is not equal to any entry of r, freq(nums, y) < freq(nums, x).
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). The answer is unique: there is exactly one set S of k distinct values occurring in nums such that for every x in S and every y occurring in nums but not in S, freq(nums, x) >= freq(nums, y), where freq(nums, v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
      (huniq : AnswerUnique nums k) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
          (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
          freqN nums y < freqN nums x := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
        (huniq : AnswerUnique nums k), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ x : ℤ, x ∈ vecElems r → ∀ y : ℤ, occurs nums y →
            (∀ (i : ℕ) (hi : i < r.val.length), r.val[i].val ≠ y) →
            freqN nums y < freqN nums x) := by
    sorry

  /-- Whenever the function returns a result r, let freq(nums, v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Let T = min { freq(nums, r[i]) | 0 <= i < len(r) }. Then for every value x occurring in nums, x is equal to some entry of r if and only if freq(nums, x) >= T.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). The answer is unique: there is exactly one set S of k distinct values occurring in nums such that for every x in S and every y occurring in nums but not in S, freq(nums, x) >= freq(nums, y), where freq(nums, v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
      (huniq : AnswerUnique nums k) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        ∀ x : ℤ, occurs nums x →
          ((∃ (i : ℕ) (hi : i < r.val.length), r.val[i].val = x) ↔
            (freqN nums x : WithTop ℕ) ≥ minEntryFreq nums r) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
        (huniq : AnswerUnique nums k), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          ∀ x : ℤ, occurs nums x →
            ((∃ (i : ℕ) (hi : i < r.val.length), r.val[i].val = x) ↔
              (freqN nums x : WithTop ℕ) ≥ minEntryFreq nums r)) := by
    sorry

  /-- Whenever the function returns a result r, let freq(nums, v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Let F be the multiset of frequencies { freq(nums, v) | v occurs in nums }, with one occurrence per distinct value v. Then the multiset { freq(nums, r[i]) | 0 <= i < len(r) } equals the multiset consisting of the k largest elements of F, counting multiplicities.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
        IsKLargest k.val.toNat ((vecElems r).map (freqN nums)) (freqMultiset nums) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64, Aegis.TopKFrequent.top_k_frequent nums k = ok r →
          IsKLargest k.val.toNat ((vecElems r).map (freqN nums)) (freqMultiset nums)) := by
    sorry

  /-- Let freq(s, v) be the number of indices j with 0 <= j < len(s) and s[j] = v for a slice s. For every slice nums2 of 64-bit integers with len(nums2) = len(nums) and with freq(nums2, v) = freq(nums, v) for every 64-bit value v, whenever the function returns r on nums and r2 on nums2, the set of entries of r equals the set of entries of r2: for every value v, v equals some entry of r if and only if v equals some entry of r2.
    Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= the number of distinct values occurring in nums (k interpreted as its mathematical integer value). The answer is unique: there is exactly one set S of k distinct values occurring in nums such that for every x in S and every y occurring in nums but not in S, freq(nums, x) >= freq(nums, y), where freq(nums, v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
      (huniq : AnswerUnique nums k) :
      ∀ nums2 : Slice Std.I64,
        nums2.val.length = nums.val.length →
          (∀ v : ℤ, freqN nums2 v = freqN nums v) →
            ∀ (r r2 : alloc.vec.Vec Std.I64),
              Aegis.TopKFrequent.top_k_frequent nums k = ok r →
                Aegis.TopKFrequent.top_k_frequent nums2 k = ok r2 →
                  ∀ v : ℤ, (v ∈ vecElems r ↔ v ∈ vecElems r2) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hk : 1 ≤ k.val) (hkdistinct : k.val ≤ (distinctCount nums : ℤ))
        (huniq : AnswerUnique nums k), ∀ nums2 : Slice Std.I64,
          nums2.val.length = nums.val.length →
            (∀ v : ℤ, freqN nums2 v = freqN nums v) →
              ∀ (r r2 : alloc.vec.Vec Std.I64),
                Aegis.TopKFrequent.top_k_frequent nums k = ok r →
                  Aegis.TopKFrequent.top_k_frequent nums2 k = ok r2 →
                    ∀ v : ℤ, (v ∈ vecElems r ↔ v ∈ vecElems r2)) := by
    sorry

  end AegisSpec.TopKFrequent
