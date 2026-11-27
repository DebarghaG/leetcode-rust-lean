import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-the-maximum-length-of-a-good-subsequence-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.MaximumLength

  namespace AegisSpec.MaximumLength

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def changes (seq : List ℤ) : ℤ :=
    (seq.zip (seq.drop 1)).countP (fun p : ℤ × ℤ => decide (p.1 ≠ p.2))

  def IsSubseq (seq : List ℤ) (l : List ℤ) : Prop := seq.Sublist l

  def count (l : List ℤ) (v : ℤ) : ℤ := l.countP (fun x => decide (x = v))

  def maxFreq (l : List ℤ) : ℤ := (l.map (fun v => count l v)).foldr max 0

  def maxLen (l : List ℤ) (t : ℤ) : ℤ :=
    ((l.sublists.filter (fun s => decide (changes s ≤ t))).map (fun s => (s.length : ℤ))).foldr
      max 0

  def SameEqualityPattern (l l' : List ℤ) : Prop :=
    ∃ h : l.length = l'.length,
      ∀ i j : Fin l.length,
        (l.get i = l.get j ↔ l'.get (Fin.cast h i) = l'.get (Fin.cast h j))

  /-- Let changes(seq) be the number of adjacent unequal pairs in seq (0 if len(seq)<2). The function returns a result r, and r equals the maximum length of a subsequence seq of nums (obtained by deleting zero or more elements while preserving order; empty allowed) such that changes(seq) <= k. Equivalently, r = max { L | there exist 0 <= i_0 < ... < i_{L-1} < len(nums) and the sequence [nums[i_0],...,nums[i_{L-1}]] has at most k indices j with 0 <= j < L-1 and nums[i_j] != nums[i_{j+1}] }.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. Indices are 0-based. -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧
        (∃ seq : List ℤ,
          IsSubseq seq (vals nums) ∧ changes seq ≤ k.val ∧ (seq.length : ℤ) = r.val) ∧
        (∀ seq : List ℤ,
          IsSubseq seq (vals nums) → changes seq ≤ k.val → (seq.length : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64, maximum_length nums k = Result.ok r ∧
          (∃ seq : List ℤ,
            IsSubseq seq (vals nums) ∧ changes seq ≤ k.val ∧ (seq.length : ℤ) = r.val) ∧
          (∀ seq : List ℤ,
            IsSubseq seq (vals nums) → changes seq ≤ k.val → (seq.length : ℤ) ≤ r.val)) := by
    sorry

  /-- Let changes(seq) be the number of adjacent unequal pairs in seq. The function returns a result r, and there exists a subsequence seq of nums with len(seq) = r and changes(seq) <= k. (A subsequence is obtained by deleting zero or more elements from nums while preserving order.)
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧
        ∃ seq : List ℤ,
          IsSubseq seq (vals nums) ∧ (seq.length : ℤ) = r.val ∧ changes seq ≤ k.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64, maximum_length nums k = Result.ok r ∧
          ∃ seq : List ℤ,
            IsSubseq seq (vals nums) ∧ (seq.length : ℤ) = r.val ∧ changes seq ≤ k.val) := by
    sorry

  /-- Let changes(seq) be the number of adjacent unequal pairs in seq. The function returns a result r, and for every subsequence seq of nums with changes(seq) <= k, len(seq) <= r.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧
        ∀ seq : List ℤ,
          IsSubseq seq (vals nums) → changes seq ≤ k.val → (seq.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64, maximum_length nums k = Result.ok r ∧
          ∀ seq : List ℤ,
            IsSubseq seq (vals nums) → changes seq ≤ k.val → (seq.length : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64, maximum_length nums k = Result.ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64, maximum_length nums k = Result.ok r) := by
    sorry

  /-- The function returns a result r, and 1 <= r <= len(nums).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧ 1 ≤ r.val ∧ r.val ≤ (nums.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧ 1 ≤ r.val ∧ r.val ≤ (nums.length : ℤ)) := by
    sorry

  /-- Let count(nums,v) = #{ i | 0 <= i < len(nums) and nums[i] = v }. The function returns a result r, and r = max { count(nums,v) | v is an integer }, i.e. r is the maximum frequency of any value in nums.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); k = 0; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_6 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) (hk_zero : k.val = 0) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧ r.val = maxFreq (vals nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) (hk_zero : k.val = 0), ∃ r : I64, maximum_length nums k = Result.ok r ∧ r.val = maxFreq (vals nums)) := by
    sorry

  /-- With changes(seq) counting adjacent unequal pairs, the function returns a result r, and r = min(len(nums), k + 1).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; for all 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9)
      (hdistinct : (vals nums).Nodup) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧ r.val = min (nums.length : ℤ) (k.val + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9)
        (hdistinct : (vals nums).Nodup), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧ r.val = min (nums.length : ℤ) (k.val + 1)) := by
    sorry

  /-- The function returns a result r, and r = len(nums).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; let C = #{ i | 0 <= i < len(nums)-1 and nums[i] != nums[i+1] }; assume C <= k. -/
  theorem spec_8 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9)
      (hC : changes (vals nums) ≤ k.val) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧ r.val = (nums.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9)
        (hC : changes (vals nums) ≤ k.val), ∃ r : I64, maximum_length nums k = Result.ok r ∧ r.val = (nums.length : ℤ)) := by
    sorry

  /-- Let count(nums,v) = #{ i | 0 <= i < len(nums) and nums[i] = v } and M = max { count(nums,v) | v is an integer }. The function returns a result r, and r >= M.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_9 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64, maximum_length nums k = Result.ok r ∧ maxFreq (vals nums) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64, maximum_length nums k = Result.ok r ∧ maxFreq (vals nums) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r >= min(len(nums), k + 1).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_10 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧ min (nums.length : ℤ) (k.val + 1) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧ min (nums.length : ℤ) (k.val + 1) ≤ r.val) := by
    sorry

  /-- Let count(nums,v) = #{ i | 0 <= i < len(nums) and nums[i] = v } and M = max { count(nums,v) | v is an integer }. The function returns a result r, and r <= min(len(nums), (k + 1) * M).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧
          r.val ≤ min (nums.length : ℤ) ((k.val + 1) * maxFreq (vals nums)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧
            r.val ≤ min (nums.length : ℤ) ((k.val + 1) * maxFreq (vals nums))) := by
    sorry

  /-- Let f(t) be the maximum length of a subsequence of nums with at most t adjacent unequal pairs, for any integer t >= 0. The function returns a result r, and for every integer t with k <= t, f(t) >= r.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_12 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧ ∀ t : ℤ, k.val ≤ t → r.val ≤ maxLen (vals nums) t := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧ ∀ t : ℤ, k.val ≤ t → r.val ≤ maxLen (vals nums) t) := by
    sorry

  /-- The function returns a result r, and r also equals the maximum length of a subsequence of rev(nums) with at most k adjacent unequal pairs, where rev(nums)[i] = nums[len(nums)-1-i] for 0 <= i < len(nums).
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_13 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧ r.val = maxLen (vals nums).reverse k.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧ r.val = maxLen (vals nums).reverse k.val) := by
    sorry

  /-- The function returns a result r, and for every array nums' of the same length as nums such that for all i,j with 0 <= i,j < len(nums), nums[i] = nums[j] iff nums'[i] = nums'[j], the maximum length of a subsequence of nums' with at most k adjacent unequal pairs is also r.
    Preconditions: 1 <= len(nums) <= 500; 0 <= k <= min(len(nums), 25); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
  theorem spec_14 (nums : Slice I64) (k : I64)
      (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
      (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
      (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9) :
      ∃ r : I64,
        maximum_length nums k = Result.ok r ∧
          ∀ nums' : Slice I64,
            SameEqualityPattern (vals nums) (vals nums') →
              maxLen (vals nums') k.val = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hlen_pos : 1 ≤ nums.length) (hlen_le : nums.length ≤ 500)
        (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ min (nums.length : ℤ) 25)
        (hvals : ∀ v ∈ vals nums, 1 ≤ v ∧ v ≤ 10 ^ 9), ∃ r : I64,
          maximum_length nums k = Result.ok r ∧
            ∀ nums' : Slice I64,
              SameEqualityPattern (vals nums) (vals nums') →
                maxLen (vals nums') k.val = r.val) := by
    sorry

  end AegisSpec.MaximumLength
