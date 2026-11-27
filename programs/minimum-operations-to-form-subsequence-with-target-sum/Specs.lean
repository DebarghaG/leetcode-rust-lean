import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-form-subsequence-with-target-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinOperations

  namespace AegisSpec.MinOperations

  def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def sliceSum (nums : Slice Std.I64) : Int := (sliceVals nums).sum

  def IsPow2 (x : Int) : Prop := ∃ j : Nat, j ≤ 30 ∧ x = (2 : Int) ^ j

  def v2 (n : Nat) : Nat := Nat.findGreatest (fun e => 2 ^ e ∣ n) n

  def Step (a a' : List Int) : Prop :=
    ∃ (p : Nat) (hp : p < a.length) (x : Int),
      a.get ⟨p, hp⟩ = x ∧ 1 < x ∧ a' = a.take p ++ a.drop (p + 1) ++ [x / 2, x / 2]

  def Steps : Nat → List Int → List Int → Prop
    | 0, a, a' => a' = a
    | k + 1, a, a' => ∃ b, Step a b ∧ Steps k b a'

  def HasSubsequenceSum (a : List Int) (t : Int) : Prop :=
    ∃ s : List Int, s.Sublist a ∧ s.sum = t

  /-- The function returns a result r and the following holds. If target > sum_{i=0}^{n-1} nums[i], then r = -1. Otherwise, r is the least integer k >= 0 for which there exist arrays A_0,...,A_k with A_0 = nums, each A_{t+1} obtained from A_t by choosing an index p with 0 <= p < len(A_t) and A_t[p] > 1, deleting A_t[p], and appending two copies of A_t[p]/2, and such that some subsequence of A_k has elements summing to target. A subsequence of an array A is a list of elements at indices i_1 < ... < i_m of A; its sum is A[i_1] + ... + A[i_m] (the empty subsequence has sum 0).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧
        ((target.val > sliceSum nums → r.val = -1) ∧
         (target.val ≤ sliceSum nums →
            0 ≤ r.val ∧
            (∃ A : List Int, Steps r.val.toNat (sliceVals nums) A ∧
              HasSubsequenceSum A target.val) ∧
            ∀ (k : Nat),
              (∃ A : List Int, Steps k (sliceVals nums) A ∧ HasSubsequenceSum A target.val) →
                r.val.toNat ≤ k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val), ∃ r : Std.I64, min_operations nums target = ok r ∧
          ((target.val > sliceSum nums → r.val = -1) ∧
           (target.val ≤ sliceSum nums →
              0 ≤ r.val ∧
              (∃ A : List Int, Steps r.val.toNat (sliceVals nums) A ∧
                HasSubsequenceSum A target.val) ∧
              ∀ (k : Nat),
                (∃ A : List Int, Steps k (sliceVals nums) A ∧ HasSubsequenceSum A target.val) →
                  r.val.toNat ≤ k))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) :
      ∃ r : Std.I64, min_operations nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val), ∃ r : Std.I64, min_operations nums target = ok r) := by
    sorry

  /-- The function returns a result r, and if target <= sum_{i=0}^{n-1} nums[i], then 0 <= r <= sum_{i=0}^{n-1} (nums[i] - 1).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧
        (target.val ≤ sliceSum nums →
          0 ≤ r.val ∧ r.val ≤ (nums.val.map (fun x => x.val - 1)).sum) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val), ∃ r : Std.I64, min_operations nums target = ok r ∧
          (target.val ≤ sliceSum nums →
            0 ≤ r.val ∧ r.val ≤ (nums.val.map (fun x => x.val - 1)).sum)) := by
    sorry

  /-- The function returns a result r, and r = -1 if and only if target > sum_{i=0}^{n-1} nums[i].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧
        (r.val = -1 ↔ target.val > sliceSum nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val), ∃ r : Std.I64, min_operations nums target = ok r ∧
          (r.val = -1 ↔ target.val > sliceSum nums)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists a subset I of {0,...,n-1} such that sum_{i in I} nums[i] = target.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) :
      ∀ r : Std.I64, min_operations nums target = ok r →
        (r.val = 0 ↔
          ∃ I : Finset (Fin nums.val.length), ∑ i ∈ I, (nums.val.get i).val = target.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val), ∀ r : Std.I64, min_operations nums target = ok r →
          (r.val = 0 ↔
            ∃ I : Finset (Fin nums.val.length), ∑ i ∈ I, (nums.val.get i).val = target.val)) := by
    sorry

  /-- The function returns a result r, and: (a) if target > nums[0] then r = -1; (b) if target = nums[0] then r = 0; (c) if 1 <= target < nums[0] then r = k - v2(target), where v2(target) is the largest integer e >= 0 such that 2^e divides target.
    Preconditions: Let n = len(nums). Assume n = 1, nums[0] = 2^k for some integer k with 0 <= k <= 30, and 1 <= target < 2^31. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64) (k : Nat) (x : Std.I64)
      (hn : nums.val = [x]) (hk : k ≤ 30) (hx : x.val = (2 : Int) ^ k)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧
        (target.val > x.val → r.val = -1) ∧
        (target.val = x.val → r.val = 0) ∧
        (1 ≤ target.val → target.val < x.val →
          r.val = (k : Int) - (v2 target.val.toNat : Int)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (k : Nat) (x : Std.I64)
        (hn : nums.val = [x]) (hk : k ≤ 30) (hx : x.val = (2 : Int) ^ k)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31), ∃ r : Std.I64, min_operations nums target = ok r ∧
          (target.val > x.val → r.val = -1) ∧
          (target.val = x.val → r.val = 0) ∧
          (1 ≤ target.val → target.val < x.val →
            r.val = (k : Int) - (v2 target.val.toNat : Int))) := by
    sorry

  /-- The function returns r = min_{0 <= i < n} j_i, where for each i, j_i is the unique integer with 0 <= j_i <= 30 and nums[i] = 2^{j_i}.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, target = 1, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64) (j : Fin nums.val.length → Nat)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht : target.val = 1)
      (hj : ∀ i : Fin nums.val.length, j i ≤ 30 ∧ (nums.val.get i).val = (2 : Int) ^ (j i)) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧
        r.val = ((Finset.univ.inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ j : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (j : Fin nums.val.length → Nat)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht : target.val = 1)
        (hj : ∀ i : Fin nums.val.length, j i ≤ 30 ∧ (nums.val.get i).val = (2 : Int) ^ (j i)), ∃ r : Std.I64, min_operations nums target = ok r ∧
          r.val = ((Finset.univ.inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ j : Nat) : Int)) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, target = sum_{i=0}^{n-1} nums[i], and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
      (hsum : target.val = sliceSum nums) :
      ∃ r : Std.I64, min_operations nums target = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
        (hsum : target.val = sliceSum nums), ∃ r : Std.I64, min_operations nums target = ok r ∧ r.val = 0) := by
    sorry

  /-- If the function returns r on input (nums, target) and r' on input (nums', target), then r = r'.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. Let nums' be any permutation of nums. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (target : Std.I64) (r r' : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
      (hperm : nums'.val.Perm nums.val)
      (hr : min_operations nums target = ok r)
      (hr' : min_operations nums' target = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64) (r r' : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
        (hperm : nums'.val.Perm nums.val)
        (hr : min_operations nums target = ok r)
        (hr' : min_operations nums' target = ok r'), r.val = r'.val) := by
    sorry

  /-- Let r be the result of the function on (nums, target) and r' its result on (nums', target). If r != -1, then r' != -1 and r' <= r.
    Preconditions: Let n = len(nums). Assume 1 <= n < 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. Let j0 be any integer with 0 <= j0 <= 30, and let nums' be the array obtained by appending the value 2^{j0} to nums. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (target : Std.I64) (j0 : Nat)
      (r r' : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length < 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val) (hj0 : j0 ≤ 30)
      (happ : sliceVals nums' = sliceVals nums ++ [(2 : Int) ^ j0])
      (hr : min_operations nums target = ok r)
      (hr' : min_operations nums' target = ok r') :
      r.val ≠ -1 → (r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64) (j0 : Nat)
        (r r' : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length < 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val) (hj0 : j0 ≤ 30)
        (happ : sliceVals nums' = sliceVals nums ++ [(2 : Int) ^ j0])
        (hr : min_operations nums target = ok r)
        (hr' : min_operations nums' target = ok r'), r.val ≠ -1 → (r'.val ≠ -1 ∧ r'.val ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exists an array A obtainable from nums by exactly r operations, in the sense of the main specification, such that some subsequence of A has elements summing to target.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_11 (nums : Slice Std.I64) (target : Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
      (hr : min_operations nums target = ok r) (hr0 : 0 ≤ r.val) :
      ∃ A : List Int, Steps r.val.toNat (sliceVals nums) A ∧
        HasSubsequenceSum A target.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
        (hr : min_operations nums target = ok r) (hr0 : 0 ≤ r.val), ∃ A : List Int, Steps r.val.toNat (sliceVals nums) A ∧
          HasSubsequenceSum A target.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every integer k with 0 <= k < r and every array A obtainable from nums by exactly k operations, no subsequence of A has elements summing to target.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, 1 <= target < 2^31, and for every i with 0 <= i < n there is an integer j with 0 <= j <= 30 such that nums[i] = 2^j. -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
      (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
      (hr : min_operations nums target = ok r) (hr0 : 0 ≤ r.val) :
      ∀ (k : Nat) (A : List Int), k < r.val.toNat → Steps k (sliceVals nums) A →
        ¬ HasSubsequenceSum A target.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (ht1 : 1 ≤ target.val) (ht2 : target.val < (2 : Int) ^ 31)
        (hpow : ∀ x ∈ nums.val, IsPow2 x.val)
        (hr : min_operations nums target = ok r) (hr0 : 0 ≤ r.val), ∀ (k : Nat) (A : List Int), k < r.val.toNat → Steps k (sliceVals nums) A →
          ¬ HasSubsequenceSum A target.val) := by
    sorry

  end AegisSpec.MinOperations
