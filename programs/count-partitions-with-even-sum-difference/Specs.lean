import Aegis.CountPartitions.Code.Funs

/-!
# Specifications of `Aegis.CountPartitions.count_partitions`

LeetCode problem `count-partitions-with-even-sum-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPartitions

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def elem (nums : Slice I64) (i : ℕ) (hi : i < nums.val.length) : ℤ := (nums.val[i]'hi).val

def leftSum (nums : Slice I64) (i : ℕ) : ℤ := ((vals nums).take (i + 1)).sum

def rightSum (nums : Slice I64) (i : ℕ) : ℤ := ((vals nums).drop (i + 1)).sum

def diff (nums : Slice I64) (i : ℕ) : ℤ := leftSum nums i - rightSum nums i

def totalSum (nums : Slice I64) : ℤ := (vals nums).sum

def EvenZ (x : ℤ) : Prop := ∃ k : ℤ, x = 2 * k

def OddZ (x : ℤ) : Prop := ∃ k : ℤ, x = 2 * k + 1

def EvenNat (m : ℕ) : Prop := ∃ k : ℕ, m = 2 * k

def OddNat (m : ℕ) : Prop := ∃ k : ℕ, m = 2 * k + 1

noncomputable instance instDecidableEvenZ (x : ℤ) : Decidable (EvenZ x) := Classical.dec _

noncomputable instance instDecidableOddZ (x : ℤ) : Decidable (OddZ x) := Classical.dec _

noncomputable instance instDecidableEvenNat (m : ℕ) : Decidable (EvenNat m) := Classical.dec _

noncomputable instance instDecidableOddNat (m : ℕ) : Decidable (OddNat m) := Classical.dec _

noncomputable def countEvenDiff (nums : Slice I64) : ℕ :=
  (List.range (nums.val.length - 1)).foldr
    (fun i acc => if EvenZ (diff nums i) then acc + 1 else acc) 0

noncomputable def oddCount (nums : Slice I64) : ℕ :=
  (vals nums).foldr (fun x acc => if OddZ x then acc + 1 else acc) 0

/-- Whenever the function returns a result r, r is the number of indices i such that 0 <= i <= n - 2 and the integer (Σ_{j=0}^{i} nums[j]) - (Σ_{j=i+1}^{n-1} nums[j]) is even. An integer x is even iff there exists an integer k with x = 2k. The first sum is the left subarray sum and the second is the right subarray sum for partition i.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    r.val = (countEvenDiff nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), r.val = (countEvenDiff nums : ℤ)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail or panic) for every nums satisfying the preconditions.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100) :
    ∃ r : I64, Aegis.CountPartitions.count_partitions nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100), ∃ r : I64, Aegis.CountPartitions.count_partitions nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, let T = Σ_{j=0}^{n-1} nums[j]. Then r = n - 1 if T is even, and r = 0 if T is odd.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    (EvenZ (totalSum nums) → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddZ (totalSum nums) → r.val = 0) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), (EvenZ (totalSum nums) → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddZ (totalSum nums) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n - 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, either r = 0 or r = n - 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    r.val = 0 ∨ r.val = (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), r.val = 0 ∨ r.val = (nums.val.length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if nums[0] and nums[1] have the same parity (equivalently, if nums[0] + nums[1] is even), and r = 0 otherwise.
  Preconditions: Let n = len(nums). Assume n = 2 and for i = 0,1, 1 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice I64) (r : I64)
    (hn : nums.val.length = 2)
    (h0 : 1 ≤ elem nums 0 (by omega) ∧ elem nums 0 (by omega) ≤ 100)
    (h1 : 1 ≤ elem nums 1 (by omega) ∧ elem nums 1 (by omega) ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    (EvenZ (elem nums 0 (by omega) + elem nums 1 (by omega)) → r.val = 1) ∧
    (OddZ (elem nums 0 (by omega) + elem nums 1 (by omega)) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn : nums.val.length = 2)
    (h0 : 1 ≤ elem nums 0 (by omega) ∧ elem nums 0 (by omega) ≤ 100)
    (h1 : 1 ≤ elem nums 1 (by omega) ∧ elem nums 1 (by omega) ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), (EvenZ (elem nums 0 (by omega) + elem nums 1 (by omega)) → r.val = 1) ∧
    (OddZ (elem nums 0 (by omega) + elem nums 1 (by omega)) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = n - 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and every nums[i] is even. -/
theorem spec_7 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (heven : ∀ (i : ℕ) (hi : i < nums.val.length), EvenZ (elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    r.val = (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (heven : ∀ (i : ℕ) (hi : i < nums.val.length), EvenZ (elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), r.val = (nums.val.length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = n - 1 if n is even, and r = 0 if n is odd.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and every nums[i] is odd. -/
theorem spec_8 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hodd : ∀ (i : ℕ) (hi : i < nums.val.length), OddZ (elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    (EvenNat nums.val.length → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddNat nums.val.length → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hodd : ∀ (i : ℕ) (hi : i < nums.val.length), OddZ (elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), (EvenNat nums.val.length → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddNat nums.val.length → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, let m be the number of indices i with 0 <= i < n such that nums[i] is odd. Then r = n - 1 if m is even, and r = 0 if m is odd.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    (EvenNat (oddCount nums) → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddNat (oddCount nums) → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), (EvenNat (oddCount nums) → r.val = (nums.val.length : ℤ) - 1) ∧
    (OddNat (oddCount nums) → r.val = 0)) := by
  sorry

/-- Whenever the function returns r on input nums and r' on input nums', we have r = r'.
  Preconditions: Let n = len(nums) = len(nums'). Assume 2 <= n <= 100, all elements of nums and nums' lie in [1,100], there is an index k with 0 <= k < n and an even integer c such that nums'[k] = nums[k] + c, and nums'[i] = nums[i] for every i with 0 <= i < n and i != k. -/
theorem spec_10 (nums nums' : Slice I64) (r r' : I64)
    (hlen : nums'.val.length = nums.val.length)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hbound' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ elem nums' i hi ∧ elem nums' i hi ≤ 100)
    (hchange : ∃ (k : ℕ) (hk : k < nums.val.length) (hk' : k < nums'.val.length) (c : ℤ),
      EvenZ c ∧ elem nums' k hk' = elem nums k hk + c ∧
      (∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        i ≠ k → elem nums' i hi' = elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r)
    (hres' : Aegis.CountPartitions.count_partitions nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64) (r r' : I64)
    (hlen : nums'.val.length = nums.val.length)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hbound' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      1 ≤ elem nums' i hi ∧ elem nums' i hi ≤ 100)
    (hchange : ∃ (k : ℕ) (hk : k < nums.val.length) (hk' : k < nums'.val.length) (c : ℤ),
      EvenZ c ∧ elem nums' k hk' = elem nums k hk + c ∧
      (∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        i ≠ k → elem nums' i hi' = elem nums i hi))
    (hres : Aegis.CountPartitions.count_partitions nums = ok r)
    (hres' : Aegis.CountPartitions.count_partitions nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, if r = n - 1 then for every i with 0 <= i <= n - 2 the difference (Σ_{j=0}^{i} nums[j]) - (Σ_{j=i+1}^{n-1} nums[j]) is even; if r = 0 then for every i with 0 <= i <= n - 2 this difference is odd.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100 and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_11 (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r) :
    (r.val = (nums.val.length : ℤ) - 1 →
      ∀ i : ℕ, i ≤ nums.val.length - 2 → EvenZ (diff nums i)) ∧
    (r.val = 0 → ∀ i : ℕ, i ≤ nums.val.length - 2 → OddZ (diff nums i)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ elem nums i hi ∧ elem nums i hi ≤ 100)
    (hres : Aegis.CountPartitions.count_partitions nums = ok r), (r.val = (nums.val.length : ℤ) - 1 →
      ∀ i : ℕ, i ≤ nums.val.length - 2 → EvenZ (diff nums i)) ∧
    (r.val = 0 → ∀ i : ℕ, i ≤ nums.val.length - 2 → OddZ (diff nums i))) := by
  sorry

end AegisSpec.CountPartitions
