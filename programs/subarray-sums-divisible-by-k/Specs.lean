import Aegis.SubarraysDivByK.Code.Funs

/-!
# Specifications of `Aegis.SubarraysDivByK.subarrays_div_by_k`

LeetCode problem `subarray-sums-divisible-by-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SubarraysDivByK

namespace AegisSpec.SubarraysDivByK

def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

def elemAt (l : List Std.I64) (i : ℕ) : ℤ := (l.getD i 0#i64).val

def segSum (l : List ℤ) (i j : ℕ) : ℤ := ((l.drop i).take (j + 1 - i)).sum

def prefixSum (l : List ℤ) (t : ℕ) : ℤ := (l.take t).sum

def absSum (l : List ℤ) : ℕ := (l.map (fun x => x.natAbs)).sum

def countSubarrays (l : List ℤ) (p : ℤ → Prop) [DecidablePred p] : ℕ :=
  (((Finset.range l.length).product (Finset.range l.length)).filter
    (fun q => q.1 ≤ q.2 ∧ p (segSum l q.1 q.2))).card

def countDivByK (l : List ℤ) (k : ℤ) : ℕ := countSubarrays l (fun s => k ∣ s)

def countZeroSum (l : List ℤ) : ℕ := countSubarrays l (fun s => s = 0)

def countElemsDivByK (l : List ℤ) (k : ℤ) : ℕ := (l.filter (fun x => k ∣ x)).length

def residueCount (l : List ℤ) (k a : ℤ) : ℕ :=
  ((Finset.range (l.length + 1)).filter (fun t => k ∣ prefixSum l t - a)).card

def residueSum (l : List ℤ) (k : ℤ) : ℕ :=
  ∑ a ∈ Finset.range k.toNat, residueCount l k (a : ℤ) * (residueCount l k (a : ℤ) - 1) / 2

/-- Whenever the function returns a result r, r equals C(nums,k), where C(nums,k) is the number of pairs (i,j) of integers such that 0 <= i <= j < len(nums) and k divides the integer sum Σ_{t=i}^{j} nums[t]. Here divisibility means there exists an integer q with Σ_{t=i}^{j} nums[t] = q*k, and the sum is over the non-empty contiguous subarray nums[i], nums[i+1], ..., nums[j].
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals nums.val) k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals nums.val) k.val : ℤ)) := by
  sorry

/-- For every input nums and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow. In particular, since k > 0, no division by zero occurs.
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∃ r : Std.I64, subarrays_div_by_k nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∃ r : Std.I64, subarrays_div_by_k nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n*(n+1)/2, where n = len(nums).
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) * ((nums.val.length : ℤ) + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) * ((nums.val.length : ℤ) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, r is at least the number of indices i such that 0 <= i < len(nums) and k divides nums[i].
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      (countElemsDivByK (vals nums.val) k.val : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      (countElemsDivByK (vals nums.val) k.val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = n*(n+1)/2 if and only if for every index i with 0 <= i < len(nums), k divides nums[i], where n = len(nums).
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      (r.val = (nums.val.length : ℤ) * ((nums.val.length : ℤ) + 1) / 2 ↔
        ∀ i : ℕ, i < nums.val.length → k.val ∣ elemAt nums.val i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      (r.val = (nums.val.length : ℤ) * ((nums.val.length : ℤ) + 1) / 2 ↔
        ∀ i : ℕ, i < nums.val.length → k.val ∣ elemAt nums.val i)) := by
  sorry

/-- Whenever the function returns a result r, r equals C(nums_rev, k), where n = len(nums), nums_rev is defined by nums_rev[i] = nums[n-1-i] for 0 <= i < n, and C is the count from spec_1: the number of pairs (i,j) with 0 <= i <= j < n and k divides Σ_{t=i}^{j} nums_rev[t].
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals (nums.val.reverse)) k.val : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals (nums.val.reverse)) k.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r equals C(nums_neg, k), where nums_neg[i] = -nums[i] for 0 <= i < len(nums), and C is the count from spec_1.
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK ((vals nums.val).map (fun x => -x)) k.val : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK ((vals nums.val).map (fun x => -x)) k.val : ℤ)) := by
  sorry

/-- For every integer array nums' with len(nums') = len(nums) such that k divides (nums'[i] - nums[i]) for every i with 0 <= i < len(nums), whenever the function returns a result r, r equals C(nums', k), where C is the count from spec_1.
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_8 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000)
    (hlen' : nums'.val.length = nums.val.length)
    (hdvd : ∀ i : ℕ, i < nums.val.length → k.val ∣ elemAt nums'.val i - elemAt nums.val i) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals nums'.val) k.val : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000)
    (hlen' : nums'.val.length = nums.val.length)
    (hdvd : ∀ i : ℕ, i < nums.val.length → k.val ∣ elemAt nums'.val i - elemAt nums.val i), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countDivByK (vals nums'.val) k.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(nums) and define prefix sums P[0] = 0 and P[t] = Σ_{u=0}^{t-1} nums[u] for 1 <= t <= n. For each integer a with 0 <= a < k, let c[a] be the number of indices t with 0 <= t <= n and k divides (P[t] - a). Then r = Σ_{a=0}^{k-1} c[a]*(c[a]-1)/2.
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (residueSum (vals nums.val) k.val : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (residueSum (vals nums.val) k.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of pairs (i,j) with 0 <= i <= j < len(nums) and Σ_{t=i}^{j} nums[t] = 0.
  Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000; 1 <= k <= 10000; Σ_{i=0}^{len(nums)-1} |nums[i]| < k. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000)
    (hsmall : (absSum (vals nums.val) : ℤ) < k.val) :
    ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countZeroSum (vals nums.val) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
    (hbound : ∀ i : ℕ, i < nums.val.length →
      -10000 ≤ elemAt nums.val i ∧ elemAt nums.val i ≤ 10000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10000)
    (hsmall : (absSum (vals nums.val) : ℤ) < k.val), ∀ r : Std.I64, subarrays_div_by_k nums k = ok r →
      r.val = (countZeroSum (vals nums.val) : ℤ)) := by
  sorry

end AegisSpec.SubarraysDivByK
