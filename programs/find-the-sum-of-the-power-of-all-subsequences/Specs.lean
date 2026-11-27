import Aegis.SumOfPower.Code.Funs

/-!
# Specifications of `Aegis.SumOfPower.sum_of_power`

LeetCode problem `find-the-sum-of-the-power-of-all-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumOfPower

def MOD : Int := 1000000007

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elemAt (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def total (l : List Int) : Int := l.sum

def subsetSum (l : List Int) (B : Finset (Fin l.length)) : Int := ∑ i ∈ B, l.get i

def subsetsWithSum (l : List Int) (k : Int) : Finset (Finset (Fin l.length)) :=
  (Finset.univ : Finset (Fin l.length)).powerset.filter (fun B => subsetSum l B = k)

def weightedSubsetSum (l : List Int) (k : Int) : Int :=
  (subsetsWithSum l k).sum (fun B => (2 : Int) ^ (l.length - B.card))

def problemSum (nums : Slice Std.I64) (k : Std.I64) : Int := weightedSubsetSum (vals nums) k.val

def countEq (l : List Int) (v : Int) : Nat := l.countP (fun x => decide (x = v))

def countGt (l : List Int) (k : Int) : Nat := l.countP (fun x => decide (k < x))

def binomTerm (n : Nat) (k : Int) : Int :=
  if 0 ≤ k ∧ k ≤ (n : Int) then (Nat.choose n k.toNat : Int) * (2 : Int) ^ (n - k.toNat) else 0

def binomTermDiv (n : Nat) (k v : Int) : Int :=
  if v ∣ k then binomTerm n (k / v) else 0

def Constraints (nums : Slice Std.I64) (k : Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100 ∧ 1 ≤ k.val ∧ k.val ≤ 100 ∧
    ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000

/-- Whenever the function returns a result r, we have 0 ≤ r < 10^9+7 and r ≡ S (mod 10^9+7), where S = sum over all subsets B ⊆ {0,...,n-1} with sum_{i in B} nums[i] = k of 2^(n - |B|). If there is no such subset B, then S = 0.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
    ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      0 ≤ r.val ∧ r.val < MOD ∧ Int.ModEq MOD r.val (problemSum nums k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      0 ≤ r.val ∧ r.val < MOD ∧ Int.ModEq MOD r.val (problemSum nums k)) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, or panic).
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
    ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. Additionally, k > sum(nums), where sum(nums) = sum_{i=0}^{n-1} nums[i]. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : total (vals nums) < k.val) :
    ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : total (vals nums) < k.val), ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. Additionally, k = sum(nums). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : k.val = total (vals nums)) :
    ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : k.val = total (vals nums)), ∃ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and (r = 1 if nums[0] = k, else r = 0).
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. Additionally, n = 1. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hn : nums.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = if elemAt nums 0 = k.val then 1 else 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hn : nums.val.length = 1), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ r.val = if elemAt nums 0 = k.val then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, we have 0 ≤ r < 10^9+7 and r ≡ 2^(n - |B|) (mod 10^9+7), where B is the unique subset with sum k.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. Additionally, there exists a unique subset B ⊆ {0,...,n-1} such that sum_{i in B} nums[i] = k. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (huniq : ∃! B : Finset (Fin (vals nums).length), subsetSum (vals nums) B = k.val) :
    ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      0 ≤ r.val ∧ r.val < MOD ∧
        ∀ B : Finset (Fin (vals nums).length), subsetSum (vals nums) B = k.val →
          Int.ModEq MOD r.val ((2 : Int) ^ ((vals nums).length - B.card)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (huniq : ∃! B : Finset (Fin (vals nums).length), subsetSum (vals nums) B = k.val), ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      0 ≤ r.val ∧ r.val < MOD ∧
        ∀ B : Finset (Fin (vals nums).length), subsetSum (vals nums) B = k.val →
          Int.ModEq MOD r.val ((2 : Int) ^ ((vals nums).length - B.card))) := by
  sorry

/-- Let n = len(nums). The function returns a result r with 0 <= r < 10^9+7 and r ≡ (if k <= n then binom(n,k) * 2^(n-k) else 0) (mod 10^9+7), where binom(n,k) is the usual binomial coefficient.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 <= n <= 100, 1 <= k <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^4. Additionally, for every i with 0 <= i < n, nums[i] = 1. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hone : ∀ x ∈ nums.val, x.val = 1) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (binomTerm (vals nums).length k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hone : ∀ x ∈ nums.val, x.val = 1), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (binomTerm (vals nums).length k.val)) := by
  sorry

/-- The function returns a result r and r ≡ c * 2^(n-1) (mod 10^9+7), where c is the number of indices i with 0 ≤ i < n and nums[i] = 1.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. Additionally, k = 1. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : k.val = 1) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧
        Int.ModEq MOD r.val ((countEq (vals nums) 1 : Int) * (2 : Int) ^ ((vals nums).length - 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hk : k.val = 1), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧
        Int.ModEq MOD r.val ((countEq (vals nums) 1 : Int) * (2 : Int) ^ ((vals nums).length - 1))) := by
  sorry

/-- The value r depends only on the multiset of elements in nums. Precisely, for any permutation π of {0,...,n-1}, if nums' is the array defined by nums'[i] = nums[π(i)] for all i, then the result returned for nums' equals r.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. -/
theorem spec_9 (nums nums' : Slice Std.I64) (k : Std.I64)
    (h : Constraints nums k) (h' : Constraints nums' k)
    (hperm : List.Perm (vals nums) (vals nums')) :
    ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      ∀ r' : Std.I64, Aegis.SumOfPower.sum_of_power nums' k = ok r' → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (h : Constraints nums k) (h' : Constraints nums' k)
    (hperm : List.Perm (vals nums) (vals nums')), ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      ∀ r' : Std.I64, Aegis.SumOfPower.sum_of_power nums' k = ok r' → r'.val = r.val) := by
  sorry

/-- Let m be the number of indices i with nums[i] > k, and let nums' be the subsequence of nums consisting of all elements ≤ k (in their original order). Let r' be the result the function would return for nums' with the same k. Then r ≡ 2^m * r' (mod 10^9+7) and 0 ≤ r < 10^9+7.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. -/
theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hsub : vals nums' = (vals nums).filter (fun v => decide (v ≤ k.val))) :
    ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      ∀ r' : Std.I64, Aegis.SumOfPower.sum_of_power nums' k = ok r' →
        0 ≤ r.val ∧ r.val < MOD ∧
          Int.ModEq MOD r.val ((2 : Int) ^ countGt (vals nums) k.val * r'.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hsub : vals nums' = (vals nums).filter (fun v => decide (v ≤ k.val))), ∀ r : Std.I64, Aegis.SumOfPower.sum_of_power nums k = ok r →
      ∀ r' : Std.I64, Aegis.SumOfPower.sum_of_power nums' k = ok r' →
        0 ≤ r.val ∧ r.val < MOD ∧
          Int.ModEq MOD r.val ((2 : Int) ^ countGt (vals nums) k.val * r'.val)) := by
  sorry

def doubleCount (l : List Int) (k : Int) : Int :=
  ((Finset.univ : Finset (Fin l.length)).powerset).sum
    (fun A => (((subsetsWithSum l k).filter (fun B => B ⊆ A)).card : Int))

/-- The function returns a result r, and r ≡ P (mod 10^9+7) with 0 ≤ r < 10^9+7, where P is the sum over all subsets A ⊆ {0,...,n-1} of the number of subsets B ⊆ A such that sum_{i in B} nums[i] = k.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 ≤ n ≤ 100, 1 ≤ k ≤ 100, and for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 10^4. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (doubleCount (vals nums) k.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (doubleCount (vals nums) k.val)) := by
  sorry

/-- The function returns a result r with 0 <= r < 10^9+7 and r ≡ (if v divides k and k/v <= n then binom(n, k/v) * 2^(n - k/v) else 0) (mod 10^9+7), where binom is the usual binomial coefficient.
  Preconditions: Let n = len(nums). The problem constraints hold: 1 <= n <= 100, 1 <= k <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^4. Additionally, there is a positive integer v such that for every i with 0 <= i < n, nums[i] = v. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (v : Int) (hv : 0 < v) (hall : ∀ x ∈ nums.val, x.val = v) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (binomTermDiv (vals nums).length k.val v) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (v : Int) (hv : 0 < v) (hall : ∀ x ∈ nums.val, x.val = v), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val (binomTermDiv (vals nums).length k.val v)) := by
  sorry

/-- The function returns a result r with 0 <= r < 10^9+7 and r ≡ c * 2^(n-1) (mod 10^9+7).
  Preconditions: Let n = len(nums). The problem constraints hold: 1 <= n <= 100, 1 <= k <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^4. Additionally, every nums[i] is either k or greater than k; let c = |{i : nums[i] = k}|. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hall : ∀ x ∈ nums.val, x.val = k.val ∨ k.val < x.val) :
    ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val
          ((countEq (vals nums) k.val : Int) * (2 : Int) ^ ((vals nums).length - 1)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (h : Constraints nums k)
    (hall : ∀ x ∈ nums.val, x.val = k.val ∨ k.val < x.val), ∃ r : Std.I64,
      Aegis.SumOfPower.sum_of_power nums k = ok r ∧ 0 ≤ r.val ∧ r.val < MOD ∧
        Int.ModEq MOD r.val
          ((countEq (vals nums) k.val : Int) * (2 : Int) ^ ((vals nums).length - 1))) := by
  sorry

end AegisSpec.SumOfPower
