import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `apply-operations-on-array-to-maximize-sum-of-squares`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSum

def M : ℤ := 1000000007

def bitWidth : ℕ := 63

def elems (nums : Slice I64) : List ℕ := nums.val.map fun v => v.val.toNat

def bitCount (nums : List ℕ) (b : ℕ) : ℕ := nums.countP fun v => v.testBit b

def xval (nums : List ℕ) (i : ℕ) : ℕ :=
  ∑ b ∈ Finset.range bitWidth, if i < bitCount nums b then 2 ^ b else 0

def xList (nums : List ℕ) (k : ℕ) : List ℕ := (List.range k).map fun i => xval nums i

def Sval (nums : List ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (xval nums i) ^ 2

def bitSumMin (nums : List ℕ) (k : ℕ) : ℕ :=
  ∑ b ∈ Finset.range bitWidth, min (bitCount nums b) k * 2 ^ b

def maxBitCount (nums : List ℕ) : ℕ :=
  (List.range bitWidth).foldr (fun b acc => max (bitCount nums b) acc) 0

def orAll (nums : List ℕ) : ℕ := nums.foldr Nat.lor 0

def sumSq (nums : List ℕ) : ℕ := (nums.map fun v => v ^ 2).sum

def descSort (nums : List ℕ) : List ℕ := nums.insertionSort fun a b : ℕ => a ≥ b

def topSqSum (nums : List ℕ) (k : ℕ) : ℕ := (((descSort nums).take k).map fun v => v ^ 2).sum

inductive AndOrStep : List ℕ → List ℕ → Prop where
  | and (l : List ℕ) (i j : ℕ) (hi : i < l.length) (hj : j < l.length) :
      AndOrStep l (l.set i (Nat.land (l.getD i 0) (l.getD j 0)))
  | or (l : List ℕ) (i j : ℕ) (hi : i < l.length) (hj : j < l.length) :
      AndOrStep l (l.set i (Nat.lor (l.getD i 0) (l.getD j 0)))

def Reachable (l l' : List ℕ) : Prop := Relation.ReflTransGen AndOrStep l l'

def selSumSq (A : List ℕ) (idx : List ℕ) (hb : ∀ i ∈ idx, i < A.length) : ℕ :=
  (idx.attach.map fun p => (A.get ⟨p.1, hb p.1 p.2⟩) ^ 2).sum

/-- The function returns a result r such that r = S(k) mod M.
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Let M = 10^9 + 7. For each b >= 0, let c_b be the number of indices i with 0 <= i < n such that the b-th bit of nums[i] is 1. For each i >= 0, let x_i = sum_{b >= 0, c_b > i} 2^b. Let S(k) = sum_{i=0}^{k-1} (x_i)^2. -/
theorem spec_1 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000) :
    ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = (Sval (elems nums) k.val.toNat : ℤ) % M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000), ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = (Sval (elems nums) k.val.toNat : ℤ) % M) := by
  sorry

/-- The function returns a result r and 0 <= r < M.
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Let M = 10^9 + 7. For each b >= 0, let c_b be the number of indices i with 0 <= i < n such that the b-th bit of nums[i] is 1. For each i >= 0, let x_i = sum_{b >= 0, c_b > i} 2^b. Let S(k) = sum_{i=0}^{k-1} (x_i)^2. -/
theorem spec_2 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000) :
    ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧ 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000), ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧ 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Let M = 10^9 + 7. For each b >= 0, let c_b be the number of indices i with 0 <= i < n such that the b-th bit of nums[i] is 1. For each i >= 0, let x_i = sum_{b >= 0, c_b > i} 2^b. Let S(k) = sum_{i=0}^{k-1} (x_i)^2. -/
theorem spec_3 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000) :
    ∃ r, Aegis.MaxSum.max_sum nums k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000), ∃ r, Aegis.MaxSum.max_sum nums k = ok r) := by
  sorry

/-- The function returns a result r and r = ( (bitwise OR of all elements of nums) ^ 2 ) mod M.
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Assume k = 1. Let M = 10^9 + 7. -/
theorem spec_4 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hk : k.val = 1) :
    ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = ((orAll (elems nums)) ^ 2 : ℕ) % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hk : k.val = 1), ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = ((orAll (elems nums)) ^ 2 : ℕ) % M) := by
  sorry

/-- The function returns a result r and r = (k * v^2) mod M.
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Assume there exists an integer v such that for every i with 0 <= i < n, nums[i] = v. Let M = 10^9 + 7. -/
theorem spec_5 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (v : ℕ) (hv : ∀ x ∈ elems nums, x = v) :
    ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = (k.val * (v : ℤ) ^ 2) % M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (v : ℕ) (hv : ∀ x ∈ elems nums, x = v), ∃ r, Aegis.MaxSum.max_sum nums k = ok r ∧
      r.val = (k.val * (v : ℤ) ^ 2) % M) := by
  sorry

/-- max_sum(nums, k) = max_sum(nums', k).
  Preconditions: Let n = len(nums) = len(nums'). Assume 1 <= k <= n. Assume for every i with 0 <= i < n, 1 <= nums[i] <= 10^9 and 1 <= nums'[i] <= 10^9. Assume nums' is a permutation of nums. -/
theorem spec_6 (nums nums' : Slice I64) (k : I64) (n : ℕ)
    (hn : n = nums.val.length) (hn' : n = nums'.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hrange' : ∀ v ∈ nums'.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hperm : nums.val.Perm nums'.val) :
    Aegis.MaxSum.max_sum nums k = Aegis.MaxSum.max_sum nums' k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64) (n : ℕ)
    (hn : n = nums.val.length) (hn' : n = nums'.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hrange' : ∀ v ∈ nums'.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (hperm : nums.val.Perm nums'.val), Aegis.MaxSum.max_sum nums k = Aegis.MaxSum.max_sum nums' k) := by
  sorry

/-- Let r1 be the result returned for k1 and r2 the result returned for k2. Then r1 = S(k1) mod M, r2 = S(k2) mod M, and S(k1) <= S(k2).
  Preconditions: Let n = len(nums). Assume 1 <= k1 <= k2 <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Let M = 10^9 + 7. For each b >= 0, let c_b be the number of indices i with 0 <= i < n such that the b-th bit of nums[i] is 1. For each i >= 0, let x_i = sum_{b >= 0, c_b > i} 2^b. Let S(k) = sum_{i=0}^{k-1} (x_i)^2. -/
theorem spec_7 (nums : Slice I64) (k1 k2 : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2n : k2.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000) :
    ∃ r1 r2, Aegis.MaxSum.max_sum nums k1 = ok r1 ∧
      Aegis.MaxSum.max_sum nums k2 = ok r2 ∧
      r1.val = (Sval (elems nums) k1.val.toNat : ℤ) % M ∧
      r2.val = (Sval (elems nums) k2.val.toNat : ℤ) % M ∧
      Sval (elems nums) k1.val.toNat ≤ Sval (elems nums) k2.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k1 k2 : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2n : k2.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000), ∃ r1 r2, Aegis.MaxSum.max_sum nums k1 = ok r1 ∧
      Aegis.MaxSum.max_sum nums k2 = ok r2 ∧
      r1.val = (Sval (elems nums) k1.val.toNat : ℤ) % M ∧
      r2.val = (Sval (elems nums) k2.val.toNat : ℤ) % M ∧
      Sval (elems nums) k1.val.toNat ≤ Sval (elems nums) k2.val.toNat) := by
  sorry

/-- max_sum(nums, k) = max_sum(nums, K).
  Preconditions: Let n = len(nums). Assume 1 <= k <= n and for every i with 0 <= i < n, 1 <= nums[i] <= 10^9. Let M = 10^9 + 7. For each b >= 0, let c_b be the number of indices i with 0 <= i < n such that the b-th bit of nums[i] is 1. For each i >= 0, let x_i = sum_{b >= 0, c_b > i} 2^b. Let S(k) = sum_{i=0}^{k-1} (x_i)^2. Let K = max_{b >= 0} c_b. Assume k >= K. -/
theorem spec_8 (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (K : I64) (hK : K.val = (maxBitCount (elems nums) : ℤ)) (hkK : K.val ≤ k.val) :
    Aegis.MaxSum.max_sum nums k = Aegis.MaxSum.max_sum nums K := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (n : ℕ) (hn : n = nums.val.length)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (n : ℤ))
    (hrange : ∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 1000000000)
    (K : I64) (hK : K.val = (maxBitCount (elems nums) : ℤ)) (hkK : K.val ≤ k.val), Aegis.MaxSum.max_sum nums k = Aegis.MaxSum.max_sum nums K) := by
  sorry

end AegisSpec.MaxSum
