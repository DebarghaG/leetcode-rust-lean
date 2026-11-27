import Aegis.SumOfPower.Code.Funs

/-!
# Specifications of `Aegis.SumOfPower.sum_of_power`

LeetCode problem `power-of-heroes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfPower

  def MOD : ℤ := 1000000007

  def getv (nums : Slice I64) (i : ℕ) : ℤ :=
    ((nums.val[i]?).map (fun (x : I64) => x.val)).getD 0

  def maxval (nums : Slice I64) {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : ℤ :=
    S.sup' hS (fun i => getv nums (i : ℕ))

  def minval (nums : Slice I64) {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : ℤ :=
    S.inf' hS (fun i => getv nums (i : ℕ))

  def power (nums : Slice I64) {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : ℤ :=
    maxval nums S hS * maxval nums S hS * minval nums S hS

  def Total (nums : Slice I64) : ℤ :=
    ∑ S : { S : Finset (Fin nums.val.length) // S.Nonempty }, power nums S.1 S.2

  def extraTotal (nums : Slice I64) (v : ℤ) : ℤ :=
    v * v * v +
      ∑ S : { S : Finset (Fin nums.val.length) // S.Nonempty },
        max v (maxval nums S.1 S.2) * max v (maxval nums S.1 S.2) * min v (minval nums S.1 S.2)

  /-- Whenever sum_of_power(nums) returns a result r, r is the least non-negative residue modulo MOD = 1000000007 of Total(nums), where Total(nums) is defined as follows. For each subset S of the index set {0,1,...,n-1} with S nonempty, let maxval(S) = max { nums[i] | i in S } and minval(S) = min { nums[i] | i in S }, and let power(S) = maxval(S) * maxval(S) * minval(S). Then Total(nums) is the sum of power(S) over all nonempty subsets S. Each subset S is counted once, and subsets are sets of indices, so two equal values at different indices correspond to different subsets.
    Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000, and for every i with 0 <= i < n, nums[i] is an integer with 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice I64) (n : ℕ)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
      (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r) :
      r.val = Total nums % MOD := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
        (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r), r.val = Total nums % MOD) := by
    sorry

  /-- For every nums satisfying the preconditions, sum_of_power(nums) returns a successful result: there exists an i64 value r such that sum_of_power(nums) returns r. It does not overflow, go out of bounds, panic, or otherwise fail.
    Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000, and for every i with 0 <= i < n, nums[i] is an integer with 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice I64) (n : ℕ)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000) :
      ∃ r : I64, Aegis.SumOfPower.sum_of_power nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000), ∃ r : I64, Aegis.SumOfPower.sum_of_power nums = ok r) := by
    sorry

  /-- Whenever sum_of_power(nums) returns a result r, 0 <= r < 1000000007.
    Preconditions: Let n = len(nums). n is an integer with 1 <= n <= 100000, and for every i with 0 <= i < n, nums[i] is an integer with 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice I64) (n : ℕ)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
      (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r) :
      0 ≤ r.val ∧ r.val < MOD := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
        (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r), 0 ≤ r.val ∧ r.val < MOD) := by
    sorry

  /-- Whenever sum_of_power(nums) returns a result r, r = (((2^n - 1) mod 1000000007) * ((v * v * v) mod 1000000007)) mod 1000000007. Here 2^n - 1 is the exact integer count of nonempty subsets of the n indices, and the final modulo returns the least non-negative residue.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and there exists an integer v with 1 <= v <= 1000000000 such that nums[i] = v for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice I64) (n : ℕ) (v : ℤ)
      (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
      (hconst : ∀ i, i < n → getv nums i = v)
      (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r) :
      r.val = (((2 : ℤ) ^ n - 1) % MOD * ((v * v * v) % MOD)) % MOD := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ) (v : ℤ)
        (hn : n = nums.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
        (hconst : ∀ i, i < n → getv nums i = v)
        (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r), r.val = (((2 : ℤ) ^ n - 1) % MOD * ((v * v * v) % MOD)) % MOD) := by
    sorry

  /-- Whenever sum_of_power(nums) returns a result r, r = (a * a * a + b * b * b + max(a, b) * max(a, b) * min(a, b)) mod 1000000007, where the final modulo returns the least non-negative residue.
    Preconditions: len(nums) = 2. Let a = nums[0] and b = nums[1]. We have 1 <= a <= 1000000000 and 1 <= b <= 1000000000. -/
  theorem spec_5 (nums : Slice I64) (a b : ℤ)
      (hlen : nums.val.length = 2)
      (ha : a = getv nums 0) (hb : b = getv nums 1)
      (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000) (hb1 : 1 ≤ b) (hb2 : b ≤ 1000000000)
      (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r) :
      r.val = (a * a * a + b * b * b + max a b * max a b * min a b) % MOD := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (a b : ℤ)
        (hlen : nums.val.length = 2)
        (ha : a = getv nums 0) (hb : b = getv nums 1)
        (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000) (hb1 : 1 ≤ b) (hb2 : b ≤ 1000000000)
        (r : I64) (hr : Aegis.SumOfPower.sum_of_power nums = ok r), r.val = (a * a * a + b * b * b + max a b * max a b * min a b) % MOD) := by
    sorry

  /-- Whenever sum_of_power(nums) returns a result r and sum_of_power(nums2) returns a result r2, we have r = r2.
    Preconditions: Let nums and nums2 be two valid input arrays of the same length n: 1 <= n <= 100000, and every entry of each array is between 1 and 1000000000. Suppose there is a bijection sigma on {0,1,...,n-1} such that nums2[j] = nums[sigma(j)] for every j with 0 <= j < n. -/
  theorem spec_6 (nums nums2 : Slice I64) (n : ℕ)
      (hn : n = nums.val.length) (hn' : n = nums2.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
      (hbound2 : ∀ i, i < n → 1 ≤ getv nums2 i ∧ getv nums2 i ≤ 1000000000)
      (σ : Equiv.Perm (Fin n))
      (hσ : ∀ j : Fin n, getv nums2 (j : ℕ) = getv nums (σ j : ℕ))
      (r r2 : I64)
      (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
      (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums2 : Slice I64) (n : ℕ)
        (hn : n = nums.val.length) (hn' : n = nums2.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
        (hbound2 : ∀ i, i < n → 1 ≤ getv nums2 i ∧ getv nums2 i ≤ 1000000000)
        (σ : Equiv.Perm (Fin n))
        (hσ : ∀ j : Fin n, getv nums2 (j : ℕ) = getv nums (σ j : ℕ))
        (r r2 : I64)
        (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
        (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever sum_of_power(nums) returns a result r and sum_of_power(nums2) returns a result r2, r2 = (c^3 * r) mod 1000000007, where c^3 and c^3 * r are exact integers and the final modulo returns the least non-negative residue.
    Preconditions: Let nums be a valid input array of length n. Let c be a positive integer. Let nums2 be the length-n array defined by nums2[i] = c * nums[i] for every i with 0 <= i < n. Assume nums2 is also a valid input: 1 <= n <= 100000 and 1 <= nums2[i] <= 1000000000 for every i. -/
  theorem spec_7 (nums nums2 : Slice I64) (n : ℕ) (c : ℤ)
      (hn : n = nums.val.length) (hn' : n = nums2.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hc : 1 ≤ c)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
      (hscale : ∀ i, i < n → getv nums2 i = c * getv nums i)
      (hbound2 : ∀ i, i < n → 1 ≤ getv nums2 i ∧ getv nums2 i ≤ 1000000000)
      (r r2 : I64)
      (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
      (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2) :
      r2.val = (c ^ 3 * r.val) % MOD := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice I64) (n : ℕ) (c : ℤ)
        (hn : n = nums.val.length) (hn' : n = nums2.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hc : 1 ≤ c)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
        (hscale : ∀ i, i < n → getv nums2 i = c * getv nums i)
        (hbound2 : ∀ i, i < n → 1 ≤ getv nums2 i ∧ getv nums2 i ≤ 1000000000)
        (r r2 : I64)
        (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
        (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2), r2.val = (c ^ 3 * r.val) % MOD) := by
    sorry

  /-- Whenever sum_of_power(nums) returns r and sum_of_power(nums2) returns r2, r2 = (r + (B mod 1000000007)) mod 1000000007, where B = v * v * v + the sum, over all nonempty subsets S of {0,1,...,n-1}, of (max(v, max { nums[i] | i in S })) * (max(v, max { nums[i] | i in S })) * min(v, min { nums[i] | i in S }), and the final modulo returns the least non-negative residue.
    Preconditions: Let nums be a valid input array of length n with 1 <= n <= 100000. Let v be an integer with 1 <= v <= 1000000000, and assume n + 1 <= 100000. Let nums2 be the length-(n+1) array defined by nums2[i] = nums[i] for 0 <= i < n and nums2[n] = v. -/
  theorem spec_8 (nums nums2 : Slice I64) (n : ℕ) (v : ℤ)
      (hn : n = nums.val.length) (hn' : nums2.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn_le : n + 1 ≤ 100000)
      (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
      (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
      (hpre : ∀ i, i < n → getv nums2 i = getv nums i)
      (hlast : getv nums2 n = v)
      (r r2 : I64)
      (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
      (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2) :
      r2.val = (r.val + extraTotal nums v % MOD) % MOD := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice I64) (n : ℕ) (v : ℤ)
        (hn : n = nums.val.length) (hn' : nums2.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn_le : n + 1 ≤ 100000)
        (hbound : ∀ i, i < n → 1 ≤ getv nums i ∧ getv nums i ≤ 1000000000)
        (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
        (hpre : ∀ i, i < n → getv nums2 i = getv nums i)
        (hlast : getv nums2 n = v)
        (r r2 : I64)
        (hr : Aegis.SumOfPower.sum_of_power nums = ok r)
        (hr2 : Aegis.SumOfPower.sum_of_power nums2 = ok r2), r2.val = (r.val + extraTotal nums v % MOD) % MOD) := by
    sorry

  end AegisSpec.SumOfPower
