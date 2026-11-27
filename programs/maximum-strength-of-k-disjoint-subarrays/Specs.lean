import Aegis.MaximumStrength.Code.Funs

/-!
# Specifications of `Aegis.MaximumStrength.maximum_strength`

LeetCode problem `maximum-strength-of-k-disjoint-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumStrength

def len (nums : Slice I64) : Nat := nums.val.length

def subarraySum (nums : Slice I64) (l r : Nat) : Int :=
  (((nums.val.drop l).take (r + 1 - l)).map fun x => x.val).sum

def coef (k i : Nat) : Int :=
  if i % 2 = 1 then ((k : Int) - (i : Int) + 1) else -((k : Int) - (i : Int) + 1)

def Feasible (nums : Slice I64) (k : Nat) (l r : Nat → Nat) : Prop :=
  (∀ i, 1 ≤ i → i ≤ k → l i ≤ r i ∧ r i < len nums) ∧
    (∀ i, 1 ≤ i → i < k → r i < l (i + 1))

def strength (nums : Slice I64) (k : Nat) (l r : Nat → Nat) : Int :=
  ((List.range k).map fun j => coef k (j + 1) * subarraySum nums (l (j + 1)) (r (j + 1))).sum

def IsMaxStrength (nums : Slice I64) (k : Nat) (r : Int) : Prop :=
  (∀ l rr, Feasible nums k l rr → strength nums k l rr ≤ r) ∧
    ∃ l rr, Feasible nums k l rr ∧ strength nums k l rr = r

def maxAbs (nums : Slice I64) : Nat :=
  (nums.val.map fun x => x.val.natAbs).foldr max 0

def smulList (c : Int) (nums : Slice I64)
    (h : ∀ x ∈ nums.val, -10 ^ 9 ≤ c * x.val ∧ c * x.val ≤ 10 ^ 9) : List I64 :=
  nums.val.attach.map fun x =>
    IScalar.ofInt (c * x.1.val) (by
      obtain ⟨h1, h2⟩ := h x.1 x.2
      have hmin : IScalar.cMin .I64 ≤ (-10 ^ 9 : Int) := by decide
      have hmax : (10 ^ 9 : Int) ≤ IScalar.cMax .I64 := by decide
      exact ⟨le_trans hmin h1, le_trans h2 hmax⟩)

def smul (c : Int) (nums : Slice I64)
    (h : ∀ x ∈ nums.val, -10 ^ 9 ≤ c * x.val ∧ c * x.val ≤ 10 ^ 9) : Slice I64 :=
  Slice.from (smulList c nums h) (by
    have hlen : (smulList c nums h).length = nums.val.length := by simp [smulList]
    rw [hlen]
    simp)

/-- Define a feasible selection to be any sequence of k pairs (l_1,r_1),...,(l_k,r_k) such that 0 <= l_i <= r_i < n for every i and r_i < l_{i+1} for every 1 <= i < k; the i-th subarray is the nonempty contiguous segment nums[l_i..r_i]. For such a selection, let c_i = (-1)^(i+1) * (k - i + 1) and let strength = sum_{i=1}^{k} c_i * (sum_{t=l_i}^{r_i} nums[t]). Then maximum_strength(nums,k) returns a result r and r = max { strength(S) : S is a feasible selection }. The maximum is over all feasible selections; selected subarrays need not cover the whole array.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6) :
    ∃ r, Aegis.MaximumStrength.maximum_strength nums k = ok r ∧
      IsMaxStrength nums k.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6), ∃ r, Aegis.MaximumStrength.maximum_strength nums k = ok r ∧
      IsMaxStrength nums k.val.toNat r.val) := by
  sorry

/-- For every input satisfying the preconditions, maximum_strength(nums,k) does not fail: it returns some result r without overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6) :
    ∃ r, Aegis.MaximumStrength.maximum_strength nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6), ∃ r, Aegis.MaximumStrength.maximum_strength nums k = ok r) := by
  sorry

/-- Let r be the result returned by maximum_strength(nums,k). For every sequence (l_1,r_1),...,(l_k,r_k) with 0 <= l_i <= r_i < n and r_i < l_{i+1} for 1 <= i < k, define strength = sum_{i=1}^{k} (-1)^(i+1) * (k - i + 1) * (sum_{t=l_i}^{r_i} nums[t]). Then strength <= r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6) :
    ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      ∀ l rr, Feasible nums k.val.toNat l rr → strength nums k.val.toNat l rr ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6), ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      ∀ l rr, Feasible nums k.val.toNat l rr → strength nums k.val.toNat l rr ≤ r.val) := by
  sorry

/-- Let r be the result returned by maximum_strength(nums,k). There exists a sequence (l_1,r_1),...,(l_k,r_k) with 0 <= l_i <= r_i < n and r_i < l_{i+1} for 1 <= i < k such that, with strength = sum_{i=1}^{k} (-1)^(i+1) * (k - i + 1) * (sum_{t=l_i}^{r_i} nums[t]), we have strength = r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6) :
    ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      ∃ l rr, Feasible nums k.val.toNat l rr ∧ strength nums k.val.toNat l rr = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6), ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      ∃ l rr, Feasible nums k.val.toNat l rr ∧ strength nums k.val.toNat l rr = r.val) := by
  sorry

/-- Whenever maximum_strength(nums,k) returns r and maximum_strength(c*nums,k) returns r_c, we have r_c = c * r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. Let c be a positive integer such that -10^9 <= c*nums[i] <= 10^9 for every 0 <= i < n; let c*nums denote the array with entries c*nums[i]. -/
theorem spec_5 (nums : Slice I64) (k : I64) (c : Int)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6)
    (hc_pos : 1 ≤ c)
    (hc_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ c * x.val ∧ c * x.val ≤ 10 ^ 9) :
    ∀ r r_c, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      Aegis.MaximumStrength.maximum_strength (smul c nums hc_bnd) k = ok r_c →
        r_c.val = c * r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (c : Int)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6)
    (hc_pos : 1 ≤ c)
    (hc_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ c * x.val ∧ c * x.val ≤ 10 ^ 9), ∀ r r_c, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      Aegis.MaximumStrength.maximum_strength (smul c nums hc_bnd) k = ok r_c →
        r_c.val = c * r.val) := by
  sorry

/-- Let n = len(nums), let M = max { |nums[i]| : 0 <= i < n }, and let r be the result returned by maximum_strength(nums,k). Then -(k * n * M) <= r <= k * n * M.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 10^4, -10^9 <= nums[i] <= 10^9 for every 0 <= i < n, 1 <= k <= n, k is odd, and n*k <= 10^6. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6) :
    ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      -((k.val.toNat : Int) * (len nums : Int) * (maxAbs nums : Int)) ≤ r.val ∧
        r.val ≤ (k.val.toNat : Int) * (len nums : Int) * (maxAbs nums : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 10 ^ 4)
    (hn_bnd : ∀ x ∈ nums.val, -10 ^ 9 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (len nums : Int))
    (hk_odd : k.val % 2 = 1)
    (hk_prod : (len nums : Int) * k.val ≤ 10 ^ 6), ∀ r, Aegis.MaximumStrength.maximum_strength nums k = ok r →
      -((k.val.toNat : Int) * (len nums : Int) * (maxAbs nums : Int)) ≤ r.val ∧
        r.val ≤ (k.val.toNat : Int) * (len nums : Int) * (maxAbs nums : Int)) := by
  sorry

end AegisSpec.MaximumStrength
