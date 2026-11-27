import Aegis.MinimizeArrayValue.Code.Funs

/-!
# Specifications of `Aegis.MinimizeArrayValue.minimize_array_value`

LeetCode problem `minimize-maximum-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimizeArrayValue

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def total (l : List ℤ) : ℤ := l.sum

def listMax : List ℤ → ℤ
  | [] => 0
  | a :: l => l.foldr max a

def prefixSum (l : List ℤ) (k : ℕ) : ℤ := (l.take k).sum

def ceilDiv (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))

def maxAvg (l : List ℤ) : ℤ :=
  listMax ((List.range l.length).map (fun k => ceilDiv (prefixSum l (k + 1)) (k + 1)))

def Step (cur next : List ℤ) : Prop :=
  ∃ (l₁ : List ℤ) (x y : ℤ) (l₂ : List ℤ),
    0 < y ∧ cur = l₁ ++ x :: y :: l₂ ∧ next = l₁ ++ (x + 1) :: (y - 1) :: l₂

def Reachable (cur fin : List ℤ) : Prop := Relation.ReflTransGen Step cur fin

/-- Whenever the function returns a result r, r = max over integers k with 1 <= k <= n of ceil(S_k / k), where S_k = sum of nums[j] for 0 <= j < k, and ceil(a/b) for positive b is the least integer c such that b*c >= a.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. All indices are 0-based. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) :
    r.val = maxAvg (vals nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r), r.val = maxAvg (vals nums)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MinimizeArrayValue.minimize_array_value nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : Std.I64, Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 1 <= k <= n, k*r >= S_k, where S_k = sum of nums[j] for 0 <= j < k.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) :
    ∀ k : ℕ, 1 ≤ k → k ≤ nums.val.length → prefixSum (vals nums) k ≤ (k : ℤ) * r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r), ∀ k : ℕ, 1 ≤ k → k ≤ nums.val.length → prefixSum (vals nums) k ≤ (k : ℤ) * r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= max over i with 0 <= i < n of nums[i].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) :
    r.val ≤ listMax (vals nums) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r), r.val ≤ listMax (vals nums)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence (possibly empty) of arrays current_0, ..., current_m of length n with current_0 = nums such that for each t with 0 <= t < m, current_{t+1} is obtained from current_t by choosing an index i with 1 <= i < n and current_t[i] > 0, setting current_{t+1}[i] = current_t[i] - 1, current_{t+1}[i-1] = current_t[i-1] + 1, and current_{t+1}[j] = current_t[j] for all other j, and such that current_m[i] <= r for every i with 0 <= i < n.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) :
    ∃ cur : List ℤ, Reachable (vals nums) cur ∧ ∀ x ∈ cur, x ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r), ∃ cur : List ℤ, Reachable (vals nums) cur ∧ ∀ x ∈ cur, x ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer M with M < r, there is no finite sequence of allowed operations transforming nums into an array v of length n with v[i] <= M for every i with 0 <= i < n, where an allowed operation chooses i with 1 <= i < n and current[i] > 0, decrements current[i], and increments current[i-1].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r) :
    ∀ M : ℤ, M < r.val → ¬ ∃ v : List ℤ, Reachable (vals nums) v ∧ ∀ x ∈ v, x ≤ M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r), ∀ M : ℤ, M < r.val → ¬ ∃ v : List ℤ, Reachable (vals nums) v ∧ ∀ x ∈ v, x ≤ M) := by
  sorry

/-- Whenever the function returns r on nums and r' on shifted, r' = r + c.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Let c be an integer with 0 <= c and nums[i]+c <= 1000000000 for every i with 0 <= i < n. Let shifted be the array of length n with shifted[i] = nums[i]+c for every i. -/
theorem spec_7 (nums shifted : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hc_nonneg : 0 ≤ c)
    (hc_bound : ∀ x ∈ nums.val, x.val + c ≤ 1000000000)
    (hshifted : vals shifted = (vals nums).map (fun y => y + c))
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r)
    (hres' : Aegis.MinimizeArrayValue.minimize_array_value shifted = ok r') :
    r'.val = r.val + c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums shifted : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hc_nonneg : 0 ≤ c)
    (hc_bound : ∀ x ∈ nums.val, x.val + c ≤ 1000000000)
    (hshifted : vals shifted = (vals nums).map (fun y => y + c))
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r)
    (hres' : Aegis.MinimizeArrayValue.minimize_array_value shifted = ok r'), r'.val = r.val + c) := by
  sorry

/-- Whenever the function returns r on nums and r' on v, r <= r'.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Let v be another slice of length n satisfying the same constraints, and assume v[i] >= nums[i] for every i with 0 <= i < n. -/
theorem spec_8 (nums v : Slice Std.I64) (r r' : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hv_lo : 2 ≤ v.val.length)
    (hv_hi : v.val.length ≤ 100000)
    (hvbounds : ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hdom : List.Forall₂ (fun x y => x.val ≤ y.val) nums.val v.val)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r)
    (hres' : Aegis.MinimizeArrayValue.minimize_array_value v = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums v : Slice Std.I64) (r r' : Std.I64)
    (hn_lo : 2 ≤ nums.val.length)
    (hn_hi : nums.val.length ≤ 100000)
    (hbounds : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hv_lo : 2 ≤ v.val.length)
    (hv_hi : v.val.length ≤ 100000)
    (hvbounds : ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hdom : List.Forall₂ (fun x y => x.val ≤ y.val) nums.val v.val)
    (hres : Aegis.MinimizeArrayValue.minimize_array_value nums = ok r)
    (hres' : Aegis.MinimizeArrayValue.minimize_array_value v = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MinimizeArrayValue
