import Aegis.MaxFrequency.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequency.max_frequency`

LeetCode problem `maximum-frequency-of-an-element-after-performing-operations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxFrequency

def freq (l : List I64) (v : ℤ) : ℤ :=
  ((l.filter (fun x => x.val = v)).length : ℤ)

def windowCount (l : List I64) (k v : ℤ) : ℤ :=
  ((l.filter (fun x => v - k ≤ x.val ∧ x.val ≤ v + k)).length : ℤ)

def IsMaxOver (f : ℤ → ℤ) (x : ℤ) : Prop :=
  (∀ v : ℤ, f v ≤ x) ∧ ∃ v : ℤ, f v = x

def entry (l : List I64) (i : ℕ) : ℤ :=
  match l[i]? with
  | some x => x.val
  | none => 0

def countFn (n : ℕ) (f : ℕ → ℤ) (t : ℤ) : ℤ :=
  (((List.range n).filter (fun i => f i = t)).length : ℤ)

/-- The function returns a result r and r = max over all integers v of min(W(v), E(v) + numOperations), where E(v) = #{i | 0 <= i < n and nums[i] = v} and W(v) = #{i | 0 <= i < n and v - k <= nums[i] <= v + k}. Equivalently, r is the largest number of occurrences of one value in nums after exactly numOperations operations, where each operation selects an index not selected before and adds a delta in [-k, k] to nums at that index.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. All indices are 0-based. -/
theorem spec_1 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver
        (fun v : ℤ =>
          min (windowCount nums.val k.val v) (freq nums.val v + numOperations.val))
        r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver
        (fun v : ℤ =>
          min (windowCount nums.val k.val v) (freq nums.val v + numOperations.val))
        r.val) := by
  sorry

/-- Under these preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_2 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ r : I64, Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ r : I64, Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r) := by
  sorry

/-- The function returns a result r and 1 <= r <= len(nums).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_3 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r >= M, where M = max over all integers v of #{i | 0 <= i < n and nums[i] = v} (the initial maximum frequency).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_4 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      M ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      M ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= M + numOperations, where M = max over all integers v of #{i | 0 <= i < n and nums[i] = v} (the initial maximum frequency).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_5 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val ≤ M + numOperations.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val ≤ M + numOperations.val) := by
  sorry

/-- The function returns a result r and r = M, where M = max over all integers v of #{i | 0 <= i < n and nums[i] = v} (the initial maximum frequency).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n; and numOperations = 0. -/
theorem spec_6 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hzero : numOperations.val = 0) :
    ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val = M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hzero : numOperations.val = 0), ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val = M) := by
  sorry

/-- The function returns a result r and r = max over all integers v of #{i | 0 <= i < n and v - k <= nums[i] <= v + k}.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n; and numOperations = n. -/
theorem spec_7 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hall : numOperations.val = (nums.val.length : ℤ)) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => windowCount nums.val k.val v) r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hall : numOperations.val = (nums.val.length : ℤ)), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => windowCount nums.val k.val v) r.val) := by
  sorry

/-- The function returns a result r and r = len(nums).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n; and there exists an integer c such that nums[i] = c for every i with 0 <= i < n. -/
theorem spec_8 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = c) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      r.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hconst : ∃ c : ℤ, ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = c), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      r.val = (nums.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = min(len(nums), M + numOperations), where M = max over all integers v of #{i | 0 <= i < n and nums[i] = v} (the initial maximum frequency).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n; and k >= (max over 0 <= i < n of nums[i]) - (min over 0 <= i < n of nums[i]). -/
theorem spec_9 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hspread : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      (nums.val[i]).val - (nums.val[j]).val ≤ k.val) :
    ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val = min (nums.val.length : ℤ) (M + numOperations.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ))
    (hspread : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      (nums.val[i]).val - (nums.val[j]).val ≤ k.val), ∃ (r : I64) (M : ℤ),
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      IsMaxOver (fun v : ℤ => freq nums.val v) M ∧
      r.val = min (nums.val.length : ℤ) (M + numOperations.val)) := by
  sorry

/-- For every array nums' of length len(nums) that is a permutation of nums, the result of max_frequency(nums', k, numOperations) equals the result of max_frequency(nums, k, numOperations).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_10 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∀ nums' : Slice I64, nums'.val.Perm nums.val →
      Aegis.MaxFrequency.max_frequency nums' k numOperations =
        Aegis.MaxFrequency.max_frequency nums k numOperations := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∀ nums' : Slice I64, nums'.val.Perm nums.val →
      Aegis.MaxFrequency.max_frequency nums' k numOperations =
        Aegis.MaxFrequency.max_frequency nums k numOperations) := by
  sorry

/-- If r1 is the result of max_frequency(nums, k1, numOperations) and r2 is the result of max_frequency(nums, k2, numOperations), then r1 <= r2.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= numOperations <= n; and let k1 and k2 be integers with 0 <= k1 <= k2 <= 100000. -/
theorem spec_11 (nums : Slice I64) (numOperations : I64) (k1 k2 : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk10 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∀ (r1 r2 : I64),
      Aegis.MaxFrequency.max_frequency nums k1 numOperations = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k2 numOperations = Result.ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (numOperations : I64) (k1 k2 : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk10 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∀ (r1 r2 : I64),
      Aegis.MaxFrequency.max_frequency nums k1 numOperations = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k2 numOperations = Result.ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If r1 is the result of max_frequency(nums, k, m1) and r2 is the result of max_frequency(nums, k, m2), then r1 <= r2.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; and let m1 and m2 be integers with 0 <= m1 <= m2 <= n. -/
theorem spec_12 (nums : Slice I64) (k : I64) (m1 m2 : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm10 : 0 ≤ m1.val) (hm12 : m1.val ≤ m2.val)
    (hm2 : m2.val ≤ (nums.val.length : ℤ)) :
    ∀ (r1 r2 : I64),
      Aegis.MaxFrequency.max_frequency nums k m1 = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k m2 = Result.ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (m1 m2 : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm10 : 0 ≤ m1.val) (hm12 : m1.val ≤ m2.val)
    (hm2 : m2.val ≤ (nums.val.length : ℤ)), ∀ (r1 r2 : I64),
      Aegis.MaxFrequency.max_frequency nums k m1 = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k m2 = Result.ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- The function returns a result r and there exist a set S of exactly numOperations distinct indices with 0 <= i < n, integers delta_i with -k <= delta_i <= k for every i in S, and an integer t such that after changing nums[i] to nums[i] + delta_i for each i in S and leaving all other entries unchanged, exactly r entries of the resulting array are equal to t.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_13 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      ∃ (S : Finset ℕ) (d : ℕ → ℤ) (t : ℤ),
        (S.card : ℤ) = numOperations.val ∧
        (∀ i ∈ S, i < nums.val.length) ∧
        (∀ i ∈ S, -k.val ≤ d i ∧ d i ≤ k.val) ∧
        countFn nums.val.length
          (fun i => if i ∈ S then entry nums.val i + d i else entry nums.val i) t = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      ∃ (S : Finset ℕ) (d : ℕ → ℤ) (t : ℤ),
        (S.card : ℤ) = numOperations.val ∧
        (∀ i ∈ S, i < nums.val.length) ∧
        (∀ i ∈ S, -k.val ≤ d i ∧ d i ≤ k.val) ∧
        countFn nums.val.length
          (fun i => if i ∈ S then entry nums.val i + d i else entry nums.val i) t = r.val) := by
  sorry

/-- The function returns a result r and for every integer t, every set S of exactly numOperations distinct indices with 0 <= i < n, and every choice of integers delta_i with -k <= delta_i <= k for i in S, the number of entries equal to t after changing nums[i] to nums[i] + delta_i for i in S and leaving other entries unchanged is at most r.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= numOperations <= n. -/
theorem spec_14 (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)) :
    ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      ∀ (t : ℤ) (S : Finset ℕ) (d : ℕ → ℤ),
        (S.card : ℤ) = numOperations.val →
        (∀ i ∈ S, i < nums.val.length) →
        (∀ i ∈ S, -k.val ≤ d i ∧ d i ≤ k.val) →
        countFn nums.val.length
          (fun i => if i ∈ S then entry nums.val i + d i else entry nums.val i) t ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k numOperations : I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hvals : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ 100000)
    (hm0 : 0 ≤ numOperations.val)
    (hm : numOperations.val ≤ (nums.val.length : ℤ)), ∃ r : I64,
      Aegis.MaxFrequency.max_frequency nums k numOperations = Result.ok r ∧
      ∀ (t : ℤ) (S : Finset ℕ) (d : ℕ → ℤ),
        (S.card : ℤ) = numOperations.val →
        (∀ i ∈ S, i < nums.val.length) →
        (∀ i ∈ S, -k.val ≤ d i ∧ d i ≤ k.val) →
        countFn nums.val.length
          (fun i => if i ∈ S then entry nums.val i + d i else entry nums.val i) t ≤ r.val) := by
  sorry

end AegisSpec.MaxFrequency
