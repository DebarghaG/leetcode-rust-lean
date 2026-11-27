import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-numbers-of-function-calls-to-make-target-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinOperations

namespace AegisSpec.MinOperations

def popcount : ℕ → ℕ
  | 0 => 0
  | x + 1 => (if (x + 1) % 2 = 1 then 1 else 0) + popcount ((x + 1) / 2)
termination_by x => x
decreasing_by omega

def top (x : ℕ) : ℕ := if x = 0 then 0 else x.log2

def sumPopcount (l : List Std.I64) : ℕ := (l.map (fun x => popcount x.val.toNat)).sum

def maxTop (l : List Std.I64) : ℕ := (l.map (fun x => top x.val.toNat)).foldr max 0

inductive Call where

  | inc (i : ℕ)

  | double

def Call.apply (c : Call) (v : List ℤ) : List ℤ :=
  match c with
  | .inc i => v.set i (v.getD i 0 + 1)
  | .double => v.map (fun x => 2 * x)

def runCalls (v : List ℤ) (cs : List Call) : List ℤ := cs.foldl (fun v c => Call.apply c v) v

def countInc : List Call → ℕ
  | [] => 0
  | .inc _ :: cs => countInc cs + 1
  | .double :: cs => countInc cs

def countDouble : List Call → ℕ
  | [] => 0
  | .inc _ :: cs => countDouble cs
  | .double :: cs => countDouble cs + 1

def ivals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

/-- The function returns a result r and r = (sum_{i=0}^{n-1} popcount(nums[i])) + max_{i=0}^{n-1} top(nums[i]).
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. For a nonnegative integer x, popcount(x) is the number of 1 bits in its binary expansion, and top(x) is 0 if x=0 and otherwise the index of its highest set bit; thus top(0)=top(1)=0, top(2)=1, and so on. -/
theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val = (sumPopcount nums.val : ℤ) + (maxTop nums.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val = (sumPopcount nums.val : ℤ) + (maxTop nums.val : ℤ)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, or panic.
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r) := by
  sorry

/-- The function returns a result r and r >= sum_{i=0}^{n-1} popcount(nums[i]).
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. For a nonnegative integer x, popcount(x) is the number of 1 bits in its binary expansion. -/
theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      (sumPopcount nums.val : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      (sumPopcount nums.val : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 30*n + 29.
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val ≤ 30 * (n : ℤ) + 29 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val ≤ 30 * (n : ℤ) + 29) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: nums has length n with 1 <= n <= 100000, and nums[i]=0 for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_zero : ∀ x ∈ nums.val, x.val = 0) :
    ∃ r : Std.I64, min_operations nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_zero : ∀ x ∈ nums.val, x.val = 0), ∃ r : Std.I64, min_operations nums = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{n-1} nums[i].
  Preconditions: nums has length n with 1 <= n <= 100000, and for every i with 0 <= i < n, nums[i] is either 0 or 1. -/
theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_bin : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val = (ivals nums.val).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_bin : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∃ r : Std.I64, min_operations nums = ok r ∧
      r.val = (ivals nums.val).sum) := by
  sorry

/-- Let ys be the array of length n-1 obtained by deleting nums[j], so ys[i]=nums[i] for 0 <= i < j and ys[i]=nums[i+1] for j <= i < n-1. Then the function returns a result r and r = the result returned by min_operations(ys).
  Preconditions: nums has length n with 2 <= n <= 100000, 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n, and nums[j]=0 for some j with 0 <= j < n. -/
theorem spec_7 (nums ys : Slice Std.I64) (n j : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 2 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_j : j < n)
    (h_j_zero : ∃ x : Std.I64, nums.val[j]? = some x ∧ x.val = 0)
    (h_ys : ys.val = nums.val.eraseIdx j) :
    ∃ r : Std.I64, min_operations nums = ok r ∧ min_operations ys = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums ys : Slice Std.I64) (n j : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 2 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_j : j < n)
    (h_j_zero : ∃ x : Std.I64, nums.val[j]? = some x ∧ x.val = 0)
    (h_ys : ys.val = nums.val.eraseIdx j), ∃ r : Std.I64, min_operations nums = ok r ∧ min_operations ys = ok r) := by
  sorry

/-- Let ys be the array of length n defined by ys[i]=nums[p(i)] for every i with 0 <= i < n. Then the function returns a result r and r = the result returned by min_operations(ys).
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Also p is a permutation of {0,...,n-1}. -/
theorem spec_8 (nums ys : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_perm : ys.val.Perm nums.val) :
    ∃ r r' : Std.I64, min_operations nums = ok r ∧ min_operations ys = ok r' ∧ r.val = r'.val
  := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums ys : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_perm : ys.val.Perm nums.val), ∃ r r' : Std.I64, min_operations nums = ok r ∧ min_operations ys = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let xs be such an array. Then the function returns a result r and r = (the result returned by min_operations(xs)) + 1.
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. There exists an array xs of length n with 0 <= xs[i] <= 500000000 for every i with 0 <= i < n, nums[i]=2*xs[i] for every i, and xs[j] > 0 for at least one j. -/
theorem spec_9 (nums xs : Slice Std.I64) (n j : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_xs_len : xs.val.length = n)
    (h_xs_nonneg : ∀ x ∈ xs.val, 0 ≤ x.val)
    (h_xs_bound : ∀ x ∈ xs.val, x.val ≤ 500000000)
    (h_double : ivals nums.val = xs.val.map (fun x => 2 * x.val))
    (h_j : j < n)
    (h_j_pos : ∃ x : Std.I64, xs.val[j]? = some x ∧ 0 < x.val) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      ∃ r' : Std.I64, min_operations xs = ok r' ∧ r.val = r'.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums xs : Slice Std.I64) (n j : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000)
    (h_xs_len : xs.val.length = n)
    (h_xs_nonneg : ∀ x ∈ xs.val, 0 ≤ x.val)
    (h_xs_bound : ∀ x ∈ xs.val, x.val ≤ 500000000)
    (h_double : ivals nums.val = xs.val.map (fun x => 2 * x.val))
    (h_j : j < n)
    (h_j_pos : ∃ x : Std.I64, xs.val[j]? = some x ∧ 0 < x.val), ∃ r : Std.I64, min_operations nums = ok r ∧
      ∃ r' : Std.I64, min_operations xs = ok r' ∧ r.val = r'.val + 1) := by
  sorry

/-- The function returns a result r and there exists a call sequence of length r from the zero array to nums that uses exactly S increment calls and exactly T doubling calls, where S = sum_{i=0}^{n-1} popcount(nums[i]) and T = max_{i=0}^{n-1} top(nums[i]).
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. For a nonnegative integer x, popcount(x) is the number of 1 bits in its binary expansion, and top(x) is 0 if x=0 and otherwise the index of its highest set bit; thus top(0)=top(1)=0, top(2)=1, and so on. -/
theorem spec_10 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      ∃ cs : List Call,
        (cs.length : ℤ) = r.val ∧
        runCalls (List.replicate n (0 : ℤ)) cs = ivals nums.val ∧
        countInc cs = sumPopcount nums.val ∧
        countDouble cs = maxTop nums.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      ∃ cs : List Call,
        (cs.length : ℤ) = r.val ∧
        runCalls (List.replicate n (0 : ℤ)) cs = ivals nums.val ∧
        countInc cs = sumPopcount nums.val ∧
        countDouble cs = maxTop nums.val) := by
  sorry

/-- The function returns a result r and for every k >= 0 and every sequence of k calls, where each call is either adding 1 to one chosen coordinate or doubling every coordinate, that starts from the all-zero array of length n and ends at nums, we have r <= k.
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      ∀ (k : ℕ) (cs : List Call),
        cs.length = k →
        runCalls (List.replicate n (0 : ℤ)) cs = ivals nums.val →
        r.val.toNat ≤ k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      ∀ (k : ℕ) (cs : List Call),
        cs.length = k →
        runCalls (List.replicate n (0 : ℤ)) cs = ivals nums.val →
        r.val.toNat ≤ k) := by
  sorry

/-- The function returns a result r and, for every i with 0 <= i < n, r >= popcount(nums[i]) + top(nums[i]).
  Preconditions: nums has length n with 1 <= n <= 100000, and 0 <= nums[i] <= 1000000000 for every i with 0 <= i < n. For a nonnegative integer x, popcount(x) is the number of 1 bits in its binary expansion, and top(x) is 0 if x=0 and otherwise the index of its highest set bit. -/
theorem spec_12 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000) :
    ∃ r : Std.I64, min_operations nums = ok r ∧
      ∀ x ∈ nums.val, (popcount x.val.toNat : ℤ) + (top x.val.toNat : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n)
    (h_n_ge : 1 ≤ n) (h_n_le : n ≤ 100000)
    (h_nonneg : ∀ x ∈ nums.val, 0 ≤ x.val)
    (h_bound : ∀ x ∈ nums.val, x.val ≤ 1000000000), ∃ r : Std.I64, min_operations nums = ok r ∧
      ∀ x ∈ nums.val, (popcount x.val.toNat : ℤ) + (top x.val.toNat : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.MinOperations
