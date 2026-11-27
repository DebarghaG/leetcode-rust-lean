import Aegis.LargestPerimeter.Code.Funs

/-!
# Specifications of `Aegis.LargestPerimeter.largest_perimeter`

LeetCode problem `find-polygon-with-the-largest-perimeter`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestPerimeter

open Aegis.LargestPerimeter

def elem (l : List Std.I64) (i : ℕ) : ℤ :=
  match l[i]? with
  | some x => x.val
  | none => 0

def toInts (l : List Std.I64) : List ℤ := l.map fun x => x.val

def setSum (l : List Std.I64) (S : Finset ℕ) : ℤ := S.sum (elem l)

def setMax (l : List Std.I64) (S : Finset ℕ) : ℤ :=
  if h : S.Nonempty then S.sup' h (elem l) else 0

def IsValidSet (l : List Std.I64) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range l.length ∧ 3 ≤ S.card ∧ setSum l S > 2 * setMax l S

def prefixSet (l : List Std.I64) (m : ℕ) : Finset ℕ :=
  (Finset.range l.length).filter fun i => elem l i ≤ elem l m

def IsSorted (b : List ℤ) : Prop := b.Pairwise (· ≤ ·)

def IsRearrangement (l : List Std.I64) (b : List ℤ) : Prop :=
  IsSorted b ∧ b.length = l.length ∧ ∀ v : ℤ, b.count v = (toInts l).count v

def prefixSum (b : List ℤ) (k : ℕ) : ℤ := (b.take k).sum

def nthVal (b : List ℤ) (i : ℕ) : ℤ := b.getD i 0

/-- The function returns a result r and the following holds. For an index set S, call S valid if S is a subset of {0,...,n-1}, |S| >= 3, and sum_{i in S} nums[i] > 2 * max_{i in S} nums[i]. If at least one valid S exists, then r is the maximum of sum_{i in S} nums[i] over all valid S. If no valid S exists, then r = -1.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∃ r : Std.I64, largest_perimeter nums = ok r ∧
      ((∃ S : Finset ℕ, IsValidSet nums.val S) →
        (∃ S : Finset ℕ, IsValidSet nums.val S ∧ setSum nums.val S = r.val) ∧
        ∀ S : Finset ℕ, IsValidSet nums.val S → setSum nums.val S ≤ r.val) ∧
      ((¬ ∃ S : Finset ℕ, IsValidSet nums.val S) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∃ r : Std.I64, largest_perimeter nums = ok r ∧
      ((∃ S : Finset ℕ, IsValidSet nums.val S) →
        (∃ S : Finset ℕ, IsValidSet nums.val S ∧ setSum nums.val S = r.val) ∧
        ∀ S : Finset ℕ, IsValidSet nums.val S → setSum nums.val S ≤ r.val) ∧
      ((¬ ∃ S : Finset ℕ, IsValidSet nums.val S) → r.val = -1)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail due to 64-bit overflow, out-of-bounds access, or panic on any input satisfying the preconditions.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∃ r : Std.I64, largest_perimeter nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∃ r : Std.I64, largest_perimeter nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then 3 <= r <= sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      3 ≤ r.val ∧ r.val ≤ (toInts nums.val).sum := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      3 ≤ r.val ∧ r.val ≤ (toInts nums.val).sum) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then there exists an index set S that is a subset of {0,...,n-1} with |S| >= 3 such that sum_{i in S} nums[i] = r and sum_{i in S} nums[i] > 2 * max_{i in S} nums[i].
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ S : Finset ℕ, IsValidSet nums.val S ∧ setSum nums.val S = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ S : Finset ℕ, IsValidSet nums.val S ∧ setSum nums.val S = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then for every index set T that is a subset of {0,...,n-1} with |T| >= 3 and sum_{i in T} nums[i] > 2 * max_{i in T} nums[i], we have sum_{i in T} nums[i] <= r.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∀ T : Finset ℕ, IsValidSet nums.val T → setSum nums.val T ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∀ T : Finset ℕ, IsValidSet nums.val T → setSum nums.val T ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no index set S that is a subset of {0,...,n-1} with |S| >= 3 and sum_{i in S} nums[i] > 2 * max_{i in S} nums[i].
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r →
      (r.val = -1 ↔ ¬ ∃ S : Finset ℕ, IsValidSet nums.val S) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r →
      (r.val = -1 ↔ ¬ ∃ S : Finset ℕ, IsValidSet nums.val S)) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then there exists an index m with 0 <= m < n such that r = sum_{i: 0 <= i < n and nums[i] <= nums[m]} nums[i] and r > 2 * nums[m].
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ m, m < nums.val.length ∧
        r.val = setSum nums.val (prefixSet nums.val m) ∧
        r.val > 2 * elem nums.val m := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ m, m < nums.val.length ∧
        r.val = setSum nums.val (prefixSet nums.val m) ∧
        r.val > 2 * elem nums.val m) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then there exists an index m with 0 <= m < n such that r = sum_{i: 0 <= i < n and nums[i] <= nums[m]} nums[i], r > 2 * nums[m], and for every index j with 0 <= j < n and nums[j] > nums[m], we have nums[j] >= r.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ m, m < nums.val.length ∧
        r.val = setSum nums.val (prefixSet nums.val m) ∧
        r.val > 2 * elem nums.val m ∧
        ∀ j, j < nums.val.length → elem nums.val m < elem nums.val j →
          r.val ≤ elem nums.val j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∃ m, m < nums.val.length ∧
        r.val = setSum nums.val (prefixSet nums.val m) ∧
        r.val > 2 * elem nums.val m ∧
        ∀ j, j < nums.val.length → elem nums.val m < elem nums.val j →
          r.val ≤ elem nums.val j) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r = r'.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. In the statement, nums' is any slice of 64-bit integers with len(nums') = n that is a permutation of nums (for every value v, the number of indices i with nums[i] = v equals the number of indices i with nums'[i] = v); hence nums' also satisfies the same value bounds. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ nums' : Slice Std.I64, nums'.val.length = nums.val.length →
      (∀ v : ℤ, (toInts nums'.val).count v = (toInts nums.val).count v) →
      ∀ r r' : Std.I64,
        largest_perimeter nums = ok r → largest_perimeter nums' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ nums' : Slice Std.I64, nums'.val.length = nums.val.length →
      (∀ v : ℤ, (toInts nums'.val).count v = (toInts nums.val).count v) →
      ∀ r r' : Std.I64,
        largest_perimeter nums = ok r → largest_perimeter nums' = ok r' → r = r') := by
  sorry

/-- Let b_1 <= b_2 <= ... <= b_n be the nondecreasing rearrangement of nums, and for k = 1,...,n let P_k = b_1 + ... + b_k. Whenever the function returns a result r, if r != -1 then there exists an integer k with 3 <= k <= n such that r = P_k and P_k > 2 * b_k.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∀ b : List ℤ, IsRearrangement nums.val b →
        ∃ k, 3 ≤ k ∧ k ≤ nums.val.length ∧
          r.val = prefixSum b k ∧ prefixSum b k > 2 * nthVal b (k - 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r → r.val ≠ -1 →
      ∀ b : List ℤ, IsRearrangement nums.val b →
        ∃ k, 3 ≤ k ∧ k ≤ nums.val.length ∧
          r.val = prefixSum b k ∧ prefixSum b k > 2 * nthVal b (k - 1)) := by
  sorry

/-- Let b_1 <= b_2 <= ... <= b_n be the nondecreasing rearrangement of nums, and for k = 1,...,n let P_k = b_1 + ... + b_k. Whenever the function returns a result r, r = -1 if and only if for every integer k with 3 <= k <= n, P_k <= 2 * b_k.
  Preconditions: Let n = len(nums). It is assumed that 3 <= n <= 100000 and that for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000) :
    ∀ r : Std.I64, largest_perimeter nums = ok r →
      ∀ b : List ℤ, IsRearrangement nums.val b →
        (r.val = -1 ↔
          ∀ k, 3 ≤ k → k ≤ nums.val.length → prefixSum b k ≤ 2 * nthVal b (k - 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len : 3 ≤ nums.val.length) (h_len_ub : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      1 ≤ elem nums.val i ∧ elem nums.val i ≤ 1000000000), ∀ r : Std.I64, largest_perimeter nums = ok r →
      ∀ b : List ℤ, IsRearrangement nums.val b →
        (r.val = -1 ↔
          ∀ k, 3 ≤ k → k ≤ nums.val.length → prefixSum b k ≤ 2 * nthVal b (k - 1))) := by
  sorry

end AegisSpec.LargestPerimeter
