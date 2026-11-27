import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-numbers-non-positive`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun v => v.val)

  def total (nums : Slice I64) : ℤ := (vals nums).sum

  def maxEntry (nums : Slice I64) : ℤ := (vals nums).foldr max 0

  def totalCost (nums : Slice I64) (x y : ℤ) : ℤ := x + ((nums.val.length : ℤ) - 1) * y

  def KFeasible (nums : Slice I64) (x y : ℤ) (k : ℕ) (c : Fin nums.val.length → ℕ) : Prop :=
    (∑ i, c i) = k ∧
      ∀ i : Fin nums.val.length, (nums.val.get i).val - y * ↑k - (x - y) * ↑(c i) ≤ 0

  def LeastFeasible (nums : Slice I64) (x y : ℤ) (k : ℕ) : Prop :=
    (∃ c, KFeasible nums x y k c) ∧ ∀ j, j < k → ¬ ∃ c, KFeasible nums x y j c

  /-- The function returns a result r. For an integer k >= 0, call a count vector c k-feasible when c assigns a nonnegative integer c(i) to every index 0 <= i < len(nums), the sum of all c(i) over 0 <= i < len(nums) equals k, and for every i with 0 <= i < len(nums), nums[i] - y*k - (x-y)*c(i) <= 0. Then r is the least nonnegative integer k for which a k-feasible count vector exists.
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_1 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
        LeastFeasible nums x.val y.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
          LeastFeasible nums x.val y.val r.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail by overflow, panic, or out-of-bounds access on any input satisfying the preconditions.
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_2 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r) := by
    sorry

  /-- Let M = max over 0 <= i < len(nums) of nums[i]. The function returns a result r and r <= (M + y - 1) / y, using integer division; equivalently r <= ceil(M / y).
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_3 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
        r.val ≤ (maxEntry nums + y.val - 1) / y.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
          r.val ≤ (maxEntry nums + y.val - 1) / y.val) := by
    sorry

  /-- Let M = max over 0 <= i < len(nums) of nums[i]. The function returns a result r and x*r >= M.
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_4 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
        maxEntry nums ≤ x.val * r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
          maxEntry nums ≤ x.val * r.val) := by
    sorry

  /-- Let S = sum over 0 <= i < len(nums) of nums[i] and D = x + (len(nums)-1)*y. The function returns a result r and r >= (S + D - 1) / D, using integer division; equivalently r >= ceil(S / D).
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_5 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
        (total nums + totalCost nums x.val y.val - 1) / totalCost nums x.val y.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
          (total nums + totalCost nums x.val y.val - 1) / totalCost nums x.val y.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and r is the least nonnegative integer t with t*x >= nums[0]; equivalently r = (nums[0] + x - 1) / x using integer division.
    Preconditions: len(nums) = 1; 1 <= nums[0] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_6 (nums : Slice I64) (x y : I64)
      (hlen : nums.val.length = 1)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
        (nums.val.get ⟨0, by omega⟩).val ≤ r.val * x.val ∧
        (∀ t : ℤ, 0 ≤ t → (nums.val.get ⟨0, by omega⟩).val ≤ t * x.val → r.val ≤ t) ∧
        r.val = ((nums.val.get ⟨0, by omega⟩).val + x.val - 1) / x.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64)
        (hlen : nums.val.length = 1)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
          (nums.val.get ⟨0, by omega⟩).val ≤ r.val * x.val ∧
          (∀ t : ℤ, 0 ≤ t → (nums.val.get ⟨0, by omega⟩).val ≤ t * x.val → r.val ≤ t) ∧
          r.val = ((nums.val.get ⟨0, by omega⟩).val + x.val - 1) / x.val) := by
    sorry

  /-- The function returns a result r and r = 1 if and only if there exists an index i with 0 <= i < len(nums) such that nums[i] <= x and, for every j with 0 <= j < len(nums) and j != i, nums[j] <= y.
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_7 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
        (r.val = 1 ↔
          ∃ i : Fin nums.val.length, (nums.val.get i).val ≤ x.val ∧
            ∀ j : Fin nums.val.length, j ≠ i → (nums.val.get j).val ≤ y.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧
          (r.val = 1 ↔
            ∃ i : Fin nums.val.length, (nums.val.get i).val ≤ x.val ∧
              ∀ j : Fin nums.val.length, j ≠ i → (nums.val.get j).val ≤ y.val)) := by
    sorry

  /-- Whenever min_operations(nums,x,y) returns r and min_operations(nums',x,y) returns r', we have r = r'.
    Preconditions: nums and nums' both satisfy len(nums') = len(nums) = n with 1 <= n <= 10^5, all their entries are in [1, 10^9], 1 <= y < x <= 10^9, and nums' is a permutation of nums: there is a bijection p on the indices with nums'[j] = nums[p(j)] for every j. -/
  theorem spec_8 (nums nums' : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hval' : ∀ i (h : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
      (hperm : nums'.val.Perm nums.val) :
      ∀ r r' : I64,
        Aegis.MinOperations.min_operations nums x y = ok r →
        Aegis.MinOperations.min_operations nums' x y = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hval' : ∀ i (h : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
        (hperm : nums'.val.Perm nums.val), ∀ r r' : I64,
          Aegis.MinOperations.min_operations nums x y = ok r →
          Aegis.MinOperations.min_operations nums' x y = ok r' → r = r') := by
    sorry

  /-- Whenever min_operations(nums,x,y) returns r and min_operations(nums',x,y) returns r', we have r <= r'.
    Preconditions: nums and nums' both satisfy len(nums') = len(nums) = n with 1 <= n <= 10^5, all their entries are in [1, 10^9], 1 <= y < x <= 10^9, and nums[i] <= nums'[i] for every 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hval' : ∀ i (h : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
      (hle : ∀ i : Fin n,
        (nums.val.get (Fin.cast hlen.symm i)).val ≤ (nums'.val.get (Fin.cast hlen'.symm i)).val) :
      ∀ r r' : I64,
        Aegis.MinOperations.min_operations nums x y = ok r →
        Aegis.MinOperations.min_operations nums' x y = ok r' → r ≤ r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hval' : ∀ i (h : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
        (hle : ∀ i : Fin n,
          (nums.val.get (Fin.cast hlen.symm i)).val ≤ (nums'.val.get (Fin.cast hlen'.symm i)).val), ∀ r r' : I64,
          Aegis.MinOperations.min_operations nums x y = ok r →
          Aegis.MinOperations.min_operations nums' x y = ok r' → r ≤ r') := by
    sorry

  /-- Whenever min_operations(nums,x1,y) returns r1 and min_operations(nums,x2,y) returns r2, we have r2 <= r1.
    Preconditions: nums satisfies len(nums) = n with 1 <= n <= 10^5, all entries are in [1, 10^9], and 1 <= y < x1 <= x2 <= 10^9. -/
  theorem spec_10 (nums : Slice I64) (x1 x2 y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy1 : y.val < x1.val) (hx12 : x1.val ≤ x2.val)
      (hx2_le : x2.val ≤ 10 ^ 9) :
      ∀ r1 r2 : I64,
        Aegis.MinOperations.min_operations nums x1 y = ok r1 →
        Aegis.MinOperations.min_operations nums x2 y = ok r2 → r2 ≤ r1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (x1 x2 y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy1 : y.val < x1.val) (hx12 : x1.val ≤ x2.val)
        (hx2_le : x2.val ≤ 10 ^ 9), ∀ r1 r2 : I64,
          Aegis.MinOperations.min_operations nums x1 y = ok r1 →
          Aegis.MinOperations.min_operations nums x2 y = ok r2 → r2 ≤ r1) := by
    sorry

  /-- Whenever min_operations(nums,x,y) returns r and min_operations(nums',x',y') returns r', we have r = r'.
    Preconditions: len(nums) = len(nums') = n with 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] <= 10^9 and 1 <= nums'[i] <= 10^9; 1 <= y < x <= 10^9; t is a positive integer; x' = t*x and y' = t*y satisfy 1 <= y' < x' <= 10^9; and for every i with 0 <= i < n, nums'[i] = t*nums[i]. -/
  theorem spec_11 (nums nums' : Slice I64) (x y x' y' : I64) (t : ℤ) (n : ℕ)
      (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hval' : ∀ i (h : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
      (ht : 0 < t) (hx' : x'.val = t * x.val) (hy' : y'.val = t * y.val)
      (hy'_pos : 1 ≤ y'.val) (hxy' : y'.val < x'.val) (hx'_le : x'.val ≤ 10 ^ 9)
      (hscale : ∀ i : Fin n,
        (nums'.val.get (Fin.cast hlen'.symm i)).val = t * (nums.val.get (Fin.cast hlen.symm i)).val) :
      ∀ r r' : I64,
        Aegis.MinOperations.min_operations nums x y = ok r →
        Aegis.MinOperations.min_operations nums' x' y' = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice I64) (x y x' y' : I64) (t : ℤ) (n : ℕ)
        (hlen : nums.val.length = n) (hlen' : nums'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hval' : ∀ i (h : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9)
        (ht : 0 < t) (hx' : x'.val = t * x.val) (hy' : y'.val = t * y.val)
        (hy'_pos : 1 ≤ y'.val) (hxy' : y'.val < x'.val) (hx'_le : x'.val ≤ 10 ^ 9)
        (hscale : ∀ i : Fin n,
          (nums'.val.get (Fin.cast hlen'.symm i)).val = t * (nums.val.get (Fin.cast hlen.symm i)).val), ∀ r r' : I64,
          Aegis.MinOperations.min_operations nums x y = ok r →
          Aegis.MinOperations.min_operations nums' x' y' = ok r' → r = r') := by
    sorry

  /-- The function returns a result r. Define a count vector c for r to be r-feasible when c assigns a nonnegative integer to every index, the sum of all c(i) over 0 <= i < len(nums) equals r, and for every i, nums[i] - y*r - (x-y)*c(i) <= 0. Then there exist an r-feasible count vector c and an index m with 0 <= m < len(nums) such that nums[m] = max over 0 <= i < len(nums) of nums[i] and c(m) >= 1.
    Preconditions: len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y < x <= 10^9. -/
  theorem spec_12 (nums : Slice I64) (x y : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
        ∃ c : Fin nums.val.length → ℕ,
          KFeasible nums x.val y.val r.val.toNat c ∧
            ∃ m : Fin nums.val.length, (nums.val.get m).val = maxEntry nums ∧ 1 ≤ c m := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (x y : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy_pos : 1 ≤ y.val) (hxy : y.val < x.val) (hx_le : x.val ≤ 10 ^ 9), ∃ r : I64, Aegis.MinOperations.min_operations nums x y = ok r ∧ 0 ≤ r.val ∧
          ∃ c : Fin nums.val.length → ℕ,
            KFeasible nums x.val y.val r.val.toNat c ∧
              ∃ m : Fin nums.val.length, (nums.val.get m).val = maxEntry nums ∧ 1 ≤ c m) := by
    sorry

  /-- Whenever min_operations(nums,x,y1) returns r1 and min_operations(nums,x,y2) returns r2, we have r2 <= r1.
    Preconditions: nums satisfies len(nums) = n with 1 <= n <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= y1 <= y2 < x <= 10^9. -/
  theorem spec_13 (nums : Slice I64) (x y1 y2 : I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
      (hval : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
      (hy1_pos : 1 ≤ y1.val) (hy12 : y1.val ≤ y2.val) (hy2x : y2.val < x.val)
      (hx_le : x.val ≤ 10 ^ 9) :
      ∀ r1 r2 : I64,
        Aegis.MinOperations.min_operations nums x y1 = ok r1 →
        Aegis.MinOperations.min_operations nums x y2 = ok r2 → r2 ≤ r1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (x y1 y2 : I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
        (hval : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 10 ^ 9)
        (hy1_pos : 1 ≤ y1.val) (hy12 : y1.val ≤ y2.val) (hy2x : y2.val < x.val)
        (hx_le : x.val ≤ 10 ^ 9), ∀ r1 r2 : I64,
          Aegis.MinOperations.min_operations nums x y1 = ok r1 →
          Aegis.MinOperations.min_operations nums x y2 = ok r2 → r2 ≤ r1) := by
    sorry

  end AegisSpec.MinOperations
