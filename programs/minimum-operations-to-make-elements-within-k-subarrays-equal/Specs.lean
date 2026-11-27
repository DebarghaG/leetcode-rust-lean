import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-elements-within-k-subarrays-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun v => v.val)

  def windowDeviation (l : List ℤ) (x i : ℕ) (v : ℤ) : ℕ :=
    ((List.range x).map (fun j => (l.getD (i + j) 0 - v).natAbs)).sum

  noncomputable def windowCost (l : List ℤ) (x i : ℕ) : ℤ :=
    ((sInf {m : ℕ | ∃ v : ℤ, m = windowDeviation l x i v} : ℕ) : ℤ)

  def Admissible (n x k : ℕ) (a : ℕ → ℕ) : Prop :=
    (∀ t, t + 1 < k → a t + x ≤ a (t + 1)) ∧ a (k - 1) + x ≤ n

  noncomputable def totalCost (l : List ℤ) (x k : ℕ) (a : ℕ → ℕ) : ℤ :=
    (Finset.range k).sum (fun t => windowCost l x (a t))

  noncomputable def bestCost (l : List ℤ) (x k : ℕ) : ℤ :=
    ((sInf {m : ℕ | ∃ a : ℕ → ℕ, Admissible l.length x k a ∧
      m = (totalCost l x k a).toNat} : ℕ) : ℤ)

  def WindowConstant (l : List ℤ) (x i : ℕ) : Prop :=
    ∀ j, j < x → l.getD (i + j) 0 = l.getD i 0

  /-- The function returns a result r, and r equals the minimum of Σ_{t=0}^{k-1} C(a_t) over all choices of k integers a_0,...,a_{k-1} such that 0 <= a_0, a_{t+1} >= a_t + x for every 0 <= t < k-1, and a_{k-1} + x <= len(nums), where for each integer i with 0 <= i <= len(nums)-x, C(i) = min { Σ_{j=0}^{x-1} |nums[i+j] - v| : v ∈ ℤ }.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_1 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
        r.val = bestCost (vals nums) x.val.toNat k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
          r.val = bestCost (vals nums) x.val.toNat k.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_2 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r) := by
    sorry

  /-- The function returns a result r and r >= 0.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_3 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 2000000 * k * x.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_4 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
        r.val ≤ 2000000 * k.val * x.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
          r.val ≤ 2000000 * k.val * x.val) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if there exist k integers a_0,...,a_{k-1} such that 0 <= a_0, a_{t+1} >= a_t + x for every t with 0 <= t < k-1, a_{k-1} + x <= len(nums), and for every t with 0 <= t < k and every j with 0 <= j < x, nums[a_t+j] = nums[a_t].
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_5 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
        (r.val = 0 ↔ ∃ a : ℕ → ℕ,
          Admissible (vals nums).length x.val.toNat k.val.toNat a ∧
            ∀ t, t < k.val.toNat → WindowConstant (vals nums) x.val.toNat (a t)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
          (r.val = 0 ↔ ∃ a : ℕ → ℕ,
            Admissible (vals nums).length x.val.toNat k.val.toNat a ∧
              ∀ t, t < k.val.toNat → WindowConstant (vals nums) x.val.toNat (a t))) := by
    sorry

  /-- If min_operations(nums,x,k) returns r and min_operations(nums',x,k) returns r', then r = r'.
    Preconditions: nums and nums' are slices of i64 with the same length n; nums and nums' both satisfy 2 <= n <= 100000 and all their entries lie in [-1000000,1000000]; 2 <= x <= n; 1 <= k <= 15; 2 <= k*x <= n; and there is an integer c such that nums'[i] = nums[i] + c for every 0 <= i < n, with every nums'[i] still in the i64 range. -/
  theorem spec_6 (nums nums' : Slice Std.I64) (x k : Std.I64) (n : ℕ) (c : ℤ)
      (h_len : (vals nums).length = n) (h_len' : (vals nums').length = n)
      (h_n_lo : 2 ≤ n) (h_n_hi : n ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_bounds' : ∀ a ∈ vals nums', -1000000 ≤ a ∧ a ≤ 1000000)
      (h_shift : ∀ i, i < n → (vals nums').getD i 0 = (vals nums).getD i 0 + c)
      (h_i64 : ∀ a ∈ vals nums',
        -9223372036854775808 ≤ a ∧ a ≤ 9223372036854775807)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ (n : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ (n : ℤ)) :
      ∀ r r' : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r →
        Aegis.MinOperations.min_operations nums' x k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (x k : Std.I64) (n : ℕ) (c : ℤ)
        (h_len : (vals nums).length = n) (h_len' : (vals nums').length = n)
        (h_n_lo : 2 ≤ n) (h_n_hi : n ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_bounds' : ∀ a ∈ vals nums', -1000000 ≤ a ∧ a ≤ 1000000)
        (h_shift : ∀ i, i < n → (vals nums').getD i 0 = (vals nums).getD i 0 + c)
        (h_i64 : ∀ a ∈ vals nums',
          -9223372036854775808 ≤ a ∧ a ≤ 9223372036854775807)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ (n : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ (n : ℤ)), ∀ r r' : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r →
          Aegis.MinOperations.min_operations nums' x k = ok r' → r.val = r'.val) := by
    sorry

  /-- If min_operations(nums,x,k1) returns r1 and min_operations(nums,x,k2) returns r2, then r1 <= r2.
    Preconditions: len(nums) is between 2 and 100000 inclusive; every nums[i] lies in [-1000000,1000000]; 2 <= x <= len(nums); and integers k1,k2 satisfy 1 <= k1 <= k2 <= 15 and 2 <= k2*x <= len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (x k1 k2 : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k1_lo : 1 ≤ k1.val) (h_k1_le : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ 15)
      (h_prod_lo : 2 ≤ k2.val * x.val)
      (h_prod_hi : k2.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∀ r1 r2 : Std.I64, Aegis.MinOperations.min_operations nums x k1 = ok r1 →
        Aegis.MinOperations.min_operations nums x k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k1 k2 : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k1_lo : 1 ≤ k1.val) (h_k1_le : k1.val ≤ k2.val) (h_k2_hi : k2.val ≤ 15)
        (h_prod_lo : 2 ≤ k2.val * x.val)
        (h_prod_hi : k2.val * x.val ≤ ((vals nums).length : ℤ)), ∀ r1 r2 : Std.I64, Aegis.MinOperations.min_operations nums x k1 = ok r1 →
          Aegis.MinOperations.min_operations nums x k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r, and for every choice of integers a_0,...,a_{k-1} with 0 <= a_0, a_{t+1} >= a_t + x for all 0 <= t < k-1, and a_{k-1}+x <= len(nums), we have r <= Σ_{t=0}^{k-1} C(a_t), where C(i) = min { Σ_{j=0}^{x-1} |nums[i+j]-v| : v ∈ ℤ }.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_8 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
        ∀ a : ℕ → ℕ, Admissible (vals nums).length x.val.toNat k.val.toNat a →
          r.val ≤ totalCost (vals nums) x.val.toNat k.val.toNat a := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
          ∀ a : ℕ → ℕ, Admissible (vals nums).length x.val.toNat k.val.toNat a →
            r.val ≤ totalCost (vals nums) x.val.toNat k.val.toNat a) := by
    sorry

  /-- The function returns a result r, and there exist integers a_0,...,a_{k-1} with 0 <= a_0, a_{t+1} >= a_t + x for all 0 <= t < k-1, and a_{k-1}+x <= len(nums) such that r = Σ_{t=0}^{k-1} C(a_t), where C(i) = min { Σ_{j=0}^{x-1} |nums[i+j]-v| : v ∈ ℤ }.
    Preconditions: len(nums) is between 2 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000 <= nums[i] <= 1000000; 2 <= x <= len(nums); 1 <= k <= 15; and 2 <= k*x <= len(nums). -/
  theorem spec_9 (nums : Slice Std.I64) (x k : Std.I64)
      (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
      (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
      (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
      (h_prod_lo : 2 ≤ k.val * x.val)
      (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
        ∃ a : ℕ → ℕ, Admissible (vals nums).length x.val.toNat k.val.toNat a ∧
          r.val = totalCost (vals nums) x.val.toNat k.val.toNat a := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (x k : Std.I64)
        (h_len_lo : 2 ≤ (vals nums).length) (h_len_hi : (vals nums).length ≤ 100000)
        (h_bounds : ∀ a ∈ vals nums, -1000000 ≤ a ∧ a ≤ 1000000)
        (h_x_lo : 2 ≤ x.val) (h_x_hi : x.val ≤ ((vals nums).length : ℤ))
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ 15)
        (h_prod_lo : 2 ≤ k.val * x.val)
        (h_prod_hi : k.val * x.val ≤ ((vals nums).length : ℤ)), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums x k = ok r ∧
          ∃ a : ℕ → ℕ, Admissible (vals nums).length x.val.toNat k.val.toNat a ∧
            r.val = totalCost (vals nums) x.val.toNat k.val.toNat a) := by
    sorry

  end AegisSpec.MinOperations
