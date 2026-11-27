import Aegis.MinCostToEqualizeArray.Code.Funs

/-!
# Specifications of `Aegis.MinCostToEqualizeArray.min_cost_to_equalize_array`

LeetCode problem `minimum-cost-to-equalize-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCostToEqualizeArray

  open Aegis.MinCostToEqualizeArray (min_cost_to_equalize_array)

  def C : Int := 1000000007

  def len (nums : Slice Std.I64) : Nat := nums.val.length

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def get (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def B (nums : Slice Std.I64) : Int := listMax (vals nums)

  def d (nums : Slice Std.I64) (T : Int) (i : Nat) : Int := T - get nums i

  def S (nums : Slice Std.I64) (T : Int) : Int :=
    ((List.range (len nums)).map (fun i => d nums T i)).sum

  def Max (nums : Slice Std.I64) (T : Int) : Int :=
    listMax ((List.range (len nums)).map (fun i => d nums T i))

  def P (nums : Slice Std.I64) (T : Int) : Int := min (S nums T / 2) (S nums T - Max nums T)

  def D (nums : Slice Std.I64) : Int := S nums (B nums)

  def costs (nums : Slice Std.I64) (cost1 cost2 : Int) : Set Int :=
    {v | ∃ T p : Int,
      B nums ≤ T ∧ 0 ≤ p ∧ p ≤ P nums T ∧
        v = p * cost2 + (S nums T - 2 * p) * cost1}

  def IsMinCost (nums : Slice Std.I64) (cost1 cost2 M : Int) : Prop :=
    IsLeast (costs nums cost1 cost2) M

  def Achievable (nums : Slice Std.I64) (T : Int) (pairs singles : Nat) : Prop :=
    ∃ (pl : List (Nat × Nat)) (sl : List Nat),
      pl.length = pairs ∧ sl.length = singles ∧
        (∀ x ∈ pl, x.1 < len nums ∧ x.2 < len nums ∧ x.1 ≠ x.2) ∧
        (∀ k ∈ sl, k < len nums) ∧
        (∀ k, k < len nums →
          get nums k + 2 * (pl.countP (fun x => decide (x.1 = k ∨ x.2 = k))) + sl.count k = T)

  def LenOK (nums : Slice Std.I64) : Prop := 1 ≤ len nums ∧ len nums ≤ 100000

  def EntriesOK (nums : Slice Std.I64) : Prop := ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000

  def CostOK (c : Std.I64) : Prop := 1 ≤ c.val ∧ c.val ≤ 1000000

  def IsConstant (nums : Slice Std.I64) : Prop := ∀ x ∈ vals nums, ∀ y ∈ vals nums, x = y

  /-- Let C = 1000000007. For an integer T, define d_i(T) = T - nums[i] for 0 <= i < len(nums), S(T) = sum_{i=0}^{len(nums)-1} d_i(T), Max(T) = max_{0 <= i < len(nums)} d_i(T), and P(T) = min(floor(S(T)/2), S(T) - Max(T)). Then the function returns a result r, and r is the unique integer such that 0 <= r < C and r is congruent modulo C to M, where M = min { p*cost2 + (S(T)-2*p)*cost1 : T is an integer with T >= max_i nums[i], and p is an integer with 0 <= p <= P(T) }.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ (r : Std.I64) (M : Int),
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          IsMinCost nums cost1.val cost2.val M ∧
          0 ≤ r.val ∧ r.val < C ∧ r.val ≡ M [ZMOD C] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ (r : Std.I64) (M : Int),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            IsMinCost nums cost1.val cost2.val M ∧
            0 ≤ r.val ∧ r.val < C ∧ r.val ≡ M [ZMOD C]) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail: it does not overflow, panic, or access an out-of-bounds index.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ r : Std.I64, min_cost_to_equalize_array nums cost1 cost2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ r : Std.I64, min_cost_to_equalize_array nums cost1 cost2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∀ r : Std.I64, min_cost_to_equalize_array nums cost1 cost2 = ok r → 0 ≤ r.val ∧ r.val < C := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∀ r : Std.I64, min_cost_to_equalize_array nums cost1 cost2 = ok r → 0 ≤ r.val ∧ r.val < C) := by
    sorry

  /-- The function returns 0.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j]; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hconst : IsConstant nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      min_cost_to_equalize_array nums cost1 cost2 = ok 0#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hconst : IsConstant nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), min_cost_to_equalize_array nums cost1 cost2 = ok 0#i64) := by
    sorry

  /-- Let a = nums[0] and b = nums[1]. The function returns r with r = ((max(a,b) - min(a,b)) * cost1) mod 1000000007.
    Preconditions: len(nums) = 2; 1 <= nums[0] <= 1000000; 1 <= nums[1] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : len nums = 2)
      (h0 : 1 ≤ get nums 0 ∧ get nums 0 ≤ 1000000)
      (h1 : 1 ≤ get nums 1 ∧ get nums 1 ≤ 1000000)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ r : Std.I64,
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          r.val =
            ((max (get nums 0) (get nums 1) - min (get nums 0) (get nums 1)) * cost1.val) % C := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : len nums = 2)
        (h0 : 1 ≤ get nums 0 ∧ get nums 0 ≤ 1000000)
        (h1 : 1 ≤ get nums 1 ∧ get nums 1 ≤ 1000000)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ r : Std.I64,
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            r.val =
              ((max (get nums 0) (get nums 1) - min (get nums 0) (get nums 1)) * cost1.val) % C) := by
    sorry

  /-- Let B = max_{0 <= i < len(nums)} nums[i] and D = sum_{i=0}^{len(nums)-1} (B - nums[i]). The function returns r = (cost1 * D) mod 1000000007.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000; cost2 >= 2*cost1. -/
  theorem spec_6 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2)
      (hc2ge : 2 * cost1.val ≤ cost2.val) :
      ∃ r : Std.I64,
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          r.val = (cost1.val * D nums) % C := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2)
        (hc2ge : 2 * cost1.val ≤ cost2.val), ∃ r : Std.I64,
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            r.val = (cost1.val * D nums) % C) := by
    sorry

  /-- The function returns r = ((S0/2) * cost2) mod 1000000007.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000; cost2 < 2*cost1. Let B = max_i nums[i]. For each i define e_i = B - nums[i], S0 = sum_i e_i, and M0 = max_i e_i. Require S0 to be even and 2*M0 <= S0. -/
  theorem spec_7 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2)
      (hc2lt : cost2.val < 2 * cost1.val)
      (hS0even : S nums (B nums) % 2 = 0)
      (hM0 : 2 * Max nums (B nums) ≤ S nums (B nums)) :
      ∃ r : Std.I64,
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          r.val = ((S nums (B nums) / 2) * cost2.val) % C := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2)
        (hc2lt : cost2.val < 2 * cost1.val)
        (hS0even : S nums (B nums) % 2 = 0)
        (hM0 : 2 * Max nums (B nums) ≤ S nums (B nums)), ∃ r : Std.I64,
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            r.val = ((S nums (B nums) / 2) * cost2.val) % C) := by
    sorry

  /-- Let r be the result of the call on nums, cost1, cost2, and let r2 be the result of the call on nums2, cost1, cost2. Then r = r2.
    Preconditions: There is an integer n with 1 <= n <= 100000 such that len(nums) = n and len(nums2) = n; every entry of nums and nums2 lies between 1 and 1000000 inclusive; nums2 is a permutation of nums; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_8 (nums nums2 : Slice Std.I64) (cost1 cost2 : Std.I64) (n : Nat)
      (hn1 : len nums = n) (hn2 : len nums2 = n)
      (hn : 1 ≤ n ∧ n ≤ 100000)
      (hvals : EntriesOK nums) (hvals2 : EntriesOK nums2)
      (hperm : (vals nums).Perm (vals nums2))
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ (r r2 : Std.I64),
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          min_cost_to_equalize_array nums2 cost1 cost2 = ok r2 ∧ r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (cost1 cost2 : Std.I64) (n : Nat)
        (hn1 : len nums = n) (hn2 : len nums2 = n)
        (hn : 1 ≤ n ∧ n ≤ 100000)
        (hvals : EntriesOK nums) (hvals2 : EntriesOK nums2)
        (hperm : (vals nums).Perm (vals nums2))
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ (r r2 : Std.I64),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            min_cost_to_equalize_array nums2 cost1 cost2 = ok r2 ∧ r = r2) := by
    sorry

  /-- Let r be the result for nums with cost1, cost2, and let r2 be the result for nums2 with the same cost1, cost2. Then r = r2.
    Preconditions: There is an integer n with 1 <= n <= 100000 such that len(nums) = n and len(nums2) = n; every entry of nums and nums2 lies between 1 and 1000000 inclusive; there is an integer c such that nums2[i] = nums[i] + c for every 0 <= i < n; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (cost1 cost2 : Std.I64) (n : Nat) (c : Int)
      (hn1 : len nums = n) (hn2 : len nums2 = n)
      (hn : 1 ≤ n ∧ n ≤ 100000)
      (hvals : EntriesOK nums) (hvals2 : EntriesOK nums2)
      (hshift : ∀ i, i < n → get nums2 i = get nums i + c)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ (r r2 : Std.I64),
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          min_cost_to_equalize_array nums2 cost1 cost2 = ok r2 ∧ r = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (cost1 cost2 : Std.I64) (n : Nat) (c : Int)
        (hn1 : len nums = n) (hn2 : len nums2 = n)
        (hn : 1 ≤ n ∧ n ≤ 100000)
        (hvals : EntriesOK nums) (hvals2 : EntriesOK nums2)
        (hshift : ∀ i, i < n → get nums2 i = get nums i + c)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ (r r2 : Std.I64),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            min_cost_to_equalize_array nums2 cost1 cost2 = ok r2 ∧ r = r2) := by
    sorry

  /-- Let r be the result for nums, cost1, cost2, and let r2 be the result for nums, k*cost1, k*cost2. Then r2 = (k * r) mod 1000000007.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; every nums[i] lies between 1 and 1000000 inclusive; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000; k is a positive integer such that 1 <= k*cost1 <= 1000000 and 1 <= k*cost2 <= 1000000. -/
  theorem spec_10 (nums : Slice Std.I64) (cost1 cost2 : Std.I64) (k : Int)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2)
      (hk : 0 < k)
      (hk1 : 1 ≤ k * cost1.val ∧ k * cost1.val ≤ 1000000)
      (hk2 : 1 ≤ k * cost2.val ∧ k * cost2.val ≤ 1000000) :
      ∀ (c1' c2' : Std.I64), c1'.val = k * cost1.val → c2'.val = k * cost2.val →
        ∃ (r r2 : Std.I64),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            min_cost_to_equalize_array nums c1' c2' = ok r2 ∧
            r2.val = (k * r.val) % C := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64) (k : Int)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2)
        (hk : 0 < k)
        (hk1 : 1 ≤ k * cost1.val ∧ k * cost1.val ≤ 1000000)
        (hk2 : 1 ≤ k * cost2.val ∧ k * cost2.val ≤ 1000000), ∀ (c1' c2' : Std.I64), c1'.val = k * cost1.val → c2'.val = k * cost2.val →
          ∃ (r r2 : Std.I64),
            min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
              min_cost_to_equalize_array nums c1' c2' = ok r2 ∧
              r2.val = (k * r.val) % C) := by
    sorry

  /-- For a pair cost c, define M(c) = min { p*c + (S(T)-2*p)*cost1 : T is an integer with T >= max_i nums[i], and p is an integer with 0 <= p <= P(T) }, where S(T) = sum_i (T - nums[i]) and P(T) = min(floor(S(T)/2), S(T) - max_i (T - nums[i])). Let r_a and r_b be the results for cost2a and cost2b respectively. Then r_a is congruent to M(cost2a) modulo 1000000007, r_b is congruent to M(cost2b) modulo 1000000007, and M(cost2a) <= M(cost2b).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; every nums[i] lies between 1 and 1000000 inclusive; 1 <= cost1 <= 1000000; 1 <= cost2a <= cost2b <= 1000000. -/
  theorem spec_11 (nums : Slice Std.I64) (cost1 cost2a cost2b : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1)
      (hca : 1 ≤ cost2a.val ∧ cost2a.val ≤ cost2b.val)
      (hcb : cost2b.val ≤ 1000000) :
      ∃ (r_a r_b : Std.I64) (Ma Mb : Int),
        min_cost_to_equalize_array nums cost1 cost2a = ok r_a ∧
          min_cost_to_equalize_array nums cost1 cost2b = ok r_b ∧
          IsMinCost nums cost1.val cost2a.val Ma ∧
          IsMinCost nums cost1.val cost2b.val Mb ∧
          r_a.val ≡ Ma [ZMOD C] ∧ r_b.val ≡ Mb [ZMOD C] ∧ Ma ≤ Mb := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2a cost2b : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1)
        (hca : 1 ≤ cost2a.val ∧ cost2a.val ≤ cost2b.val)
        (hcb : cost2b.val ≤ 1000000), ∃ (r_a r_b : Std.I64) (Ma Mb : Int),
          min_cost_to_equalize_array nums cost1 cost2a = ok r_a ∧
            min_cost_to_equalize_array nums cost1 cost2b = ok r_b ∧
            IsMinCost nums cost1.val cost2a.val Ma ∧
            IsMinCost nums cost1.val cost2b.val Mb ∧
            r_a.val ≡ Ma [ZMOD C] ∧ r_b.val ≡ Mb [ZMOD C] ∧ Ma ≤ Mb) := by
    sorry

  /-- For an integer T define d_i(T) = T - nums[i], S(T) = sum_i d_i(T), Max(T) = max_i d_i(T), and P(T) = min(floor(S(T)/2), S(T) - Max(T)). Let M be the minimum value of p*cost2 + (S(T)-2*p)*cost1 over T >= max_i nums[i] and 0 <= p <= P(T). There exist an integer T0 >= max_i nums[i] and an integer p0 with 0 <= p0 <= P(T0) such that M = p0*cost2 + (S(T0)-2*p0)*cost1. Moreover, the array can be made all equal to T0 using exactly p0 pair operations and S(T0)-2*p0 single operations, for total cost M.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_12 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ (r : Std.I64) (M : Int),
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          IsMinCost nums cost1.val cost2.val M ∧
          ∃ (T0 : Int) (p0 s0 : Nat),
            B nums ≤ T0 ∧ (p0 : Int) ≤ P nums T0 ∧
              M = (p0 : Int) * cost2.val + (s0 : Int) * cost1.val ∧
              2 * (p0 : Int) + (s0 : Int) = S nums T0 ∧
              Achievable nums T0 p0 s0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ (r : Std.I64) (M : Int),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            IsMinCost nums cost1.val cost2.val M ∧
            ∃ (T0 : Int) (p0 s0 : Nat),
              B nums ≤ T0 ∧ (p0 : Int) ≤ P nums T0 ∧
                M = (p0 : Int) * cost2.val + (s0 : Int) * cost1.val ∧
                2 * (p0 : Int) + (s0 : Int) = S nums T0 ∧
                Achievable nums T0 p0 s0) := by
    sorry

  /-- For an integer c, define M(c) = min { p*cost2 + (S(T)-2*p)*c : T is an integer with T >= max_i nums[i], and p is an integer with 0 <= p <= P(T) }, where S(T)=sum_i (T-nums[i]) and P(T)=min(floor(S(T)/2), S(T)-max_i(T-nums[i])). Let r_a and r_b be the results for cost1a and cost1b respectively. Then r_a is congruent to M(cost1a) modulo 1000000007, r_b is congruent to M(cost1b) modulo 1000000007, and M(cost1a) <= M(cost1b).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1a <= cost1b <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_13 (nums : Slice Std.I64) (cost1a cost1b cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hca : 1 ≤ cost1a.val ∧ cost1a.val ≤ cost1b.val)
      (hcb : cost1b.val ≤ 1000000)
      (hc2 : CostOK cost2) :
      ∃ (r_a r_b : Std.I64) (Ma Mb : Int),
        min_cost_to_equalize_array nums cost1a cost2 = ok r_a ∧
          min_cost_to_equalize_array nums cost1b cost2 = ok r_b ∧
          IsMinCost nums cost1a.val cost2.val Ma ∧
          IsMinCost nums cost1b.val cost2.val Mb ∧
          r_a.val ≡ Ma [ZMOD C] ∧ r_b.val ≡ Mb [ZMOD C] ∧ Ma ≤ Mb := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1a cost1b cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hca : 1 ≤ cost1a.val ∧ cost1a.val ≤ cost1b.val)
        (hcb : cost1b.val ≤ 1000000)
        (hc2 : CostOK cost2), ∃ (r_a r_b : Std.I64) (Ma Mb : Int),
          min_cost_to_equalize_array nums cost1a cost2 = ok r_a ∧
            min_cost_to_equalize_array nums cost1b cost2 = ok r_b ∧
            IsMinCost nums cost1a.val cost2.val Ma ∧
            IsMinCost nums cost1b.val cost2.val Mb ∧
            r_a.val ≡ Ma [ZMOD C] ∧ r_b.val ≡ Mb [ZMOD C] ∧ Ma ≤ Mb) := by
    sorry

  /-- Let B = max_i nums[i], D = sum_i (B - nums[i]), and let M be the minimum from spec_1 for this input. Then M <= cost1 * D. Furthermore, M = 0 if and only if nums[0] = nums[1] = ... = nums[len(nums)-1].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= cost1 <= 1000000; 1 <= cost2 <= 1000000. -/
  theorem spec_14 (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
      (hlen : LenOK nums) (hvals : EntriesOK nums)
      (hc1 : CostOK cost1) (hc2 : CostOK cost2) :
      ∃ (r : Std.I64) (M : Int),
        min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
          IsMinCost nums cost1.val cost2.val M ∧
          M ≤ cost1.val * D nums ∧
          (M = 0 ↔ IsConstant nums) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (cost1 cost2 : Std.I64)
        (hlen : LenOK nums) (hvals : EntriesOK nums)
        (hc1 : CostOK cost1) (hc2 : CostOK cost2), ∃ (r : Std.I64) (M : Int),
          min_cost_to_equalize_array nums cost1 cost2 = ok r ∧
            IsMinCost nums cost1.val cost2.val M ∧
            M ≤ cost1.val * D nums ∧
            (M = 0 ↔ IsConstant nums)) := by
    sorry

  end AegisSpec.MinCostToEqualizeArray
