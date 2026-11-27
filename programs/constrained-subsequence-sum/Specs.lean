import Aegis.ConstrainedSubsetSum.Code.Funs

/-!
# Specifications of `Aegis.ConstrainedSubsetSum.constrained_subset_sum`

LeetCode problem `constrained-subsequence-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ConstrainedSubsetSum

def ints (a : Slice Std.I64) : List Int := a.val.map (fun x => x.val)

def size (a : Slice Std.I64) : Nat := a.val.length

def elem (a : Slice Std.I64) (i : Nat) : Int :=
  match a.val[i]? with
  | some x => x.val
  | none => 0

def IsAdmissible (a : Slice Std.I64) (k : Int) (is : List Nat) : Prop :=
  is ≠ [] ∧
    List.Pairwise (· < ·) is ∧
    (∀ i ∈ is, i < size a) ∧
    ∀ p ∈ is.zip is.tail, (p.2 : Int) - (p.1 : Int) ≤ k

def selSum (a : Slice Std.I64) (is : List Nat) : Int := (is.map (fun i => elem a i)).sum

def posSum (a : Slice Std.I64) : Int := ((ints a).filter (fun x => 0 < x)).sum

def rangeSum (a : Slice Std.I64) (i j : Nat) : Int := ((ints a).drop i).take (j - i + 1) |>.sum

def IsSubarraySum (a : Slice Std.I64) (s : Int) : Prop :=
  ∃ i j, i ≤ j ∧ j < size a ∧ s = rangeSum a i j

def revSlice (a : Slice Std.I64) : Slice Std.I64 where
  leng := a.val.reverse.length
  list := Aeneas.Data.ListN.ListN.fromList a.val.reverse
  bound := by
    have h1 : a.val.length ≤ Usize.max := by
      have h2 : a.val.length = a.leng := Aeneas.Data.ListN.ListN_length a.list
      rw [h2]
      exact a.bound
    have h3 : a.val.reverse.length = a.val.length := List.length_reverse
    rw [h3]
    exact h1

/-- Let S be the set of all integers s for which there exists an index sequence (i_0, ..., i_{m-1}) such that m >= 1, 0 <= i_0 < ... < i_{m-1} < len(nums), i_{t+1} - i_t <= k for every 0 <= t < m-1, and s = nums[i_0] + ... + nums[i_{m-1}]. The function returns a result r (so it does not fail) such that r is the maximum of S: r is in S and s <= r for every s in S. Equivalently, r is the maximum sum of a non-empty subsequence of nums whose selected indices, taken in increasing order, have every gap between consecutive selected indices at most k.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        (∃ is : List Nat, IsAdmissible nums k.val is ∧ selSum nums is = r.val) ∧
        (∀ is : List Nat, IsAdmissible nums k.val is → selSum nums is ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        (∃ is : List Nat, IsAdmissible nums k.val is ∧ selSum nums is = r.val) ∧
        (∀ is : List Nat, IsAdmissible nums k.val is → selSum nums is ≤ r.val)) := by
  sorry

/-- The function returns a result r and, for every index i with 0 <= i < len(nums), nums[i] <= r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∀ i, i < size nums → elem nums i ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∀ i, i < size nums → elem nums i ≤ r.val) := by
  sorry

/-- Let P be the sum of nums[i] over all indices i with nums[i] > 0, using P = 0 if there are no positive entries. The function returns a result r and r <= P.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val ≤ posSum nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val ≤ posSum nums) := by
  sorry

/-- The function returns a result r; it does not overflow, panic, or fail on any input satisfying the preconditions.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64, Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r) := by
  sorry

/-- The function returns a result r and r = nums[0].
  Preconditions: len(nums) = 1; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : size nums = 1) (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val = elem nums 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : size nums = 1) (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val = elem nums 0) := by
  sorry

/-- The function returns a result r and r = max { nums[a] + nums[a+1] + ... + nums[b] | 0 <= a <= b < len(nums) }, i.e. the maximum sum of a non-empty contiguous subarray of nums.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; k = 1; for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk : k.val = 1)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        IsSubarraySum nums r.val ∧
        (∀ s, IsSubarraySum nums s → s ≤ r.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk : k.val = 1)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        IsSubarraySum nums r.val ∧
        (∀ s, IsSubarraySum nums s → s ≤ r.val)) := by
  sorry

/-- Let P be the sum of nums[i] over all indices i with nums[i] > 0, using P = 0 if there are no positive entries, and let M be the maximum of nums[i] over 0 <= i < len(nums). If there exists an index i with nums[i] > 0, then the function returns result r = P; otherwise it returns result r = M.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); k >= len(nums) - 1; for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hk_ge : (size nums : Int) - 1 ≤ k.val)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ((∃ i, i < size nums ∧ 0 < elem nums i) → r.val = posSum nums) ∧
        ((¬ ∃ i, i < size nums ∧ 0 < elem nums i) →
          (∃ i, i < size nums ∧ r.val = elem nums i) ∧
            ∀ i, i < size nums → elem nums i ≤ r.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hk_ge : (size nums : Int) - 1 ≤ k.val)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ((∃ i, i < size nums ∧ 0 < elem nums i) → r.val = posSum nums) ∧
        ((¬ ∃ i, i < size nums ∧ 0 < elem nums i) →
          (∃ i, i < size nums ∧ r.val = elem nums i) ∧
            ∀ i, i < size nums → elem nums i ≤ r.val)) := by
  sorry

/-- The function returns a result r and r = max { nums[i] | 0 <= i < len(nums) }.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), nums[i] <= 0 and -10^4 <= nums[i] <= 10^4. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hnonpos : ∀ i, i < size nums → elem nums i ≤ 0)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        (∃ i, i < size nums ∧ r.val = elem nums i) ∧
        (∀ i, i < size nums → elem nums i ≤ r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hnonpos : ∀ i, i < size nums → elem nums i ≤ 0)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        (∃ i, i < size nums ∧ r.val = elem nums i) ∧
        (∀ i, i < size nums → elem nums i ≤ r.val)) := by
  sorry

/-- The function returns a result r and r = nums[0] + nums[1] + ... + nums[len(nums)-1].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^4. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hnonneg : ∀ i, i < size nums → 0 ≤ elem nums i)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val = (ints nums).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hnonneg : ∀ i, i < size nums → 0 ≤ elem nums i)
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧ r.val = (ints nums).sum) := by
  sorry

/-- The function returns a result r and there exists an index sequence (i_0, ..., i_{m-1}) such that m >= 1, 0 <= i_0 < ... < i_{m-1} < len(nums), i_{t+1} - i_t <= k for every 0 <= t < m-1, and r = nums[i_0] + ... + nums[i_{m-1}].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∃ is : List Nat, IsAdmissible nums k.val is ∧ r.val = selSum nums is := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∃ is : List Nat, IsAdmissible nums k.val is ∧ r.val = selSum nums is) := by
  sorry

/-- The function returns a result r and, for every index sequence (i_0, ..., i_{m-1}) with m >= 1, 0 <= i_0 < ... < i_{m-1} < len(nums), and i_{t+1} - i_t <= k for every 0 <= t < m-1, we have nums[i_0] + ... + nums[i_{m-1}] <= r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∀ is : List Nat, IsAdmissible nums k.val is → selSum nums is ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        ∀ is : List Nat, IsAdmissible nums k.val is → selSum nums is ≤ r.val) := by
  sorry

/-- Let r1 be the result of constrained_subset_sum nums k1 and let r2 be the result of constrained_subset_sum nums k2. Both calls return results and r1 <= r2.
  Preconditions: For every slice nums and all integers k1, k2 with 1 <= len(nums) <= 100000, 1 <= k1 <= k2 <= len(nums), and every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_12 (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk1_lb : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r1 r2 : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k1 = ok r1 ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk1_lb : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r1 r2 : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k1 = ok r1 ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Let rev be the slice of length len(nums) with rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). Let r be the result of constrained_subset_sum nums k and let r' be the result of constrained_subset_sum rev k. Both calls return results and r = r'.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r r' : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum (revSlice nums) k = ok r' ∧
        r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hrange : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r r' : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum (revSlice nums) k = ok r' ∧
        r.val = r'.val) := by
  sorry

/-- Let r be the result of constrained_subset_sum nums k and let r' be the result of constrained_subset_sum nums' k. Both calls return results and r <= r'.
  Preconditions: For any two slices nums and nums' with len(nums) = len(nums') and 1 <= len(nums) <= 100000, any integer k with 1 <= k <= len(nums), and every i with 0 <= i < len(nums), -10^4 <= nums[i] <= nums'[i] <= 10^4. -/
theorem spec_14 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_eq : size nums = size nums')
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hle : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ elem nums' i ∧
      elem nums' i ≤ 10000) :
    ∃ r r' : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum nums' k = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_eq : size nums = size nums')
    (hlen_pos : 1 ≤ size nums) (hlen_le : size nums ≤ 100000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (size nums : Int))
    (hle : ∀ i, i < size nums → -10000 ≤ elem nums i ∧ elem nums i ≤ elem nums' i ∧
      elem nums' i ≤ 10000), ∃ r r' : Std.I64,
      Aegis.ConstrainedSubsetSum.constrained_subset_sum nums k = ok r ∧
        Aegis.ConstrainedSubsetSum.constrained_subset_sum nums' k = ok r' ∧ r.val ≤ r'.val) := by
  sorry

end AegisSpec.ConstrainedSubsetSum
