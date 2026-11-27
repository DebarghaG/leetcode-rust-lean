import Aegis.SumIndicesWithKSetBits.Code.Funs

/-!
# Specifications of `Aegis.SumIndicesWithKSetBits.sum_indices_with_k_set_bits`

LeetCode problem `sum-of-values-at-indices-with-k-set-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumIndicesWithKSetBits

open Aegis.SumIndicesWithKSetBits

def pc : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + pc ((n + 1) / 2)
termination_by n => n
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

def elem (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i default).val

def sumWhere (nums : Slice Std.I64) (p : Nat → Prop) [DecidablePred p] : Int :=
  (((List.range nums.val.length).filter (fun i => decide (p i))).map (elem nums)).sum

def sumK (nums : Slice Std.I64) (k : Int) : Int := sumWhere nums (fun i => (pc i : Int) = k)

def sumNotK (nums : Slice Std.I64) (k : Int) : Int := sumWhere nums (fun i => (pc i : Int) ≠ k)

def total (nums : Slice Std.I64) : Int := (nums.val.map (fun x => x.val)).sum

def AgreesExcept (nums nums' : Slice Std.I64) (i : Nat) (v : Int) : Prop :=
  nums'.val.length = nums.val.length ∧
    elem nums' i = v ∧
    ∀ j, j < nums.val.length → j ≠ i → elem nums' j = elem nums j

/-- Let pc(n) denote the number of 1-bits in the binary representation of the nonnegative integer n (pc(0)=0). The function returns a result r, and r = sum_{i : 0 <= i < len(nums) and pc(i) = k} nums[i]. If no index i satisfies the condition, r is the empty sum 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = sumK nums k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = sumK nums k.val) := by
  sorry

/-- The function returns a result r (it does not panic, fail, or overflow).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∃ r, sum_indices_with_k_set_bits nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∃ r, sum_indices_with_k_set_bits nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ r, sum_indices_with_k_set_bits nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ r, sum_indices_with_k_set_bits nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val ≤ total nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val ≤ total nums) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n (pc(0)=0). Whenever the function returns a result r, r = 0 if and only if there is no index i such that 0 <= i < len(nums) and pc(i) = k.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ r, sum_indices_with_k_set_bits nums k = ok r →
      (r.val = 0 ↔ ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ r, sum_indices_with_k_set_bits nums k = ok r →
      (r.val = 0 ↔ ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val)) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n (pc(0)=0). If k = 0, then the function returns a result r with r = nums[0].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10)
    (hk0 : k.val = 0) :
    ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = elem nums 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10)
    (hk0 : k.val = 0), ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = elem nums 0) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n. Since len(nums) <= 1000, every index i satisfies 0 <= i <= 999; the smallest nonnegative integer with 10 set bits is 1023, so no index has pc(i) >= 10. Therefore if k = 10, the function returns a result r with r = 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10)
    (hk10 : k.val = 10) :
    ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10)
    (hk10 : k.val = 10), ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ r.val = 0) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n. For every index i with 0 <= i < len(nums) and pc(i) = k, the function returns a result r with r >= nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ i, i < nums.val.length → (pc i : Int) = k.val →
      ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ elem nums i ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ i, i < nums.val.length → (pc i : Int) = k.val →
      ∃ r, sum_indices_with_k_set_bits nums k = ok r ∧ elem nums i ≤ r.val) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n. For every index i with 0 <= i < len(nums) and pc(i) != k, whenever the function returns a result r, r + nums[i] <= sum_{j=0}^{len(nums)-1} nums[j].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val →
      ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val + elem nums i ≤ total nums := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val →
      ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val + elem nums i ≤ total nums) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n. For every index i with 0 <= i < len(nums) and pc(i) != k, and every integer v with 1 <= v <= 100000, let nums' be the slice of the same length such that nums'[i] = v and nums'[j] = nums[j] for all j != i. The function returns the same result on (nums, k) and on (nums', k): there exist r and r' such that the call on (nums, k) returns r, the call on (nums', k) returns r', and r = r'.
  Preconditions: 1 <= len(nums) <= 1000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100000; and 0 <= k <= 10. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ j, j < nums.val.length → 1 ≤ elem nums j ∧ elem nums j ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val →
      ∀ v, 1 ≤ v → v ≤ 100000 →
        ∀ nums', AgreesExcept nums nums' i v →
          ∃ r r', sum_indices_with_k_set_bits nums k = ok r ∧
            sum_indices_with_k_set_bits nums' k = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ j, j < nums.val.length → 1 ≤ elem nums j ∧ elem nums j ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ i, i < nums.val.length → (pc i : Int) ≠ k.val →
      ∀ v, 1 ≤ v → v ≤ 100000 →
        ∀ nums', AgreesExcept nums nums' i v →
          ∃ r r', sum_indices_with_k_set_bits nums k = ok r ∧
            sum_indices_with_k_set_bits nums' k = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let pc(n) denote the number of 1-bits in the binary representation of n. Whenever the function returns a result r, r + sum_{i : 0 <= i < len(nums) and pc(i) != k} nums[i] = sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and 0 <= k <= 10. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10) :
    ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val + sumNotK nums k.val = total nums := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 1000)
    (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 10), ∀ r, sum_indices_with_k_set_bits nums k = ok r → r.val + sumNotK nums k.val = total nums) := by
  sorry

end AegisSpec.SumIndicesWithKSetBits
