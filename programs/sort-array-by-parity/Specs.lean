import Aegis.SortArrayByParity.Code.Funs

/-!
# Specifications of `Aegis.SortArrayByParity.sort_array_by_parity`

LeetCode problem `sort-array-by-parity`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortArrayByParity

def countVal (l : List Std.I64) (v : Int) : Nat := l.countP fun x => x.val = v

def countEven (l : List Std.I64) : Nat := l.countP fun x => x.val % 2 = 0

def allInRange (l : List Std.I64) (lo hi : Nat) (p : Int → Prop) : Prop :=
  ∀ i (h : i < l.length), lo ≤ i → i < hi → p l[i].val

/-- The function returns a result r such that: (1) len(r) = len(nums); (2) for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(nums) and nums[j] = v; (3) there exists an integer k with 0 <= k <= len(r) such that every r[i] with 0 <= i < k satisfies r[i] mod 2 = 0, and every r[i] with k <= i < len(r) satisfies r[i] mod 2 = 1.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∃ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ v : Int, countVal r.val v = countVal nums.val v) ∧
      ∃ k, k ≤ r.val.length ∧
        allInRange r.val 0 k (fun x => x % 2 = 0) ∧
        allInRange r.val k r.val.length (fun x => x % 2 = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∃ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ v : Int, countVal r.val v = countVal nums.val v) ∧
      ∃ k, k ≤ r.val.length ∧
        allInRange r.val 0 k (fun x => x % 2 = 0) ∧
        allInRange r.val k r.val.length (fun x => x % 2 = 1)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∃ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∃ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(nums) and nums[j] = v.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∀ v : Int, countVal r.val v = countVal nums.val v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∀ v : Int, countVal r.val v = countVal nums.val v) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k with 0 <= k <= len(r) such that every r[i] with 0 <= i < k satisfies r[i] mod 2 = 0, and every r[i] with k <= i < len(r) satisfies r[i] mod 2 = 1.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∃ k, k ≤ r.val.length ∧
        allInRange r.val 0 k (fun x => x % 2 = 0) ∧
        allInRange r.val k r.val.length (fun x => x % 2 = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∃ k, k ≤ r.val.length ∧
        allInRange r.val 0 k (fun x => x % 2 = 0) ∧
        allInRange r.val k r.val.length (fun x => x % 2 = 1)) := by
  sorry

/-- Let e be the number of indices i with 0 <= i < len(nums) and nums[i] mod 2 = 0. Whenever the function returns a result r, 0 <= e <= len(r), every r[i] with 0 <= i < e satisfies r[i] mod 2 = 0, and every r[i] with e <= i < len(r) satisfies r[i] mod 2 = 1.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      let e := countEven nums.val
      0 ≤ e ∧ e ≤ r.val.length ∧
        allInRange r.val 0 e (fun x => x % 2 = 0) ∧
        allInRange r.val e r.val.length (fun x => x % 2 = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      let e := countEven nums.val
      0 ≤ e ∧ e ≤ r.val.length ∧
        allInRange r.val 0 e (fun x => x % 2 = 0) ∧
        allInRange r.val e r.val.length (fun x => x % 2 = 1)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index j with 0 <= j < len(nums) and nums[j] mod 2 = 0, then len(r) >= 1 and r[0] mod 2 = 0.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      (∃ (j : Nat) (h : j < nums.val.length), nums.val[j].val % 2 = 0) →
      ∃ (h : 1 ≤ r.val.length), r.val[0].val % 2 = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      (∃ (j : Nat) (h : j < nums.val.length), nums.val[j].val % 2 = 0) →
      ∃ (h : 1 ≤ r.val.length), r.val[0].val % 2 = 0) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index j with 0 <= j < len(nums) and nums[j] mod 2 = 1, then len(r) >= 1 and r[len(r)-1] mod 2 = 1.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      (∃ (j : Nat) (h : j < nums.val.length), nums.val[j].val % 2 = 1) →
      ∃ (h : 1 ≤ r.val.length), r.val[r.val.length - 1].val % 2 = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      (∃ (j : Nat) (h : j < nums.val.length), nums.val[j].val % 2 = 1) →
      ∃ (h : 1 ≤ r.val.length), r.val[r.val.length - 1].val % 2 = 1) := by
  sorry

/-- Whenever the function returns a result r, the number of indices i with 0 <= i < len(r) and r[i] mod 2 = 0 equals the number of indices j with 0 <= j < len(nums) and nums[j] mod 2 = 0.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      countEven r.val = countEven nums.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      countEven r.val = countEven nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i] <= 5000.
  Preconditions: 1 <= len(nums) <= 5000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 5000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000) :
    ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∀ i (h : i < r.val.length), 0 ≤ r.val[i].val ∧ r.val[i].val ≤ 5000 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 5000)
    (hval : ∀ i (h : i < nums.val.length), 0 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 5000), ∀ r, Aegis.SortArrayByParity.sort_array_by_parity nums = ok r →
      ∀ i (h : i < r.val.length), 0 ≤ r.val[i].val ∧ r.val[i].val ≤ 5000) := by
  sorry

end AegisSpec.SortArrayByParity
