import Aegis.SingleNumber.Code.Funs

/-!
# Specifications of `Aegis.SingleNumber.single_number`

LeetCode problem `single-number-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SingleNumber

def cnt (v : Int) (l : List Std.I64) : Nat := (l.filter (fun x => x.val = v)).length

def singletonValues (l : List Std.I64) : List Int :=
  ((l.map (fun x => x.val)).eraseDups).filter (fun v => cnt v l = 1)

def sumSingletons (l : List Std.I64) : Int := (singletonValues l).foldl (fun acc v => acc + v) 0

def primitiveOps (nums : Slice Std.I64) : Nat := 3 * nums.val.length + 5 * nums.val.length + 8

def extraWords : Nat := 4

/-- Whenever the function returns a result r, len(r) = 2 and for every integer v, v is equal to r[0] or r[1] if and only if cnt(v, nums) = 1. Thus r contains exactly the two distinct values that occur exactly once in nums, in either order.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      r.val.length = 2 ∧ ∃ a b : Std.I64, r.val = [a, b] ∧
        ∀ v : Int, (v = a.val ∨ v = b.val) ↔ cnt v nums.val = 1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      r.val.length = 2 ∧ ∃ a b : Std.I64, r.val = [a, b] ∧
        ∀ v : Int, (v = a.val ∨ v = b.val) ↔ cnt v nums.val = 1) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∃ r, Aegis.SingleNumber.single_number nums = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∃ r, Aegis.SingleNumber.single_number nums = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, every entry of r occurs exactly once in nums: for every j with 0 <= j < len(r), cnt(r[j], nums) = 1.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (j : Nat) (hj : j < r.val.length), cnt (r.val.get ⟨j, hj⟩).val nums.val = 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (j : Nat) (hj : j < r.val.length), cnt (r.val.get ⟨j, hj⟩).val nums.val = 1) := by
  sorry

/-- Whenever the function returns a result r, every entry of r is an element of nums: for every j with 0 <= j < len(r), there exists i with 0 <= i < len(nums) and nums[i] = r[j].
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (j : Nat) (hj : j < r.val.length),
        ∃ (i : Nat) (hi : i < nums.val.length),
          (nums.val.get ⟨i, hi⟩).val = (r.val.get ⟨j, hj⟩).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (j : Nat) (hj : j < r.val.length),
        ∃ (i : Nat) (hi : i < nums.val.length),
          (nums.val.get ⟨i, hi⟩).val = (r.val.get ⟨j, hj⟩).val) := by
  sorry

/-- Whenever the function returns a result r, every value that occurs exactly once in nums is an entry of r: for every i with 0 <= i < len(nums), if cnt(nums[i], nums) = 1 then there exists j with 0 <= j < len(r) and r[j] = nums[i].
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (i : Nat) (hi : i < nums.val.length),
        cnt (nums.val.get ⟨i, hi⟩).val nums.val = 1 →
          ∃ (j : Nat) (hj : j < r.val.length),
            (r.val.get ⟨j, hj⟩).val = (nums.val.get ⟨i, hi⟩).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ (i : Nat) (hi : i < nums.val.length),
        cnt (nums.val.get ⟨i, hi⟩).val nums.val = 1 →
          ∃ (j : Nat) (hj : j < r.val.length),
            (r.val.get ⟨j, hj⟩).val = (nums.val.get ⟨i, hi⟩).val) := by
  sorry

/-- Whenever the function returns a result r, no value that occurs exactly twice in nums is an entry of r: for every integer v with cnt(v, nums) = 2 and every j with 0 <= j < len(r), r[j] != v.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, cnt v nums.val = 2 →
        ∀ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val ≠ v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, cnt v nums.val = 2 →
        ∀ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val ≠ v) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, cnt(v, r) = 1 if cnt(v, nums) = 1, and cnt(v, r) = 0 otherwise, where cnt(v, r) = |{ j | 0 <= j < len(r) and r[j] = v }|.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int,
        (cnt v nums.val = 1 → cnt v r.val = 1) ∧ (cnt v nums.val ≠ 1 → cnt v r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int,
        (cnt v nums.val = 1 → cnt v r.val = 1) ∧ (cnt v nums.val ≠ 1 → cnt v r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, r[0] + r[1] equals the sum, as an integer, of all distinct values v satisfying cnt(v, nums) = 1.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r → r.val.length = 2 →
      ∃ a b : Std.I64, r.val = [a, b] ∧ a.val + b.val = sumSingletons nums.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r → r.val.length = 2 →
      ∃ a b : Std.I64, r.val = [a, b] ∧ a.val + b.val = sumSingletons nums.val) := by
  sorry

/-- Whenever the function returns a result r, every value that occurs in nums but is not an entry of r occurs exactly twice in nums: for every integer v, if cnt(v, nums) > 0 and for every j with 0 <= j < len(r) we have r[j] != v, then cnt(v, nums) = 2.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, 0 < cnt v nums.val →
        (∀ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val ≠ v) →
          cnt v nums.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, 0 < cnt v nums.val →
        (∀ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val ≠ v) →
          cnt v nums.val = 2) := by
  sorry

/-- Whenever single_number(nums) returns r and single_number(p) returns r', if len(r) = len(r') = 2 then the unordered pairs of entries agree: either r'[0] = r[0] and r'[1] = r[1], or r'[0] = r[1] and r'[1] = r[0].
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. Let p be any sequence of 64-bit integers such that len(p) = len(nums) and cnt(v, p) = cnt(v, nums) for every integer v. -/
theorem spec_10 (nums p : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2)
    (hlen_p : p.val.length = nums.val.length)
    (hcnt_p : ∀ v : Int, cnt v p.val = cnt v nums.val) :
    ∀ r r', Aegis.SingleNumber.single_number nums = Result.ok r →
      Aegis.SingleNumber.single_number p = Result.ok r' →
        r.val.length = 2 → r'.val.length = 2 →
          ∃ a b a' b' : Std.I64, r.val = [a, b] ∧ r'.val = [a', b'] ∧
            ((a'.val = a.val ∧ b'.val = b.val) ∨ (a'.val = b.val ∧ b'.val = a.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums p : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2)
    (hlen_p : p.val.length = nums.val.length)
    (hcnt_p : ∀ v : Int, cnt v p.val = cnt v nums.val), ∀ r r', Aegis.SingleNumber.single_number nums = Result.ok r →
      Aegis.SingleNumber.single_number p = Result.ok r' →
        r.val.length = 2 → r'.val.length = 2 →
          ∃ a b a' b' : Std.I64, r.val = [a, b] ∧ r'.val = [a', b'] ∧
            ((a'.val = a.val ∧ b'.val = b.val) ∨ (a'.val = b.val ∧ b'.val = a.val))) := by
  sorry

/-- Whenever the function returns a result r, no value occurs more than once in r: for every integer v, cnt(v, r) <= 1, where cnt(v, r) = |{ j | 0 <= j < len(r) and r[j] = v }|.
  Preconditions: Let cnt(v, nums) = |{ i | 0 <= i < len(nums) and nums[i] = v }|. The input nums satisfies: 2 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; the set { v | cnt(v, nums) = 1 } has exactly two distinct elements; and for every integer w, if cnt(w, nums) > 0 and cnt(w, nums) != 1 then cnt(w, nums) = 2. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2) :
    ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, cnt v r.val ≤ 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 30000)
    (hvalues : ∀ x ∈ nums.val, -2147483648 ≤ x.val ∧ x.val ≤ 2147483647)
    (hexactly_two : ∃ a b : Int, a ≠ b ∧ ∀ v : Int, cnt v nums.val = 1 ↔ v = a ∨ v = b)
    (hno_other : ∀ w : Int, 0 < cnt w nums.val → cnt w nums.val ≠ 1 → cnt w nums.val = 2), ∀ r, Aegis.SingleNumber.single_number nums = Result.ok r →
      ∀ v : Int, cnt v r.val ≤ 1) := by
  sorry

end AegisSpec.SingleNumber
