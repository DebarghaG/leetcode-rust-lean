import Aegis.ArraySign.Code.Funs

/-!
# Specifications of `Aegis.ArraySign.array_sign`

LeetCode problem `sign-of-the-product-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ArraySign (array_sign)

namespace AegisSpec.ArraySign

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def signFun (x : ℤ) : ℤ := if x > 0 then 1 else if x < 0 then -1 else 0

def exactProd (nums : Slice Std.I64) : ℤ := List.prod (vals nums)

def negCount (nums : Slice Std.I64) : ℕ := (vals nums).countP (fun x => decide (x < 0))

def first (nums : Slice Std.I64) : ℤ := (vals nums).headD 0

/-- Let P = product_{i=0}^{len(nums)-1} nums[i] be the exact mathematical integer product, not a 64-bit computation. Whenever array_sign(nums) returns a result r, r = signFunc(P), where signFunc(x) = 1 if x > 0, signFunc(x) = -1 if x < 0, and signFunc(x) = 0 if x = 0. Equivalently: if some nums[i] = 0 then r = 0; otherwise r = 1 when the number of indices i with nums[i] < 0 is even, and r = -1 when that number is odd.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r) :
    r.val = signFun (exactProd nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r), r.val = signFun (exactProd nums)) := by
  sorry

/-- For every nums satisfying the preconditions, array_sign(nums) returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
    ∃ r : Std.I64, array_sign nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∃ r : Std.I64, array_sign nums = ok r) := by
  sorry

/-- Whenever array_sign(nums) returns a result r, r is one of -1, 0, or 1 (equivalently, -1 <= r <= 1 and r is not any other integer).
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r) :
    r.val = -1 ∨ r.val = 0 ∨ r.val = 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r), r.val = -1 ∨ r.val = 0 ∨ r.val = 1) := by
  sorry

/-- Whenever array_sign(nums) returns a result r with r = 0, there exists an index i such that 0 <= i < len(nums) and nums[i] = 0.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r) (hr : r.val = 0) :
    ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val.get ⟨i, hi⟩).val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (h : array_sign nums = ok r) (hr : r.val = 0), ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val.get ⟨i, hi⟩).val = 0) := by
  sorry

/-- If there exists an index i with 0 <= i < len(nums) and nums[i] = 0, then whenever array_sign(nums) returns a result r, r = 0.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_zero : ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val.get ⟨i, hi⟩).val = 0)
    (r : Std.I64) (h : array_sign nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_zero : ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val.get ⟨i, hi⟩).val = 0)
    (r : Std.I64) (h : array_sign nums = ok r), r.val = 0) := by
  sorry

/-- Assume every entry of nums is nonzero: for every i with 0 <= i < len(nums), nums[i] != 0. Let k be the number of indices i with nums[i] < 0. Whenever array_sign(nums) returns a result r, r = 1 if k is even and r = -1 if k is odd.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_nz : ∀ x ∈ nums.val, x.val ≠ 0)
    (r : Std.I64) (h : array_sign nums = ok r) :
    (negCount nums % 2 = 0 → r.val = 1) ∧ (negCount nums % 2 = 1 → r.val = -1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_nz : ∀ x ∈ nums.val, x.val ≠ 0)
    (r : Std.I64) (h : array_sign nums = ok r), (negCount nums % 2 = 0 → r.val = 1) ∧ (negCount nums % 2 = 1 → r.val = -1)) := by
  sorry

/-- If len(nums) = 1, then whenever array_sign(nums) returns a result r, r = 1 if nums[0] > 0, r = -1 if nums[0] < 0, and r = 0 if nums[0] = 0.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_len_one : nums.val.length = 1)
    (r : Std.I64) (h : array_sign nums = ok r) :
    r.val = signFun (first nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_len_one : nums.val.length = 1)
    (r : Std.I64) (h : array_sign nums = ok r), r.val = signFun (first nums)) := by
  sorry

/-- If every entry of nums is positive (for every i with 0 <= i < len(nums), nums[i] > 0), then whenever array_sign(nums) returns a result r, r = 1.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_pos : ∀ x ∈ nums.val, 0 < x.val)
    (r : Std.I64) (h : array_sign nums = ok r) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_pos : ∀ x ∈ nums.val, 0 < x.val)
    (r : Std.I64) (h : array_sign nums = ok r), r.val = 1) := by
  sorry

/-- If every entry of nums is negative (for every i with 0 <= i < len(nums), nums[i] < 0), then whenever array_sign(nums) returns a result r, r = 1 when len(nums) is even and r = -1 when len(nums) is odd.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_neg : ∀ x ∈ nums.val, x.val < 0)
    (r : Std.I64) (h : array_sign nums = ok r) :
    (nums.val.length % 2 = 0 → r.val = 1) ∧ (nums.val.length % 2 = 1 → r.val = -1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_neg : ∀ x ∈ nums.val, x.val < 0)
    (r : Std.I64) (h : array_sign nums = ok r), (nums.val.length % 2 = 0 → r.val = 1) ∧ (nums.val.length % 2 = 1 → r.val = -1)) := by
  sorry

/-- Whenever array_sign(nums) returns a result r and array_sign(nums2) returns a result r2, r = r2.
  Preconditions: Both nums and nums2 satisfy the problem constraints: 1 <= len(nums) <= 1000, 1 <= len(nums2) <= 1000, every nums[i] and nums2[i] lies in [-100,100]; moreover len(nums) = len(nums2), and for every i with 0 <= i < len(nums), nums[i] = 0 if and only if nums2[i] = 0, and nums[i] < 0 if and only if nums2[i] < 0. -/
theorem spec_10 (nums nums2 : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_len_min2 : 1 ≤ nums2.val.length) (h_len_max2 : nums2.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_bnd2 : ∀ x ∈ nums2.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_len : nums.val.length = nums2.val.length)
    (h_zero : ∀ (i : ℕ) (hi : i < nums.val.length) (hi2 : i < nums2.val.length),
      ((nums.val.get ⟨i, hi⟩).val = 0 ↔ (nums2.val.get ⟨i, hi2⟩).val = 0))
    (h_neg : ∀ (i : ℕ) (hi : i < nums.val.length) (hi2 : i < nums2.val.length),
      ((nums.val.get ⟨i, hi⟩).val < 0 ↔ (nums2.val.get ⟨i, hi2⟩).val < 0))
    (r r2 : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign nums2 = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_len_min2 : 1 ≤ nums2.val.length) (h_len_max2 : nums2.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_bnd2 : ∀ x ∈ nums2.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_len : nums.val.length = nums2.val.length)
    (h_zero : ∀ (i : ℕ) (hi : i < nums.val.length) (hi2 : i < nums2.val.length),
      ((nums.val.get ⟨i, hi⟩).val = 0 ↔ (nums2.val.get ⟨i, hi2⟩).val = 0))
    (h_neg : ∀ (i : ℕ) (hi : i < nums.val.length) (hi2 : i < nums2.val.length),
      ((nums.val.get ⟨i, hi⟩).val < 0 ↔ (nums2.val.get ⟨i, hi2⟩).val < 0))
    (r r2 : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign nums2 = ok r2), r.val = r2.val) := by
  sorry

/-- Let rev be the array of length len(nums) defined by rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). Whenever array_sign(nums) returns a result r and array_sign(rev) returns a result r_rev, r = r_rev.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_11 (nums rev : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_rev : rev.val = nums.val.reverse)
    (r r_rev : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign rev = ok r_rev) :
    r.val = r_rev.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_rev : rev.val = nums.val.reverse)
    (r r_rev : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign rev = ok r_rev), r.val = r_rev.val) := by
  sorry

/-- Let p be any bijection from {0,1,...,len(nums)-1} to itself, and let perm be the array defined by perm[i] = nums[p(i)] for every i with 0 <= i < len(nums). Whenever array_sign(nums) returns a result r and array_sign(perm) returns a result r_perm, r = r_perm.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_12 (nums perm : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (p : Fin nums.val.length → Fin nums.val.length) (hp : Function.Bijective p)
    (h_perm : perm.val = List.ofFn (fun i : Fin nums.val.length => nums.val.get (p i)))
    (r r_perm : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign perm = ok r_perm) :
    r.val = r_perm.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums perm : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (p : Fin nums.val.length → Fin nums.val.length) (hp : Function.Bijective p)
    (h_perm : perm.val = List.ofFn (fun i : Fin nums.val.length => nums.val.get (p i)))
    (r r_perm : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign perm = ok r_perm), r.val = r_perm.val) := by
  sorry

/-- Let neg be the array defined by neg[i] = -nums[i] for every i with 0 <= i < len(nums). Whenever array_sign(nums) returns a result r and array_sign(neg) returns a result r_neg: if r = 0 then r_neg = 0; if r != 0 and len(nums) is even then r_neg = r; and if r != 0 and len(nums) is odd then r_neg = -r.
  Preconditions: 1 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_13 (nums neg : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_neg : vals neg = (vals nums).map (fun x => -x))
    (r r_neg : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign neg = ok r_neg) :
    (r.val = 0 → r_neg.val = 0) ∧
      (r.val ≠ 0 → nums.val.length % 2 = 0 → r_neg.val = r.val) ∧
      (r.val ≠ 0 → nums.val.length % 2 = 1 → r_neg.val = -r.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums neg : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 1000)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (h_neg : vals neg = (vals nums).map (fun x => -x))
    (r r_neg : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign neg = ok r_neg), (r.val = 0 → r_neg.val = 0) ∧
      (r.val ≠ 0 → nums.val.length % 2 = 0 → r_neg.val = r.val) ∧
      (r.val ≠ 0 → nums.val.length % 2 = 1 → r_neg.val = -r.val)) := by
  sorry

/-- For every integer c with 1 <= c <= 100, let ext be the array with len(ext) = len(nums)+1, ext[i] = nums[i] for 0 <= i < len(nums), and ext[len(nums)] = c. Whenever array_sign(nums) returns a result r and array_sign(ext) returns a result r_ext, r = r_ext.
  Preconditions: 1 <= len(nums) <= 999, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_14 (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 100)
    (h_ext : ext.val = nums.val ++ [c])
    (r r_ext : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign ext = ok r_ext) :
    r.val = r_ext.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc_lo : 1 ≤ c.val) (hc_hi : c.val ≤ 100)
    (h_ext : ext.val = nums.val ++ [c])
    (r r_ext : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign ext = ok r_ext), r.val = r_ext.val) := by
  sorry

/-- For every integer c with -100 <= c < 0, let ext be the array with len(ext) = len(nums)+1, ext[i] = nums[i] for 0 <= i < len(nums), and ext[len(nums)] = c. Whenever array_sign(nums) returns a result r and array_sign(ext) returns a result r_ext: if r = 0 then r_ext = 0, and if r != 0 then r_ext = -r.
  Preconditions: 1 <= len(nums) <= 999, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_15 (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc_lo : -100 ≤ c.val) (hc_hi : c.val < 0)
    (h_ext : ext.val = nums.val ++ [c])
    (r r_ext : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign ext = ok r_ext) :
    (r.val = 0 → r_ext.val = 0) ∧ (r.val ≠ 0 → r_ext.val = -r.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc_lo : -100 ≤ c.val) (hc_hi : c.val < 0)
    (h_ext : ext.val = nums.val ++ [c])
    (r r_ext : Std.I64) (h : array_sign nums = ok r) (h2 : array_sign ext = ok r_ext), (r.val = 0 → r_ext.val = 0) ∧ (r.val ≠ 0 → r_ext.val = -r.val)) := by
  sorry

/-- Let ext be the array with len(ext) = len(nums)+1, ext[i] = nums[i] for 0 <= i < len(nums), and ext[len(nums)] = 0. Whenever array_sign(ext) returns a result r_ext, r_ext = 0.
  Preconditions: 1 <= len(nums) <= 999, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_16 (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc : c.val = 0)
    (h_ext : ext.val = nums.val ++ [c])
    (r_ext : Std.I64) (h : array_sign ext = ok r_ext) :
    r_ext.val = 0 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums ext : Slice Std.I64)
    (h_len_min : 1 ≤ nums.val.length) (h_len_max : nums.val.length ≤ 999)
    (h_bnd : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (c : Std.I64) (hc : c.val = 0)
    (h_ext : ext.val = nums.val ++ [c])
    (r_ext : Std.I64) (h : array_sign ext = ok r_ext), r_ext.val = 0) := by
  sorry

end AegisSpec.ArraySign
