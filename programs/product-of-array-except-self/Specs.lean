import Aegis.ProductExceptSelf.Code.Funs

/-!
# Specifications of `Aegis.ProductExceptSelf.product_except_self`

LeetCode problem `product-of-array-except-self`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ProductExceptSelf

def inI32 (x : ℤ) : Prop := -(2 : ℤ) ^ 31 ≤ x ∧ x ≤ (2 : ℤ) ^ 31 - 1

def listProd (l : List Std.I64) : ℤ := (l.map (fun x => x.val)).prod

def productExcept (l : List Std.I64) (i : ℕ) : ℤ := listProd (l.eraseIdx i)

def prefixProd (l : List Std.I64) (k : ℕ) : ℤ := listProd (l.take (k + 1))

def suffixProd (l : List Std.I64) (k : ℕ) : ℤ := listProd (l.drop k)

def negCountExcept (l : List Std.I64) (i : ℕ) : ℕ :=
  ((l.eraseIdx i).filter (fun x => decide (x.val < 0))).length

/-- The function returns a result r, and len(r) = len(nums), and for every i with 0 <= i < len(nums), r[i] = product_{j=0, j != i}^{len(nums)-1} nums[j].
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] (product of all elements except nums[i]) lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * nums[1] * ... * nums[k] and the suffix product nums[k] * nums[k+1] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∃ r, Aegis.ProductExceptSelf.product_except_self nums = ok r ∧
      r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]'hi').val = productExcept nums.val i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∃ r, Aegis.ProductExceptSelf.product_except_self nums = ok r ∧
      r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]'hi').val = productExcept nums.val i) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      r.val.length = nums.val.length) := by
  sorry

/-- The function returns a result r (it does not overflow, panic, or otherwise fail) for every input satisfying the preconditions.
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∃ r, Aegis.ProductExceptSelf.product_except_self nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∃ r, Aegis.ProductExceptSelf.product_except_self nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), -2^31 <= r[i] <= 2^31 - 1.
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        inI32 (r.val[i]'hi').val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        inI32 (r.val[i]'hi').val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), nums[i] * r[i] = product_{j=0}^{len(nums)-1} nums[j].
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]'hi).val * (r.val[i]'hi').val = listProd nums.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]'hi).val * (r.val[i]'hi').val = listProd nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = 0 if and only if there exists j with 0 <= j < len(nums), j != i, and nums[j] = 0.
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]'hi').val = 0 ↔
          ∃ (j : ℕ) (hj : j < nums.val.length), j ≠ i ∧ (nums.val[j]'hj).val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k)), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]'hi').val = 0 ↔
          ∃ (j : ℕ) (hj : j < nums.val.length), j ≠ i ∧ (nums.val[j]'hj).val = 0)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] > 0 if the number of indices j with 0 <= j < len(nums), j != i, and nums[j] < 0 is even, and r[i] < 0 if that number is odd.
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]; (v) for every i with 0 <= i < n, nums[i] != 0. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k))
    (h_nz : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ 0) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (Even (negCountExcept nums.val i) → 0 < (r.val[i]'hi').val) ∧
        (Odd (negCountExcept nums.val i) → (r.val[i]'hi').val < 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k))
    (h_nz : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ 0), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (Even (negCountExcept nums.val i) → 0 < (r.val[i]'hi').val) ∧
        (Odd (negCountExcept nums.val i) → (r.val[i]'hi').val < 0)) := by
  sorry

/-- Whenever the function returns a result r, the mathematical product product_{i=0}^{len(nums)-1} r[i] equals (product_{i=0}^{len(nums)-1} nums[i])^(len(nums)-1).
  Preconditions: Let n = len(nums). The following hold: (i) 2 <= n <= 100000; (ii) for every i with 0 <= i < n, -30 <= nums[i] <= 30; (iii) for every i with 0 <= i < n, the mathematical product P_i = product_{j=0, j != i}^{n-1} nums[j] lies in the signed 32-bit range [-2^31, 2^31 - 1]; (iv) for every k with 0 <= k < n, the prefix product nums[0] * ... * nums[k] and the suffix product nums[k] * ... * nums[n-1] lie in the signed 32-bit range [-2^31, 2^31 - 1]; (v) for every i with 0 <= i < n, nums[i] != 0. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k))
    (h_nz : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ 0) :
    ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      listProd r.val = listProd nums.val ^ (nums.val.length - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 2 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_elem : ∀ (i : ℕ) (hi : i < nums.val.length),
      -(30 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 30)
    (h_prod_i32 : ∀ (i : ℕ) (hi : i < nums.val.length), inI32 (productExcept nums.val i))
    (h_ps_i32 : ∀ (k : ℕ) (hk : k < nums.val.length),
      inI32 (prefixProd nums.val k) ∧ inI32 (suffixProd nums.val k))
    (h_nz : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ 0), ∀ r, Aegis.ProductExceptSelf.product_except_self nums = ok r →
      listProd r.val = listProd nums.val ^ (nums.val.length - 1)) := by
  sorry

end AegisSpec.ProductExceptSelf
