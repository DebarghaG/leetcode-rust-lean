import Aegis.MaxRotateFunction.Code.Funs

/-!
# Specifications of `Aegis.MaxRotateFunction.max_rotate_function`

LeetCode problem `rotate-function`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxRotateFunction

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (vals nums).getD i 0

def IsBounded (nums : Slice Std.I64) : Prop :=
  ∀ i, i < nums.length → -100 ≤ elem nums i ∧ elem nums i ≤ 100

def rotIndex (n i k : ℕ) : ℕ := (i + n - k) % n

def F (nums : Slice Std.I64) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range nums.length, (i : ℤ) * elem nums (rotIndex nums.length i k)

def total (nums : Slice Std.I64) : ℤ := ∑ i ∈ Finset.range nums.length, elem nums i

def T (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) - 1) / 2

def maxF (nums : Slice Std.I64) (h : 0 < nums.length) : ℤ :=
  ((Finset.range nums.length).image (fun k => F nums k)).max'
    (Finset.Nonempty.image ⟨0, Finset.mem_range.mpr h⟩ _)

theorem vals_length (nums : Slice Std.I64) : (vals nums).length = nums.length := by
  simp [vals, Aeneas.Std.Slice.length]

theorem elem_eq_getElem (nums : Slice Std.I64) (i : ℕ) (hi : i < nums.length) :
    elem nums i = (vals nums).get ⟨i, by simpa [vals_length] using hi⟩ := by
  unfold elem
  exact List.getD_eq_getElem (vals nums) 0 (by simpa [vals_length] using hi)

theorem rotIndex_lt (n i k : ℕ) (hn : 0 < n) : rotIndex n i k < n :=
  Nat.mod_lt _ hn

theorem rotIndex_modEq (n i k : ℕ) (hn : 0 < n) (hi : i < n) (hk : k < n) :
    ∃ t : ℤ, (i : ℤ) - (k : ℤ) = (rotIndex n i k : ℤ) + t * (n : ℤ) := by
  unfold rotIndex
  rcases lt_or_ge i k with hlt | hle
  · refine ⟨-1, ?_⟩
    have hkn : k ≤ n := by omega
    have h1 : i + n - k = i + (n - k) := by omega
    have h2 : i + (n - k) < n := by omega
    rw [h1, Nat.mod_eq_of_lt h2]
    have hcast : ((i + (n - k) : ℕ) : ℤ) = (i : ℤ) + (n : ℤ) - (k : ℤ) := by
      push_cast [hkn]
      ring
    rw [hcast]
    ring
  · refine ⟨0, ?_⟩
    have h1 : i + n - k = (i - k) + n := by omega
    have hi' : i - k < n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi']
    have hcast : ((i - k : ℕ) : ℤ) = (i : ℤ) - (k : ℤ) := by omega
    rw [hcast]
    ring

theorem F_zero (nums : Slice Std.I64) :
    F nums 0 = ∑ i ∈ Finset.range nums.length, (i : ℤ) * elem nums i := by
  unfold F
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < nums.length := Finset.mem_range.mp hi
  rw [show rotIndex nums.length i 0 = i from by
    unfold rotIndex
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hi']]

/-- Let F(k) = sum_{i=0}^{n-1} i * nums[(i-k) mod n] for 0 <= k < n, where (i-k) mod n denotes the unique integer j with 0 <= j < n and j ≡ i-k (mod n). Whenever the function returns a result r, r = max_{0 <= k < n} F(k).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r) :
    r.val = maxF nums (by omega) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r), r.val = maxF nums (by omega)) := by
  sorry

/-- The function returns a result (some i64 value) for every input satisfying the preconditions; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) :
    ∃ r : Std.I64, Aegis.MaxRotateFunction.max_rotate_function nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums), ∃ r : Std.I64, Aegis.MaxRotateFunction.max_rotate_function nums = ok r) := by
  sorry

/-- Let F(k) = sum_{i=0}^{n-1} i * nums[(i-k) mod n] for 0 <= k < n, with modulo taken into [0,n-1]. Whenever the function returns a result r, there exists an integer k with 0 <= k < n such that r = F(k).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r) :
    ∃ k, k < nums.length ∧ r.val = F nums k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r), ∃ k, k < nums.length ∧ r.val = F nums k) := by
  sorry

/-- Let F(k) = sum_{i=0}^{n-1} i * nums[(i-k) mod n] for 0 <= k < n, with modulo taken into [0,n-1]. Whenever the function returns a result r, for every integer k with 0 <= k < n, F(k) <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r) :
    ∀ k, k < nums.length → F nums k ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r), ∀ k, k < nums.length → F nums k ≤ r.val) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i] and F(k) = sum_{i=0}^{n-1} i * nums[(i-k) mod n] for 0 <= k < n, with modulo taken into [0,n-1]. Whenever the function returns a result r, 2*r >= (n-1)*S.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r) :
    ((nums.length : ℤ) - 1) * total nums ≤ 2 * r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r), ((nums.length : ℤ) - 1) * total nums ≤ 2 * r.val) := by
  sorry

/-- Let r be the result of the function on nums and r' be the result of the function on nums'. Then r' = r + c * n*(n-1)/2.
  Preconditions: Let nums and nums' be slices of the same length n with 1 <= n <= 100000, and both satisfy the element bounds -100 <= nums[i] <= 100 and -100 <= nums'[i] <= 100 for all 0 <= i < n. Assume there is an integer c such that nums'[i] = nums[i] + c for every i with 0 <= i < n. -/
theorem spec_6 (nums nums' : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hc : ∀ i, i < nums.length → elem nums' i = elem nums i + c)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r') :
    r'.val = r.val + c * T nums.length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hc : ∀ i, i < nums.length → elem nums' i = elem nums i + c)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r'), r'.val = r.val + c * T nums.length) := by
  sorry

/-- Let r be the result of the function on nums and r' be the result of the function on nums'. Then r' = c * r.
  Preconditions: Let nums and nums' be slices of the same length n with 1 <= n <= 100000, and both satisfy the element bounds -100 <= nums[i] <= 100 and -100 <= nums'[i] <= 100 for all 0 <= i < n. Assume there is an integer c with c >= 0 such that nums'[i] = c * nums[i] for every i with 0 <= i < n. -/
theorem spec_7 (nums nums' : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hc0 : 0 ≤ c)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hc : ∀ i, i < nums.length → elem nums' i = c * elem nums i)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hc0 : 0 ≤ c)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hc : ∀ i, i < nums.length → elem nums' i = c * elem nums i)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r'), r'.val = c * r.val) := by
  sorry

/-- The result of the function on nums' equals the result of the function on nums.
  Preconditions: Let nums and nums' be slices of the same length n with 1 <= n <= 100000, and both satisfy the element bounds -100 <= nums[i] <= 100 and -100 <= nums'[i] <= 100 for all 0 <= i < n. Assume nums' is a cyclic rotation of nums: there exists an integer j with 0 <= j < n such that nums'[i] = nums[(i+j) mod n] for every i with 0 <= i < n, where modulo is taken into [0,n-1]. -/
theorem spec_8 (nums nums' : Slice Std.I64) (j : ℕ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hj : j < nums.length)
    (hrot : ∀ i, i < nums.length → elem nums' i = elem nums (rotIndex nums.length i j))
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (j : ℕ) (r r' : Std.I64)
    (hlen : nums'.length = nums.length)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums) (hb' : IsBounded nums')
    (hj : j < nums.length)
    (hrot : ∀ i, i < nums.length → elem nums' i = elem nums (rotIndex nums.length i j))
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r)
    (hr' : Aegis.MaxRotateFunction.max_rotate_function nums' = ok r'), r'.val = r.val) := by
  sorry

/-- Let T = n*(n-1)/2. Whenever the function returns a result r, -100*T <= r <= 100*T.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, -100 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r) :
    -100 * T nums.length ≤ r.val ∧ r.val ≤ 100 * T nums.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ nums.length) (hn2 : nums.length ≤ 100000)
    (hb : IsBounded nums)
    (hr : Aegis.MaxRotateFunction.max_rotate_function nums = ok r), -100 * T nums.length ≤ r.val ∧ r.val ≤ 100 * T nums.length) := by
  sorry

end AegisSpec.MaxRotateFunction
