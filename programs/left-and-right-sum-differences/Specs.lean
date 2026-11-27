import Aegis.LeftRightDifference.Code.Funs

/-!
# Specifications of `Aegis.LeftRightDifference.left_right_difference`

LeetCode problem `left-and-right-sum-differences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.LeftRightDifference

def inVals (nums : Slice Std.I64) : List Int := nums.val.map fun x => x.val

def outVals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map fun x => x.val

def preSum (nums : Slice Std.I64) (i : Nat) : Int := (inVals nums).take i |>.sum

def sufSum (nums : Slice Std.I64) (i : Nat) : Int := (inVals nums).drop (i + 1) |>.sum

def totalSum (nums : Slice Std.I64) : Int := (inVals nums).sum

def outAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Int := (r.val.getD i 0#i64).val

/-- The function returns a result r such that len(r) = n and, for every i with 0 <= i < n, r[i] = |L_i - R_i|, where L_i = sum_{j=0}^{i-1} nums[j] (empty sum when i=0, equal to 0) and R_i = sum_{j=i+1}^{n-1} nums[j] (empty sum when i=n-1, equal to 0). Thus r is exactly the required answer array.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. All arithmetic below is over mathematical integers. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.LeftRightDifference.left_right_difference nums = ok r ∧
        r.val.length = nums.val.length ∧
          ∀ (i : Nat) (hi : i < nums.val.length),
            outAt r i = |preSum nums i - sufSum nums i| := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.LeftRightDifference.left_right_difference nums = ok r ∧
        r.val.length = nums.val.length ∧
          ∀ (i : Nat) (hi : i < nums.val.length),
            outAt r i = |preSum nums i - sufSum nums i|) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or encounter an i64 overflow in producing the answer.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.LeftRightDifference.left_right_difference nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.LeftRightDifference.left_right_difference nums = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, len(r) = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] >= 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length), 0 ≤ outAt r i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length), 0 ≤ outAt r i) := by
  sorry

/-- Whenever the function returns a result r, r[0] = sum_{j=1}^{n-1} nums[j], i.e. the sum of all elements strictly to the right of index 0 (this sum is 0 when n=1).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        outAt r 0 = sufSum nums 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        outAt r 0 = sufSum nums 0) := by
  sorry

/-- Whenever the function returns a result r, r[n-1] = sum_{j=0}^{n-2} nums[j], i.e. the sum of all elements strictly to the left of the last index (this sum is 0 when n=1).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        outAt r (nums.val.length - 1) = preSum nums (nums.val.length - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        outAt r (nums.val.length - 1) = preSum nums (nums.val.length - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] and T - nums[i] have the same parity. Equivalently, r[i] mod 2 = (T - nums[i]) mod 2 with residues 0 or 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let T = sum_{j=0}^{n-1} nums[j]. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i % 2 = (totalSum nums - (nums.val[i]).val) % 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i % 2 = (totalSum nums - (nums.val[i]).val) % 2) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 0 if and only if sum_{j=0}^{i-1} nums[j] = sum_{j=i+1}^{n-1} nums[j] (both empty sums being 0).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          (outAt r i = 0 ↔ preSum nums i = sufSum nums i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          (outAt r i = 0 ↔ preSum nums i = sufSum nums i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= T - nums[i]. Moreover, equality r[i] = T - nums[i] holds exactly when i = 0 or i = n-1 (for n=1 these are the same index), and for 0 < i < n-1 the inequality is strict: r[i] < T - nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let T = sum_{j=0}^{n-1} nums[j]. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        (∀ (i : Nat) (hi : i < nums.val.length),
            outAt r i ≤ totalSum nums - (nums.val[i]).val) ∧
          (∀ (i : Nat) (hi : i < nums.val.length),
              (outAt r i = totalSum nums - (nums.val[i]).val ↔
                (i = 0 ∨ i = nums.val.length - 1))) ∧

            (∀ (i : Nat) (hi : i < nums.val.length), 0 < i → i < nums.val.length - 1 →
              outAt r i < totalSum nums - (nums.val[i]).val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        (∀ (i : Nat) (hi : i < nums.val.length),
            outAt r i ≤ totalSum nums - (nums.val[i]).val) ∧
          (∀ (i : Nat) (hi : i < nums.val.length),
              (outAt r i = totalSum nums - (nums.val[i]).val ↔
                (i = 0 ∨ i = nums.val.length - 1))) ∧

            (∀ (i : Nat) (hi : i < nums.val.length), 0 < i → i < nums.val.length - 1 →
              outAt r i < totalSum nums - (nums.val[i]).val)) := by
  sorry

/-- Let b be the array of length n defined by b[i] = nums[n-1-i] for 0 <= i < n. If r is a result returned for nums and r' is a result returned for b, then len(r') = n and for every i with 0 <= i < n, r'[i] = r[n-1-i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_10 (nums b : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_b : b.val = nums.val.reverse) :
    ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        Aegis.LeftRightDifference.left_right_difference b = ok r' →
          r'.val.length = nums.val.length ∧
            ∀ (i : Nat) (hi : i < nums.val.length),
              outAt r' i = outAt r (nums.val.length - 1 - i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums b : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_b : b.val = nums.val.reverse), ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        Aegis.LeftRightDifference.left_right_difference b = ok r' →
          r'.val.length = nums.val.length ∧
            ∀ (i : Nat) (hi : i < nums.val.length),
              outAt r' i = outAt r (nums.val.length - 1 - i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= max(L_i, R_i), where L_i = sum_{j=0}^{i-1} nums[j] and R_i = sum_{j=i+1}^{n-1} nums[j] (empty sums 0).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i ≤ max (preSum nums i) (sufSum nums i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i ≤ max (preSum nums i) (sufSum nums i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = |(2*i - (n - 1)) * c| = |2*i - n + 1| * c.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and there is an integer c with 1 <= c <= 100000 such that nums[i] = c for every i with 0 <= i < n. -/
theorem spec_12 (nums : Slice Std.I64) (c : Int)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_c_lo : 1 ≤ c) (h_c_hi : c ≤ 100000)
    (h_const : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = c) :
    ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i = |((2 : Int) * (i : Int) - ((nums.val.length : Int) - 1)) * c| := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (c : Int)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_c_lo : 1 ≤ c) (h_c_hi : c ≤ 100000)
    (h_const : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = c), ∀ (r : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          outAt r i = |((2 : Int) * (i : Int) - ((nums.val.length : Int) - 1)) * c|) := by
  sorry

/-- Whenever the function returns r for nums and r' for scaled, for every i with 0 <= i < n, r'[i] = c * r[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let c be a positive integer such that for every i with 0 <= i < n, 1 <= c * nums[i] <= 100000, and let scaled be the array of length n with scaled[i] = c * nums[i]. -/
theorem spec_13 (nums scaled : Slice Std.I64) (c : Int)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_c_pos : 0 < c)
    (h_scaled_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ 100000)
    (h_scaled : inVals scaled = (inVals nums).map fun v => c * v) :
    ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        Aegis.LeftRightDifference.left_right_difference scaled = ok r' →
          ∀ (i : Nat) (hi : i < nums.val.length), outAt r' i = c * outAt r i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums scaled : Slice Std.I64) (c : Int)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 1000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (h_c_pos : 0 < c)
    (h_scaled_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ 100000)
    (h_scaled : inVals scaled = (inVals nums).map fun v => c * v), ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.LeftRightDifference.left_right_difference nums = ok r →
        Aegis.LeftRightDifference.left_right_difference scaled = ok r' →
          ∀ (i : Nat) (hi : i < nums.val.length), outAt r' i = c * outAt r i) := by
  sorry

end AegisSpec.LeftRightDifference
