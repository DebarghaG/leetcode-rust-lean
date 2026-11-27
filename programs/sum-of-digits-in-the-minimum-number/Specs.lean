import Aegis.SumOfDigits.Code.Funs

/-!
# Specifications of `Aegis.SumOfDigits.sum_of_digits`

LeetCode problem `sum-of-digits-in-the-minimum-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.SumOfDigits

  namespace AegisSpec.SumOfDigits

  def digitSum (n : Nat) : Nat :=
    if h : n < 10 then n else n % 10 + digitSum (n / 10)
  termination_by n
  decreasing_by omega

  def digitSumInt (z : Int) : Int := (digitSum z.natAbs : Int)

  def listMin (l : List Int) : Int := (l.min?).getD 0

  def sliceMin (nums : Slice Std.I64) : Int := listMin (nums.val.map (fun x => x.val))

  /-- Let m = min{nums[i] | 0 <= i < len(nums)} and let ds(m) be the sum of the decimal digits of m. The function returns a result r such that r = 0 if ds(m) is odd and r = 1 if ds(m) is even; equivalently, r = 1 - (ds(m) mod 2).
    Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r : Std.I64, sum_of_digits nums = ok r ∧
        r.val = 1 - (digitSumInt (sliceMin nums) % 2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r : Std.I64, sum_of_digits nums = ok r ∧
          r.val = 1 - (digitSumInt (sliceMin nums) % 2)) := by
    sorry

  /-- Whenever the function returns a result r, r is either 0 or 1.
    Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∀ r : Std.I64, sum_of_digits nums = ok r → r.val = 0 ∨ r.val = 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∀ r : Std.I64, sum_of_digits nums = ok r → r.val = 0 ∨ r.val = 1) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r : Std.I64, sum_of_digits nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r : Std.I64, sum_of_digits nums = ok r) := by
    sorry

  /-- Let m = min{nums[i] | 0 <= i < len(nums)} and let ds(m) be the sum of the decimal digits of m. Whenever the function returns a result r, r = 0 if and only if ds(m) is odd.
    Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∀ r : Std.I64, sum_of_digits nums = ok r →
        (r.val = 0 ↔ digitSumInt (sliceMin nums) % 2 = 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∀ r : Std.I64, sum_of_digits nums = ok r →
          (r.val = 0 ↔ digitSumInt (sliceMin nums) % 2 = 1)) := by
    sorry

  /-- Whenever the function returns r on input nums and returns r' on input nums', we have r = r'.
    Preconditions: nums and nums' are two slices, each satisfying len between 1 and 100 inclusive and every entry between 1 and 100 inclusive. Let m = min{nums[i] | 0 <= i < len(nums)} and m' = min{nums'[i] | 0 <= i < len(nums')}. Suppose the sum of the decimal digits of m and the sum of the decimal digits of m' have the same parity, i.e., ds(m) mod 2 = ds(m') mod 2. -/
  theorem spec_5 (nums nums' : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hlen1' : 1 ≤ nums'.val.length) (hlen2' : nums'.val.length ≤ 100)
      (hrange' : ∀ (i : Nat) (h : i < nums'.val.length),
        1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 100)
      (hparity : digitSumInt (sliceMin nums) % 2 = digitSumInt (sliceMin nums') % 2) :
      ∀ (r r' : Std.I64), sum_of_digits nums = ok r → sum_of_digits nums' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hlen1' : 1 ≤ nums'.val.length) (hlen2' : nums'.val.length ≤ 100)
        (hrange' : ∀ (i : Nat) (h : i < nums'.val.length),
          1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 100)
        (hparity : digitSumInt (sliceMin nums) % 2 = digitSumInt (sliceMin nums') % 2), ∀ (r r' : Std.I64), sum_of_digits nums = ok r → sum_of_digits nums' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let ds(nums[0]) be the sum of the decimal digits of nums[0]. Whenever the function returns a result r, r = 0 if ds(nums[0]) is odd, and r = 1 if ds(nums[0]) is even.
    Preconditions: len(nums) = 1, and nums[0] is an integer with 1 <= nums[0] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64) (hlen : nums.val.length = 1)
      (hlo : 1 ≤ (nums.val[0]'(by omega)).val)
      (hhi : (nums.val[0]'(by omega)).val ≤ 100) :
      ∀ r : Std.I64, sum_of_digits nums = ok r →
        ((digitSumInt (nums.val[0]'(by omega)).val % 2 = 1 → r.val = 0) ∧
         (digitSumInt (nums.val[0]'(by omega)).val % 2 = 0 → r.val = 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 1)
        (hlo : 1 ≤ (nums.val[0]'(by omega)).val)
        (hhi : (nums.val[0]'(by omega)).val ≤ 100), ∀ r : Std.I64, sum_of_digits nums = ok r →
          ((digitSumInt (nums.val[0]'(by omega)).val % 2 = 1 → r.val = 0) ∧
           (digitSumInt (nums.val[0]'(by omega)).val % 2 = 0 → r.val = 1))) := by
    sorry

  /-- Let ds(n) be the sum of the decimal digits of n. Whenever the function returns a result r, r = 0 if ds(n) is odd, and r = 1 if ds(n) is even.
    Preconditions: len(nums) is between 1 and 100 inclusive, and there exists an integer n with 1 <= n <= 100 such that nums[i] = n for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (n : Int)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hnlo : 1 ≤ n) (hnhi : n ≤ 100)
      (hconst : ∀ (i : Nat) (h : i < nums.val.length), (nums.val[i]'h).val = n) :
      ∀ r : Std.I64, sum_of_digits nums = ok r →
        ((digitSumInt n % 2 = 1 → r.val = 0) ∧
         (digitSumInt n % 2 = 0 → r.val = 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Int)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hnlo : 1 ≤ n) (hnhi : n ≤ 100)
        (hconst : ∀ (i : Nat) (h : i < nums.val.length), (nums.val[i]'h).val = n), ∀ r : Std.I64, sum_of_digits nums = ok r →
          ((digitSumInt n % 2 = 1 → r.val = 0) ∧
           (digitSumInt n % 2 = 0 → r.val = 1))) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: len(nums) is between 1 and 100 inclusive, every nums[i] is between 1 and 100 inclusive, and min{nums[i] | 0 <= i < len(nums)} = 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hmin : sliceMin nums = 100) :
      ∀ r : Std.I64, sum_of_digits nums = ok r → r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hmin : sliceMin nums = 100), ∀ r : Std.I64, sum_of_digits nums = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if m is even and r = 0 if m is odd.
    Preconditions: len(nums) is between 1 and 100 inclusive, every nums[i] is between 1 and 100 inclusive, and m = min{nums[i] | 0 <= i < len(nums)} satisfies 1 <= m <= 9. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hmin : 1 ≤ sliceMin nums ∧ sliceMin nums ≤ 9) :
      ∀ r : Std.I64, sum_of_digits nums = ok r →
        ((sliceMin nums % 2 = 0 → r.val = 1) ∧
         (sliceMin nums % 2 = 1 → r.val = 0)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hmin : 1 ≤ sliceMin nums ∧ sliceMin nums ≤ 9), ∀ r : Std.I64, sum_of_digits nums = ok r →
          ((sliceMin nums % 2 = 0 → r.val = 1) ∧
           (sliceMin nums % 2 = 1 → r.val = 0))) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index j with 0 <= j < len(nums) such that nums[j] <= nums[i] for every i with 0 <= i < len(nums), and, letting ds(nums[j]) be the sum of the decimal digits of nums[j], r = 0 if ds(nums[j]) is odd and r = 1 if ds(nums[j]) is even.
    Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∀ r : Std.I64, sum_of_digits nums = ok r →
        ∃ (j : Nat) (hj : j < nums.val.length),
          (∀ (i : Nat) (hi : i < nums.val.length), (nums.val[j]'hj).val ≤ (nums.val[i]'hi).val) ∧
          ((digitSumInt (nums.val[j]'hj).val % 2 = 1 → r.val = 0) ∧
           (digitSumInt (nums.val[j]'hj).val % 2 = 0 → r.val = 1)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∀ r : Std.I64, sum_of_digits nums = ok r →
          ∃ (j : Nat) (hj : j < nums.val.length),
            (∀ (i : Nat) (hi : i < nums.val.length), (nums.val[j]'hj).val ≤ (nums.val[i]'hi).val) ∧
            ((digitSumInt (nums.val[j]'hj).val % 2 = 1 → r.val = 0) ∧
             (digitSumInt (nums.val[j]'hj).val % 2 = 0 → r.val = 1))) := by
    sorry

  end AegisSpec.SumOfDigits
