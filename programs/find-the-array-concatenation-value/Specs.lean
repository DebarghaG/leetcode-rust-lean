import Aegis.FindTheArrayConcVal.Code.Funs

/-!
# Specifications of `Aegis.FindTheArrayConcVal.find_the_array_conc_val`

LeetCode problem `find-the-array-concatenation-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTheArrayConcVal

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    ((nums.val[i]?).map (fun x => x.val)).getD 0

  def digitCount (x : Int) : Nat :=
    if 1 ≤ x then Nat.log 10 x.toNat + 1 else 0

  def digitPow (x : Int) : Int :=
    10 ^ digitCount x

  def pairVal (nums : Slice Std.I64) (k : Nat) : Int :=
    elem nums k * digitPow (elem nums (nums.val.length - 1 - k)) +
      elem nums (nums.val.length - 1 - k)

  def midVal (nums : Slice Std.I64) : Int :=
    if nums.val.length % 2 = 1 then elem nums (nums.val.length / 2) else 0

  def pairSum (nums : Slice Std.I64) : Int :=
    (Finset.range (nums.val.length / 2)).sum (fun k => pairVal nums k)

  def tailSum (nums : Slice Std.I64) : Int :=
    (Finset.range (nums.val.length / 2)).sum (fun k => elem nums (nums.val.length - 1 - k))

  def total (nums : Slice Std.I64) : Int :=
    (Finset.range nums.val.length).sum (fun i => elem nums i)

  /-- The function returns a result r, and r = (sum_{k=0}^{floor(len(nums)/2)-1} (nums[k] * 10^{d(nums[len(nums)-1-k])} + nums[len(nums)-1-k])) + (if len(nums) is odd then nums[(len(nums)-1)/2] else 0), where d(x) is the number of decimal digits of x, i.e., the unique positive integer d such that 10^{d-1} <= x < 10^d.
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          r.val = pairSum nums + midVal nums := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            r.val = pairSum nums + midVal nums) := by
    sorry

  /-- For every nums satisfying the preconditions, the function returns a result r (it does not fail from integer overflow, out-of-bounds indexing, or a panic).
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r) := by
    sorry

  /-- The function returns a result r and r >= sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          total nums ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            total nums ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 100000 * sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          r.val ≤ 100000 * total nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            r.val ≤ 100000 * total nums) := by
    sorry

  /-- Let r be the result of the function on nums and r' the result on nums'. Then r <= r'.
    Preconditions: Let nums and nums' be two arrays such that 1 <= len(nums) = len(nums') <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= nums'[i] <= 10000. -/
  theorem spec_5 (nums nums' : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hlen : nums.val.length = nums'.val.length)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmono : ∀ i, i < nums.val.length → elem nums i ≤ elem nums' i)
      (hmax : ∀ i, i < nums.val.length → elem nums' i ≤ 10000) :
      ∀ r r' : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r →
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums' = ok r' →
            r.val ≤ r'.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hlen : nums.val.length = nums'.val.length)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmono : ∀ i, i < nums.val.length → elem nums i ≤ elem nums' i)
        (hmax : ∀ i, i < nums.val.length → elem nums' i ≤ 10000), ∀ r r' : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r →
            Aegis.FindTheArrayConcVal.find_the_array_conc_val nums' = ok r' →
              r.val ≤ r'.val) := by
    sorry

  /-- The function returns a result r and r >= nums[0] * 10^{d(nums[len(nums)-1])} + nums[len(nums)-1], where d(x) is the number of decimal digits of x.
    Preconditions: len(nums) >= 2 and 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          elem nums 0 * digitPow (elem nums (nums.val.length - 1)) +
              elem nums (nums.val.length - 1) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            elem nums 0 * digitPow (elem nums (nums.val.length - 1)) +
                elem nums (nums.val.length - 1) ≤ r.val) := by
    sorry

  /-- Let Q = (sum_{k=0}^{floor(len(nums)/2)-1} nums[len(nums)-1-k]) + (if len(nums) is odd then nums[(len(nums)-1)/2] else 0). The function returns a result r and r mod 10 = Q mod 10.
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          r.val % 10 = (tailSum nums + midVal nums) % 10 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            r.val % 10 = (tailSum nums + midVal nums) % 10) := by
    sorry

  /-- The function returns a result r and r <= 500005000000.
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
      (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
      (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
          r.val ≤ 500005000000 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 1 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 1000)
        (hmin : ∀ i, i < nums.val.length → 1 ≤ elem nums i)
        (hmax : ∀ i, i < nums.val.length → elem nums i ≤ 10000), ∃ r : Std.I64,
          Aegis.FindTheArrayConcVal.find_the_array_conc_val nums = ok r ∧
            r.val ≤ 500005000000) := by
    sorry

  end AegisSpec.FindTheArrayConcVal
