import Aegis.FindPeakElement.Code.Funs

/-!
# Specifications of `Aegis.FindPeakElement.find_peak_element`

LeetCode problem `find-peak-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindPeakElement

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def sz (nums : Slice Std.I64) : Nat := (vals nums).length

  def elem (l : List Int) (i : Int) : Int := (l[i.toNat]?).getD 0

  def i64Max : Int := 2147483647

  def i64Min : Int := -2147483648

  def InI64Range (l : List Int) : Prop :=
    ∀ i : Int, 0 ≤ i → i < (l.length : Int) → i64Min ≤ elem l i ∧ elem l i ≤ i64Max

  def AdjacentNe (l : List Int) : Prop :=
    ∀ i : Int, 0 ≤ i → i + 1 < (l.length : Int) → elem l i ≠ elem l (i + 1)

  def StrictlyIncreasing (l : List Int) : Prop :=
    ∀ i : Int, 0 ≤ i → i + 1 < (l.length : Int) → elem l i < elem l (i + 1)

  def IsPeakIndex (l : List Int) (p : Int) : Prop :=
    0 ≤ p ∧ p < (l.length : Int) ∧
      (p = 0 ∨ elem l (p - 1) < elem l p) ∧
      (p = (l.length : Int) - 1 ∨ elem l (p + 1) < elem l p)

  def loopIterations (len : Nat) : Nat :=
    if len = 0 then 0
    else 1 + max (loopIterations (len / 2)) (loopIterations ((len + 1) / 2 - 1))
  termination_by len
  decreasing_by
    · exact Nat.div_lt_self (by omega) (by omega)
    · have h1 : 0 < len + 1 := by omega
      have h2 : (len + 1) / 2 < len + 1 := Nat.div_lt_self h1 (by omega)
      omega

  def comparisonCount (n : Nat) : Nat := loopIterations (n - 1) + 1

  def accessCount (n : Nat) : Nat := 2 * loopIterations (n - 1)

  /-- The function returns a result r such that 0 <= r < n and (r = 0 or nums[r] > nums[r-1]) and (r = n-1 or nums[r] > nums[r+1]). Thus r is the 0-based index of a peak element, where a missing neighbor on the left or right is treated as -∞ and automatically satisfies the corresponding comparison.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; and for every i with 0 <= i < n-1, nums[i] != nums[i+1]. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums)) :
      ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧
        IsPeakIndex (vals nums) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums)), ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧
          IsPeakIndex (vals nums) r.val) := by
    sorry

  /-- For every input satisfying the preconditions, there exists an integer r such that the function returns `Result.ok r` (i.e., it never returns `Result.fail`). In particular, it does not fail due to indexing, arithmetic, or other runtime errors.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; and for every i with 0 <= i < n-1, nums[i] != nums[i+1]. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums)) :
      ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums)), ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; and n = 1. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_one : sz nums = 1) :
      ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_one : sz nums = 1), ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 0) := by
    sorry

  /-- If nums[0] > nums[1], the function returns r = 0; otherwise, by nums[0] != nums[1], nums[0] < nums[1] and the function returns r = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; and n = 2. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_two : sz nums = 2) :
      ((elem (vals nums) 1 < elem (vals nums) 0 →
          ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 0) ∧
        (¬ (elem (vals nums) 1 < elem (vals nums) 0) →
          ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_two : sz nums = 2), ((elem (vals nums) 1 < elem (vals nums) 0 →
            ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 0) ∧
          (¬ (elem (vals nums) 1 < elem (vals nums) 0) →
            ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = 1))) := by
    sorry

  /-- The function returns r = n-1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; and for every i with 0 <= i < n-1, nums[i] < nums[i+1]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_incr : StrictlyIncreasing (vals nums)) :
      ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧
        r.val = (sz nums : Int) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_incr : StrictlyIncreasing (vals nums)), ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧
          r.val = (sz nums : Int) - 1) := by
    sorry

  /-- The function returns r = p.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; and there is exactly one index p with 0 <= p < n such that (p = 0 or nums[p] > nums[p-1]) and (p = n-1 or nums[p] > nums[p+1]). -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (p : Int) (h_p : IsPeakIndex (vals nums) p)
      (h_unique : ∀ q : Int, IsPeakIndex (vals nums) q → q = p) :
      ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = p := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (p : Int) (h_p : IsPeakIndex (vals nums) p)
        (h_unique : ∀ q : Int, IsPeakIndex (vals nums) q → q = p), ∃ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r ∧ r.val = p) := by
    sorry

  /-- Whenever the function returns a result r, r != 0.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; n >= 2; and nums[0] < nums[1]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_ge : 2 ≤ sz nums) (h_first : elem (vals nums) 0 < elem (vals nums) 1) :
      ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r → r.val ≠ 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_ge : 2 ≤ sz nums) (h_first : elem (vals nums) 0 < elem (vals nums) 1), ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r → r.val ≠ 0) := by
    sorry

  /-- Whenever the function returns a result r, r != n-1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; n >= 2; and nums[n-1] < nums[n-2]. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_ge : 2 ≤ sz nums)
      (h_last : elem (vals nums) ((sz nums : Int) - 1) < elem (vals nums) ((sz nums : Int) - 2)) :
      ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
        r.val ≠ (sz nums : Int) - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_ge : 2 ≤ sz nums)
        (h_last : elem (vals nums) ((sz nums : Int) - 1) < elem (vals nums) ((sz nums : Int) - 2)), ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
          r.val ≠ (sz nums : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n-2.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]; n >= 3; nums[0] < nums[1]; and nums[n-1] < nums[n-2]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_ge : 3 ≤ sz nums) (h_first : elem (vals nums) 0 < elem (vals nums) 1)
      (h_last : elem (vals nums) ((sz nums : Int) - 1) < elem (vals nums) ((sz nums : Int) - 2)) :
      ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
        1 ≤ r.val ∧ r.val ≤ (sz nums : Int) - 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_ge : 3 ≤ sz nums) (h_first : elem (vals nums) 0 < elem (vals nums) 1)
        (h_last : elem (vals nums) ((sz nums : Int) - 1) < elem (vals nums) ((sz nums : Int) - 2)), ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
          1 ≤ r.val ∧ r.val ≤ (sz nums : Int) - 2) := by
    sorry

  /-- Whenever the function returns a result r on nums, r is a peak index of nums': 0 <= r < n, (r = 0 or nums'[r] > nums'[r-1]), and (r = n-1 or nums'[r] > nums'[r+1]).
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; and for every i with 0 <= i < n-1, nums[i] != nums[i+1]. Let nums' be any slice of i64 of length n such that for every i with 0 <= i < n, -2^31 <= nums'[i] <= 2^31 - 1, for every i with 0 <= i < n-1, nums'[i] != nums'[i+1], and for every i with 0 <= i < n-1, nums[i] < nums[i+1] iff nums'[i] < nums'[i+1]. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_len' : (vals nums').length = (vals nums).length)
      (h_range' : InI64Range (vals nums')) (h_adj' : AdjacentNe (vals nums'))
      (h_pattern : ∀ i : Int, 0 ≤ i → i + 1 < (vals nums).length →
        (elem (vals nums) i < elem (vals nums) (i + 1) ↔
          elem (vals nums') i < elem (vals nums') (i + 1))) :
      ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
        IsPeakIndex (vals nums') r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_len' : (vals nums').length = (vals nums).length)
        (h_range' : InI64Range (vals nums')) (h_adj' : AdjacentNe (vals nums'))
        (h_pattern : ∀ i : Int, 0 ≤ i → i + 1 < (vals nums).length →
          (elem (vals nums) i < elem (vals nums) (i + 1) ↔
            elem (vals nums') i < elem (vals nums') (i + 1))), ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
          IsPeakIndex (vals nums') r.val) := by
    sorry

  /-- Whenever the function returns a result r on nums, the index j = n-1-r is a peak index of nums': 0 <= j < n, (j = 0 or nums'[j] > nums'[j-1]), and (j = n-1 or nums'[j] > nums'[j+1]).
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 1000; for every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1; for every i with 0 <= i < n-1, nums[i] != nums[i+1]. Let nums' be the slice of length n defined by nums'[i] = nums[n-1-i] for every i with 0 <= i < n. -/
  theorem spec_11 (nums nums' : Slice Std.I64)
      (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
      (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
      (h_len' : (vals nums').length = (vals nums).length)
      (h_rev : ∀ i : Int, 0 ≤ i → i < (vals nums).length →
        elem (vals nums') i = elem (vals nums) ((vals nums).length - 1 - i)) :
      ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
        IsPeakIndex (vals nums') ((vals nums).length - 1 - r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len : 1 ≤ sz nums) (h_len_ub : sz nums ≤ 1000)
        (h_range : InI64Range (vals nums)) (h_adj : AdjacentNe (vals nums))
        (h_len' : (vals nums').length = (vals nums).length)
        (h_rev : ∀ i : Int, 0 ≤ i → i < (vals nums).length →
          elem (vals nums') i = elem (vals nums) ((vals nums).length - 1 - i)), ∀ r : Std.I64, Aegis.FindPeakElement.find_peak_element nums = ok r →
          IsPeakIndex (vals nums') ((vals nums).length - 1 - r.val)) := by
    sorry

  end AegisSpec.FindPeakElement
