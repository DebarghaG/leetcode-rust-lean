import Aegis.CheckPossibility.Code.Funs

/-!
# Specifications of `Aegis.CheckPossibility.check_possibility`

LeetCode problem `non-decreasing-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckPossibility

  def NonDecreasing (l : List Std.I64) : Prop :=
    ∀ k : ℕ, k + 1 < l.length → (l[k]!).val ≤ (l[k + 1]!).val

  def DiffersAtMostOne (a b : List Std.I64) : Prop :=
    ∀ j₁ j₂ : ℕ, j₁ < a.length → j₂ < a.length →
      b[j₁]! ≠ a[j₁]! → b[j₂]! ≠ a[j₂]! → j₁ = j₂

  /-- The function returns a result r and r = true if and only if there exists a sequence b of length len(nums) of i64 values such that (i) b differs from nums at no more than one index, meaning there is at most one j with 0 <= j < len(nums) and b[j] != nums[j], and (ii) b is non-decreasing, meaning for every k with 0 <= k < len(nums)-1, b[k] <= b[k+1].
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
      ∃ r : Bool,
        Aegis.CheckPossibility.check_possibility nums = ok r ∧
          (r = true ↔
            ∃ b : List Std.I64,
              b.length = nums.val.length ∧
                DiffersAtMostOne nums.val b ∧
                  NonDecreasing b) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∃ r : Bool,
          Aegis.CheckPossibility.check_possibility nums = ok r ∧
            (r = true ↔
              ∃ b : List Std.I64,
                b.length = nums.val.length ∧
                  DiffersAtMostOne nums.val b ∧
                    NonDecreasing b)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
      ∃ r : Bool, Aegis.CheckPossibility.check_possibility nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∃ r : Bool, Aegis.CheckPossibility.check_possibility nums = ok r) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: 1 <= len(nums) <= 10000, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000, and there exist indices i and j with 0 <= i < j <= len(nums)-2 such that nums[i] > nums[i+1] and nums[j] > nums[j+1]. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
      (htwo : ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length - 2 ∧
        (nums.val[i]!).val > (nums.val[i + 1]!).val ∧
          (nums.val[j]!).val > (nums.val[j + 1]!).val) :
      ∃ r : Bool,
        Aegis.CheckPossibility.check_possibility nums = ok r ∧ r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
        (htwo : ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length - 2 ∧
          (nums.val[i]!).val > (nums.val[i + 1]!).val ∧
            (nums.val[j]!).val > (nums.val[j + 1]!).val), ∃ r : Bool,
          Aegis.CheckPossibility.check_possibility nums = ok r ∧ r = false) := by
    sorry

  /-- Whenever the function returns a result r with r = true and nums is not non-decreasing (that is, there exists k with 0 <= k < len(nums)-1 and nums[k] > nums[k+1]), there is exactly one index i such that 0 <= i < len(nums)-1 and nums[i] > nums[i+1].
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000) :
      ∀ r : Bool, Aegis.CheckPossibility.check_possibility nums = ok r → r = true →
        (∃ k : ℕ, k + 1 < nums.val.length ∧ (nums.val[k]!).val > (nums.val[k + 1]!).val) →
          ∃! i : ℕ, i + 1 < nums.val.length ∧ (nums.val[i]!).val > (nums.val[i + 1]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000), ∀ r : Bool, Aegis.CheckPossibility.check_possibility nums = ok r → r = true →
          (∃ k : ℕ, k + 1 < nums.val.length ∧ (nums.val[k]!).val > (nums.val[k + 1]!).val) →
            ∃! i : ℕ, i + 1 < nums.val.length ∧ (nums.val[i]!).val > (nums.val[i + 1]!).val) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: 1 <= len(nums) <= 10000, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000, and for every i with 1 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
      (hsorted : ∀ i : ℕ, 1 ≤ i → i + 1 < nums.val.length →
        (nums.val[i]!).val ≤ (nums.val[i + 1]!).val) :
      ∃ r : Bool,
        Aegis.CheckPossibility.check_possibility nums = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
        (hsorted : ∀ i : ℕ, 1 ≤ i → i + 1 < nums.val.length →
          (nums.val[i]!).val ≤ (nums.val[i + 1]!).val), ∃ r : Bool,
          Aegis.CheckPossibility.check_possibility nums = ok r ∧ r = true) := by
    sorry

  /-- Let i be that unique index. The function returns a result r and r = true if and only if (i = 0 or i = len(nums)-2 or (i >= 1 and nums[i-1] <= nums[i+1]) or (i+2 < len(nums) and nums[i] <= nums[i+2])), with out-of-range terms guarded by the displayed inequalities and otherwise ignored.
    Preconditions: 1 <= len(nums) <= 10000, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000, and there is exactly one index i with 0 <= i < len(nums)-1 and nums[i] > nums[i+1]. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
      (i : ℕ)
      (hi : i + 1 < nums.val.length)
      (hdescent : (nums.val[i]!).val > (nums.val[i + 1]!).val)
      (hunique : ∀ k : ℕ, k + 1 < nums.val.length →
        (nums.val[k]!).val > (nums.val[k + 1]!).val → k = i) :
      ∃ r : Bool,
        Aegis.CheckPossibility.check_possibility nums = ok r ∧
          (r = true ↔
            (i = 0 ∨
              i = nums.val.length - 2 ∨
              (1 ≤ i ∧ (nums.val[i - 1]!).val ≤ (nums.val[i + 1]!).val) ∨
              (i + 2 < nums.val.length ∧ (nums.val[i]!).val ≤ (nums.val[i + 2]!).val))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
        (i : ℕ)
        (hi : i + 1 < nums.val.length)
        (hdescent : (nums.val[i]!).val > (nums.val[i + 1]!).val)
        (hunique : ∀ k : ℕ, k + 1 < nums.val.length →
          (nums.val[k]!).val > (nums.val[k + 1]!).val → k = i), ∃ r : Bool,
          Aegis.CheckPossibility.check_possibility nums = ok r ∧
            (r = true ↔
              (i = 0 ∨
                i = nums.val.length - 2 ∨
                (1 ≤ i ∧ (nums.val[i - 1]!).val ≤ (nums.val[i + 1]!).val) ∨
                (i + 2 < nums.val.length ∧ (nums.val[i]!).val ≤ (nums.val[i + 2]!).val)))) := by
    sorry

  /-- Whenever check_possibility(nums) returns a result r and check_possibility(nums') returns a result r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 10000, for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. Let c be an integer and nums' a slice of length len(nums) such that nums'[i] = nums[i] + c for every i with 0 <= i < len(nums), and -100000 <= nums'[i] <= 100000 for every i. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (c : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
      (hbounds : ∀ i : ℕ, i < nums.val.length →
        -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
      (hlen_eq : nums'.val.length = nums.val.length)
      (hshift : ∀ i : ℕ, i < nums.val.length → (nums'.val[i]!).val = (nums.val[i]!).val + c)
      (hbounds' : ∀ i : ℕ, i < nums'.val.length →
        -100000 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000) :
      ∀ r r' : Bool,
        Aegis.CheckPossibility.check_possibility nums = ok r →
          Aegis.CheckPossibility.check_possibility nums' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 10000)
        (hbounds : ∀ i : ℕ, i < nums.val.length →
          -100000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100000)
        (hlen_eq : nums'.val.length = nums.val.length)
        (hshift : ∀ i : ℕ, i < nums.val.length → (nums'.val[i]!).val = (nums.val[i]!).val + c)
        (hbounds' : ∀ i : ℕ, i < nums'.val.length →
          -100000 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 100000), ∀ r r' : Bool,
          Aegis.CheckPossibility.check_possibility nums = ok r →
            Aegis.CheckPossibility.check_possibility nums' = ok r' → r = r') := by
    sorry

  end AegisSpec.CheckPossibility
