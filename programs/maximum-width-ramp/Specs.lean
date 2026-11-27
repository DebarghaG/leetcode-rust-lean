import Aegis.MaxWidthRamp.Code.Funs

/-!
# Specifications of `Aegis.MaxWidthRamp.max_width_ramp`

LeetCode problem `maximum-width-ramp`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxWidthRamp

  def IsRamp (nums : Slice Std.I64) (i j : ℕ) : Prop :=
    ∃ (_hij : i < j) (_hj : j < nums.val.length), (nums.val[i]).val ≤ (nums.val[j]).val

  def rampWidth (i j : ℕ) : ℤ := (j : ℤ) - (i : ℤ)

  def rampWidths (nums : Slice Std.I64) : Set ℤ :=
    {d : ℤ | ∃ i j : ℕ, IsRamp nums i j ∧ d = rampWidth i j}

  /-- The function returns a result r and r is the maximum of the set { j - i | 0 <= i < j < len(nums) and nums[i] <= nums[j] } when this set is nonempty; if this set is empty, r = 0.
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∃ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r ∧
        ((∃ d : ℤ, d ∈ rampWidths nums) →
          r.val ∈ rampWidths nums ∧
            ∀ d : ℤ, d ∈ rampWidths nums → d ≤ r.val) ∧
        ((¬ ∃ d : ℤ, d ∈ rampWidths nums) → r.val = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∃ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r ∧
          ((∃ d : ℤ, d ∈ rampWidths nums) →
            r.val ∈ rampWidths nums ∧
              ∀ d : ℤ, d ∈ rampWidths nums → d ≤ r.val) ∧
          ((¬ ∃ d : ℤ, d ∈ rampWidths nums) → r.val = 0)) := by
    sorry

  /-- For every input satisfying the preconditions, the function does not fail: there exists an integer r such that the result is Ok r.
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∃ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∃ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) - 1.
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there do not exist indices i and j with 0 <= i < j < len(nums) and nums[i] <= nums[j].
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        (r.val = 0 ↔ ¬ ∃ i j : ℕ, IsRamp nums i j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          (r.val = 0 ↔ ¬ ∃ i j : ℕ, IsRamp nums i j)) := by
    sorry

  /-- Whenever the function returns a result r and r > 0, there exist indices i and j with 0 <= i < j < len(nums), j - i = r, and nums[i] <= nums[j].
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        0 < r.val → ∃ i j : ℕ, IsRamp nums i j ∧ rampWidth i j = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          0 < r.val → ∃ i j : ℕ, IsRamp nums i j ∧ rampWidth i j = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices i and j with 0 <= i < j < len(nums) and nums[i] <= nums[j], we have j - i <= r.
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        ∀ i j : ℕ, IsRamp nums i j → rampWidth i j ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          ∀ i j : ℕ, IsRamp nums i j → rampWidth i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) - 1 if and only if nums[0] <= nums[len(nums) - 1].
    Preconditions: 2 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        (r.val = (nums.val.length : ℤ) - 1 ↔
          (nums.val[0]).val ≤ (nums.val[nums.val.length - 1]).val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          (r.val = (nums.val.length : ℤ) - 1 ↔
            (nums.val[0]).val ≤ (nums.val[nums.val.length - 1]).val)) := by
    sorry

  /-- For every slice nums' with len(nums') = len(nums) and nums'[i] = nums[i] + c for every i with 0 <= i < len(nums), whenever max_width_ramp(nums) returns r and max_width_ramp(nums') returns r', we have r' = r.
    Preconditions: 2 <= len(nums) <= 50000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000, and c is an integer such that for every i with 0 <= i < len(nums), 0 <= nums[i] + c <= 50000. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (c : ℤ)
      (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000)
      (hc : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ 50000)
      (hlen' : nums'.val.length = nums.val.length)
      (hvals : ∀ (i : ℕ) (_hi : i < nums.val.length),
        (nums'.val[i]).val = (nums.val[i]).val + c) :
      ∀ r r' : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
        Aegis.MaxWidthRamp.max_width_ramp nums' = Aeneas.Std.Result.ok r' → r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (hlen : 2 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 50000)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000)
        (hc : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ 50000)
        (hlen' : nums'.val.length = nums.val.length)
        (hvals : ∀ (i : ℕ) (_hi : i < nums.val.length),
          (nums'.val[i]).val = (nums.val[i]).val + c), ∀ r r' : Std.I64, Aegis.MaxWidthRamp.max_width_ramp nums = Aeneas.Std.Result.ok r →
          Aegis.MaxWidthRamp.max_width_ramp nums' = Aeneas.Std.Result.ok r' → r'.val = r.val) := by
    sorry

  /-- Whenever max_width_ramp(extended) returns a result r, r = len(nums).
    Preconditions: 1 <= len(nums) <= 49999, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50000, v is an integer with 0 <= v <= 50000 and nums[0] <= v, and extended is a slice with len(extended) = len(nums) + 1, extended[i] = nums[i] for every i with 0 <= i < len(nums), and extended[len(nums)] = v. -/
  theorem spec_10 (nums extended : Slice Std.I64) (v : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 49999)
      (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000)
      (hv : 0 ≤ v.val ∧ v.val ≤ 50000)
      (hv0 : (nums.val[0]).val ≤ v.val)
      (hlen_ext : extended.val.length = nums.val.length + 1)
      (hext : ∀ (i : ℕ) (_hi : i < nums.val.length), (extended.val[i]).val = (nums.val[i]).val)
      (hlast : (extended.val[nums.val.length]).val = v.val) :
      ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp extended = Aeneas.Std.Result.ok r →
        r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums extended : Slice Std.I64) (v : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 49999)
        (hrange : ∀ (i : ℕ) (_hi : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50000)
        (hv : 0 ≤ v.val ∧ v.val ≤ 50000)
        (hv0 : (nums.val[0]).val ≤ v.val)
        (hlen_ext : extended.val.length = nums.val.length + 1)
        (hext : ∀ (i : ℕ) (_hi : i < nums.val.length), (extended.val[i]).val = (nums.val[i]).val)
        (hlast : (extended.val[nums.val.length]).val = v.val), ∀ r : Std.I64, Aegis.MaxWidthRamp.max_width_ramp extended = Aeneas.Std.Result.ok r →
          r.val = (nums.val.length : ℤ)) := by
    sorry

  end AegisSpec.MaxWidthRamp
