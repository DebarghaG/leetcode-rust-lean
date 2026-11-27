import Aegis.MaxFrequencyElements.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequencyElements.max_frequency_elements`

LeetCode problem `count-elements-with-maximum-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxFrequencyElements

  namespace AegisSpec.MaxFrequencyElements

  def elems (nums : Slice I64) : List Int := nums.list.toList.map (fun x => x.val)

  def freq (nums : Slice I64) (v : Int) : ℕ :=
    ((elems nums).filter (fun w => w = v)).length

  def occurring (nums : Slice I64) : Finset Int := (elems nums).toFinset

  def IsMaxFreq (nums : Slice I64) (M : ℕ) : Prop :=
    0 < M ∧ (∃ v : Int, freq nums v = M) ∧ ∀ v : Int, freq nums v ≤ M

  def countMaxFreq (nums : Slice I64) (M : ℕ) : ℕ :=
    ((occurring nums).filter (fun v => freq nums v = M)).card

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Let M be the maximum of freq(v) over all integers v with freq(v) > 0, and let K be the number of integers v with freq(v) = M. The function returns a result r and r = M * K (equivalently, r is the sum of freq(v) over all integers v with freq(v) = M).
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice I64) (M : ℕ)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hM : IsMaxFreq nums M) :
      ∃ r : I64,
        max_frequency_elements nums = ok r ∧
          r.val = ((M * countMaxFreq nums M : ℕ) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (M : ℕ)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hM : IsMaxFreq nums M), ∃ r : I64,
          max_frequency_elements nums = ok r ∧
            r.val = ((M * countMaxFreq nums M : ℕ) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access memory out of bounds.
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice I64)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100) :
      ∃ r : I64, max_frequency_elements nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100), ∃ r : I64, max_frequency_elements nums = ok r) := by
    sorry

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let M be the maximum of freq(v) over all integers v with freq(v) > 0. Whenever the function returns a result r, r <= len(nums).
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice I64) (M : ℕ)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hM : IsMaxFreq nums M) (r : I64)
      (hr : max_frequency_elements nums = ok r) :
      r.val ≤ (nums.leng : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (M : ℕ)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hM : IsMaxFreq nums M) (r : I64)
        (hr : max_frequency_elements nums = ok r), r.val ≤ (nums.leng : Int)) := by
    sorry

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let M be the maximum of freq(v) over all integers v with freq(v) > 0. Whenever the function returns a result r, r >= M.
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice I64) (M : ℕ)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hM : IsMaxFreq nums M) (r : I64)
      (hr : max_frequency_elements nums = ok r) :
      (M : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (M : ℕ)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hM : IsMaxFreq nums M) (r : I64)
        (hr : max_frequency_elements nums = ok r), (M : Int) ≤ r.val) := by
    sorry

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let M be the maximum of freq(v) over all integers v with freq(v) > 0. Whenever the function returns a result r, M divides r; equivalently, there is an integer K >= 1 such that r = M * K.
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice I64) (M : ℕ)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hM : IsMaxFreq nums M) (r : I64)
      (hr : max_frequency_elements nums = ok r) :
      ∃ K : Int, 1 ≤ K ∧ r.val = (M : Int) * K := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (M : ℕ)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hM : IsMaxFreq nums M) (r : I64)
        (hr : max_frequency_elements nums = ok r), ∃ K : Int, 1 ≤ K ∧ r.val = (M : Int) * K) := by
    sorry

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r, r = len(nums) if and only if all integers v with freq(v) > 0 have the same frequency (i.e., there exists an integer f such that freq(v) = f for every v with freq(v) > 0).
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice I64)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100) (r : I64)
      (hr : max_frequency_elements nums = ok r) :
      (r.val = (nums.leng : Int)) ↔
        ∃ f : ℕ, ∀ v : Int, 0 < freq nums v → freq nums v = f := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100) (r : I64)
        (hr : max_frequency_elements nums = ok r), (r.val = (nums.leng : Int)) ↔
          ∃ f : ℕ, ∀ v : Int, 0 < freq nums v → freq nums v = f) := by
    sorry

  /-- Let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let M be the maximum of freq(v) over all integers v with freq(v) > 0. Whenever the function returns a result r, if exactly one integer v satisfies freq(v) = M, then r = M.
    Preconditions: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice I64) (M : ℕ)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hM : IsMaxFreq nums M) (r : I64)
      (hr : max_frequency_elements nums = ok r) :
      (∃! v : Int, freq nums v = M) → r.val = (M : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (M : ℕ)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hM : IsMaxFreq nums M) (r : I64)
        (hr : max_frequency_elements nums = ok r), (∃! v : Int, freq nums v = M) → r.val = (M : Int)) := by
    sorry

  /-- Whenever the function returns results r and r' on nums and nums' respectively, r = r'.
    Preconditions: Both nums and nums' are slices satisfying: 1 <= len(nums) <= 100, 1 <= len(nums') <= 100, all entries of nums and nums' lie in [1, 100], and for every integer v, freq(nums, v) = freq(nums', v), where freq(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v. -/
  theorem spec_8 (nums nums' : Slice I64)
      (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
      (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
      (hlen2 : 1 ≤ nums'.leng) (hlen2' : nums'.leng ≤ 100)
      (hval2 : ∀ w ∈ elems nums', 1 ≤ w ∧ w ≤ 100)
      (hfreq : ∀ v : Int, freq nums v = freq nums' v)
      (r r' : I64)
      (hr : max_frequency_elements nums = ok r)
      (hr' : max_frequency_elements nums' = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlen : 1 ≤ nums.leng) (hlen' : nums.leng ≤ 100)
        (hval : ∀ w ∈ elems nums, 1 ≤ w ∧ w ≤ 100)
        (hlen2 : 1 ≤ nums'.leng) (hlen2' : nums'.leng ≤ 100)
        (hval2 : ∀ w ∈ elems nums', 1 ≤ w ∧ w ≤ 100)
        (hfreq : ∀ v : Int, freq nums v = freq nums' v)
        (r r' : I64)
        (hr : max_frequency_elements nums = ok r)
        (hr' : max_frequency_elements nums' = ok r'), r = r') := by
    sorry

  end AegisSpec.MaxFrequencyElements
