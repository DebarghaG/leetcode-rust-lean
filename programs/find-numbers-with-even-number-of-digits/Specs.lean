import Aegis.FindNumbers.Code.Funs

/-!
# Specifications of `Aegis.FindNumbers.find_numbers`

LeetCode problem `find-numbers-with-even-number-of-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindNumbers

  namespace AegisSpec.FindNumbers

  def HasEvenDigitCount (n : Int) : Prop :=
    ∃ k : ℕ, 1 ≤ k ∧ (10 : Int) ^ (2 * k - 1) ≤ n ∧ n < (10 : Int) ^ (2 * k)

  def HasOddDigitCount (n : Int) : Prop :=
    ∃ k : ℕ, (10 : Int) ^ (2 * k) ≤ n ∧ n < (10 : Int) ^ (2 * k + 1)

  def EntriesInRange (l : List Std.I64) : Prop :=
    ∀ i : Fin l.length, 1 ≤ (l.get i).val ∧ (l.get i).val ≤ 100000

  def IsSmallEvenDigitValue (n : Int) : Prop :=
    (10 ≤ n ∧ n ≤ 99) ∨ (1000 ≤ n ∧ n ≤ 9999) ∨ n = 100000

  noncomputable def countP (l : List Std.I64) (p : Std.I64 → Prop) : ℕ :=
    l.countP fun x => @decide (p x) (Classical.propDecidable (p x))

  noncomputable def evenDigitCount (l : List Std.I64) : ℕ :=
    countP l fun x => HasEvenDigitCount x.val

  noncomputable def oddDigitCount (l : List Std.I64) : ℕ :=
    countP l fun x => HasOddDigitCount x.val

  noncomputable def smallEvenDigitCount (l : List Std.I64) : ℕ :=
    countP l fun x => IsSmallEvenDigitValue x.val

  noncomputable def evenDigitCountBetween (l : List Std.I64) (a b : ℕ) : ℕ :=
    countP ((l.drop a).take (b - a)) fun x => HasEvenDigitCount x.val

  def IsIndexPermutation (nums permuted : Slice Std.I64) : Prop :=
    ∃ p : Equiv.Perm (Fin nums.val.length),
      permuted.val = (List.finRange nums.val.length).map fun i => nums.val.get (p i)

  /-- The function returns a result r and r = |{ i | 0 <= i < len(nums) and nums[i] has an even number of decimal digits }|. A positive integer n has an even number of decimal digits iff there exists an integer k >= 1 such that 10^(2k-1) <= n < 10^(2k).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val) :
      ∃ r : Std.I64,
        find_numbers nums = ok r ∧ r.val = (evenDigitCount nums.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val), ∃ r : Std.I64,
          find_numbers nums = ok r ∧ r.val = (evenDigitCount nums.val : Int)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail by overflow, panic, or out-of-bounds access on any input satisfying the preconditions.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val) :
      ∃ r : Std.I64, find_numbers nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val), ∃ r : Std.I64, find_numbers nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(nums).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = |{ i | 0 <= i < len(nums) and (10 <= nums[i] <= 99 or 1000 <= nums[i] <= 9999 or nums[i] = 100000) }|.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      r.val = (smallEvenDigitCount nums.val : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), r.val = (smallEvenDigitCount nums.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r + o = len(nums), where o = |{ i | 0 <= i < len(nums) and nums[i] has an odd number of decimal digits }|. A positive integer n has an odd number of decimal digits iff there exists an integer k >= 0 such that 10^(2k) <= n < 10^(2k+1).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      r.val + (oddDigitCount nums.val : Int) = (nums.val.length : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), r.val + (oddDigitCount nums.val : Int) = (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 iff there is no index i with 0 <= i < len(nums) such that nums[i] has an even number of decimal digits.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      r.val = 0 ↔ ¬ ∃ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), r.val = 0 ↔ ¬ ∃ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) iff for every i with 0 <= i < len(nums), nums[i] has an even number of decimal digits.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      r.val = (nums.val.length : Int) ↔
        ∀ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), r.val = (nums.val.length : Int) ↔
          ∀ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val) := by
    sorry

  /-- For any permutation p of the index set {0,...,len(nums)-1}, let permuted be the slice with permuted[i] = nums[p(i)] for 0 <= i < len(nums). Whenever the function returns r on nums and r' on permuted, r = r'.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums permuted : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (h_perm : IsIndexPermutation nums permuted)
      (r r' : Std.I64)
      (hr : find_numbers nums = ok r) (hr' : find_numbers permuted = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums permuted : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (h_perm : IsIndexPermutation nums permuted)
        (r r' : Std.I64)
        (hr : find_numbers nums = ok r) (hr' : find_numbers permuted = ok r'), r.val = r'.val) := by
    sorry

  /-- For every split position k with 0 <= k <= len(nums), whenever the function returns r on nums, r = E(0,k) + E(k,len(nums)), where for 0 <= a <= b <= len(nums), E(a,b) is the number of indices i with a <= i < b such that nums[i] has an even number of decimal digits.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (k : ℕ) (hk : k ≤ nums.val.length)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      r.val = ((evenDigitCountBetween nums.val 0 k +
          evenDigitCountBetween nums.val k nums.val.length : ℕ) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (k : ℕ) (hk : k ≤ nums.val.length)
        (r : Std.I64) (hr : find_numbers nums = ok r), r.val = ((evenDigitCountBetween nums.val 0 k +
            evenDigitCountBetween nums.val k nums.val.length : ℕ) : Int)) := by
    sorry

  /-- Let extended be the slice obtained by appending v after nums. Whenever the function returns r on nums and r' on extended, if v has an even number of decimal digits then r' = r + 1, and if v has an odd number of decimal digits then r' = r.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 499, every entry of nums is an integer with 1 <= nums[i] <= 100000, and v is an integer with 1 <= v <= 100000. -/
  theorem spec_10 (nums extended : Slice Std.I64) (v : Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 499)
      (h_entries : EntriesInRange nums.val)
      (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
      (h_ext : extended.val = nums.val ++ [v])
      (r r' : Std.I64)
      (hr : find_numbers nums = ok r) (hr' : find_numbers extended = ok r') :
      (HasEvenDigitCount v.val → r'.val = r.val + 1) ∧
        (HasOddDigitCount v.val → r'.val = r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums extended : Slice Std.I64) (v : Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 499)
        (h_entries : EntriesInRange nums.val)
        (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
        (h_ext : extended.val = nums.val ++ [v])
        (r r' : Std.I64)
        (hr : find_numbers nums = ok r) (hr' : find_numbers extended = ok r'), (HasEvenDigitCount v.val → r'.val = r.val + 1) ∧
          (HasOddDigitCount v.val → r'.val = r.val)) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exists an index i with 0 <= i < len(nums) such that nums[i] has an even number of decimal digits; and if r < len(nums) then there exists an index j with 0 <= j < len(nums) such that nums[j] has an odd number of decimal digits.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, and for every i with 0 <= i < len(nums), nums[i] is an integer with 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (r : Std.I64) (hr : find_numbers nums = ok r) :
      (0 < r.val → ∃ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val) ∧
        (r.val < (nums.val.length : Int) →
          ∃ j : Fin nums.val.length, HasOddDigitCount (nums.val.get j).val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (r : Std.I64) (hr : find_numbers nums = ok r), (0 < r.val → ∃ i : Fin nums.val.length, HasEvenDigitCount (nums.val.get i).val) ∧
          (r.val < (nums.val.length : Int) →
            ∃ j : Fin nums.val.length, HasOddDigitCount (nums.val.get j).val)) := by
    sorry

  /-- Let modified be the slice obtained from nums by setting modified[i] = v and leaving all other positions unchanged. If nums[i] and v have the same parity of decimal-digit count (both even or both odd), then the function returns the same result on nums and on modified.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, every entry of nums is an integer with 1 <= nums[i] <= 100000, i is an index with 0 <= i < len(nums), and v is an integer with 1 <= v <= 100000. -/
  theorem spec_12 (nums modified : Slice Std.I64) (i : ℕ) (v : Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (h_i : i < nums.val.length)
      (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
      (h_mod : modified.val = nums.val.set i v)
      (h_same : HasEvenDigitCount v.val ↔ HasEvenDigitCount (nums.val.get ⟨i, h_i⟩).val)
      (r r' : Std.I64)
      (hr : find_numbers nums = ok r) (hr' : find_numbers modified = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums modified : Slice Std.I64) (i : ℕ) (v : Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (h_i : i < nums.val.length)
        (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
        (h_mod : modified.val = nums.val.set i v)
        (h_same : HasEvenDigitCount v.val ↔ HasEvenDigitCount (nums.val.get ⟨i, h_i⟩).val)
        (r r' : Std.I64)
        (hr : find_numbers nums = ok r) (hr' : find_numbers modified = ok r'), r.val = r'.val) := by
    sorry

  /-- Let modified be the slice obtained from nums by setting modified[i] = v and leaving all other positions unchanged. If nums[i] has an odd number of decimal digits and v has an even number, then r' = r + 1, where r and r' are the results on nums and modified; if nums[i] has an even number and v has an odd number, then r' = r - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 500, every entry of nums is an integer with 1 <= nums[i] <= 100000, i is an index with 0 <= i < len(nums), and v is an integer with 1 <= v <= 100000. -/
  theorem spec_13 (nums modified : Slice Std.I64) (i : ℕ) (v : Std.I64)
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
      (h_entries : EntriesInRange nums.val)
      (h_i : i < nums.val.length)
      (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
      (h_mod : modified.val = nums.val.set i v)
      (r r' : Std.I64)
      (hr : find_numbers nums = ok r) (hr' : find_numbers modified = ok r') :
      (HasOddDigitCount (nums.val.get ⟨i, h_i⟩).val → HasEvenDigitCount v.val →
          r'.val = r.val + 1) ∧
        (HasEvenDigitCount (nums.val.get ⟨i, h_i⟩).val → HasOddDigitCount v.val →
          r'.val = r.val - 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums modified : Slice Std.I64) (i : ℕ) (v : Std.I64)
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 500)
        (h_entries : EntriesInRange nums.val)
        (h_i : i < nums.val.length)
        (h_v : 1 ≤ v.val ∧ v.val ≤ 100000)
        (h_mod : modified.val = nums.val.set i v)
        (r r' : Std.I64)
        (hr : find_numbers nums = ok r) (hr' : find_numbers modified = ok r'), (HasOddDigitCount (nums.val.get ⟨i, h_i⟩).val → HasEvenDigitCount v.val →
            r'.val = r.val + 1) ∧
          (HasEvenDigitCount (nums.val.get ⟨i, h_i⟩).val → HasOddDigitCount v.val →
            r'.val = r.val - 1)) := by
    sorry

  end AegisSpec.FindNumbers
