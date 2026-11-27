import Aegis.FindMaxLength.Code.Funs

/-!
# Specifications of `Aegis.FindMaxLength.find_max_length`

LeetCode problem `contiguous-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindMaxLength (find_max_length)

namespace AegisSpec.FindMaxLength

def countIn (l : List I64) (c : ℤ) (i j : ℕ) : ℕ :=
  ((l.drop i).take (j - i)).countP (fun x => x.val == c)

def balanced (l : List I64) (i j : ℕ) : Prop := countIn l 0 i j = countIn l 1 i j

def zeros (l : List I64) : ℕ := countIn l 0 0 l.length

def ones (l : List I64) : ℕ := countIn l 1 0 l.length

def occursAt (l : List I64) (c : ℤ) : Prop :=
  ∃ a : ℕ, ∃ ha : a < l.length, (l.get ⟨a, ha⟩).val = c

def sliceOfList (l : List I64) (h : l.length ≤ Usize.max) : Slice I64 :=
  { leng := l.length, list := Aeneas.Data.ListN.ListN.fromList l, bound := h }

lemma val_sliceOfList (l : List I64) (h : l.length ≤ Usize.max) :
    (sliceOfList l h).val = l := by
  simp [sliceOfList, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

lemma val_length_le_max (s : Slice I64) : s.val.length ≤ Usize.max := by
  have h1 := s.bound
  have h2 : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
  omega

def reverseSlice (nums : Slice I64) : Slice I64 :=
  sliceOfList nums.val.reverse (by
    rw [List.length_reverse]
    exact val_length_le_max nums)

lemma val_reverseSlice (nums : Slice I64) : (reverseSlice nums).val = nums.val.reverse := by
  simp [reverseSlice, val_sliceOfList]

def complementVal (x : I64) : I64 := if x.val = 0 then 1#i64 else 0#i64

def complementSlice (nums : Slice I64) : Slice I64 :=
  sliceOfList (nums.val.map complementVal) (by
    rw [List.length_map]
    exact val_length_le_max nums)

lemma val_complementSlice (nums : Slice I64) :
    (complementSlice nums).val = nums.val.map complementVal := by
  simp [complementSlice, val_sliceOfList]

/-- Whenever find_max_length(nums) returns a result r, both of the following hold: (1) there exist indices i,j with 0 <= i <= j <= len(nums) such that the interval [i,j) contains the same number of entries equal to 0 as entries equal to 1, and j - i = r; (2) for every pair of indices i,j with 0 <= i <= j <= len(nums), if the interval [i,j) contains the same number of entries equal to 0 as entries equal to 1, then j - i <= r.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_1 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r →
      (∃ i j : ℕ, i ≤ j ∧ j ≤ nums.val.length ∧ balanced nums.val i j ∧
          (j : ℤ) - (i : ℤ) = r.val) ∧
        (∀ i j : ℕ, i ≤ j → j ≤ nums.val.length → balanced nums.val i j →
          (j : ℤ) - (i : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r →
      (∃ i j : ℕ, i ≤ j ∧ j ≤ nums.val.length ∧ balanced nums.val i j ∧
          (j : ℤ) - (i : ℤ) = r.val) ∧
        (∀ i j : ℕ, i ≤ j → j ≤ nums.val.length → balanced nums.val i j →
          (j : ℤ) - (i : ℤ) ≤ r.val)) := by
  sorry

/-- For every input satisfying the preconditions, find_max_length(nums) returns a result r; that is, it does not fail, panic, overflow, or go out of bounds.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_2 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∃ r : I64, find_max_length nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∃ r : I64, find_max_length nums = ok r) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, 0 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_3 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, r is even; equivalently, there exists an integer m such that r = 2*m.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_4 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r → ∃ m : ℤ, r.val = 2 * m := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r → ∃ m : ℤ, r.val = 2 * m) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, r = 0 if and only if for every i,j with 0 <= i < j <= len(nums), the interval [i,j) does not contain equal numbers of 0 and 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_5 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j ≤ nums.val.length → ¬ balanced nums.val i j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j ≤ nums.val.length → ¬ balanced nums.val i j)) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, r >= 2 if and only if there exists an index a with 0 <= a < len(nums) and nums[a] = 0, and there exists an index b with 0 <= b < len(nums) and nums[b] = 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_6 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r →
      ((2 : ℤ) ≤ r.val ↔ occursAt nums.val 0 ∧ occursAt nums.val 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r →
      ((2 : ℤ) ≤ r.val ↔ occursAt nums.val 0 ∧ occursAt nums.val 1)) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, let z be the number of indices k with 0 <= k < len(nums) and nums[k] = 0, and let o be the number of indices k with 0 <= k < len(nums) and nums[k] = 1. Then r <= 2 * min(z, o).
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_7 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r →
      r.val ≤ 2 * ((min (zeros nums.val) (ones nums.val) : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r →
      r.val ≤ 2 * ((min (zeros nums.val) (ones nums.val) : ℕ) : ℤ)) := by
  sorry

/-- Whenever find_max_length(nums) returns a result r, r = len(nums) if and only if the interval [0, len(nums)) contains equal numbers of 0 and 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_8 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r : I64, find_max_length nums = ok r →
      (r.val = (nums.val.length : ℤ) ↔ balanced nums.val 0 nums.val.length) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r : I64, find_max_length nums = ok r →
      (r.val = (nums.val.length : ℤ) ↔ balanced nums.val 0 nums.val.length)) := by
  sorry

/-- Let rev(nums) be the slice of length len(nums) with rev(nums)[k] = nums[len(nums)-1-k] for every 0 <= k < len(nums). Whenever find_max_length(nums) returns a result r and find_max_length(rev(nums)) returns a result r', we have r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_9 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r r' : I64, find_max_length nums = ok r →
      find_max_length (reverseSlice nums) = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r r' : I64, find_max_length nums = ok r →
      find_max_length (reverseSlice nums) = ok r' → r' = r) := by
  sorry

/-- Let comp(nums) be the slice of length len(nums) with comp(nums)[k] = 1 - nums[k] for every 0 <= k < len(nums). Whenever find_max_length(nums) returns a result r and find_max_length(comp(nums)) returns a result r', we have r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and for every k with 0 <= k < len(nums), nums[k] is either 0 or 1. -/
theorem spec_10 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1) :
    ∀ r r' : I64, find_max_length nums = ok r →
      find_max_length (complementSlice nums) = ok r' → r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbit : ∀ x ∈ nums.val, x.val = 0 ∨ x.val = 1), ∀ r r' : I64, find_max_length nums = ok r →
      find_max_length (complementSlice nums) = ok r' → r' = r) := by
  sorry

end AegisSpec.FindMaxLength
