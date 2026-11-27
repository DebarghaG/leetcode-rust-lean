import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-operations-to-make-all-array-elements-equal-to-1`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOperations

namespace AegisSpec.MinOperations

def contents (nums : Slice I64) : List Int := nums.list.toList.map (fun x => x.val)

def listGcd (l : List Int) : ℕ := l.foldl (fun acc x => Nat.gcd acc x.natAbs) 0

def countOnes (l : List Int) : ℕ := l.countP (fun x => decide (x = 1))

def subarray (l : List Int) (s k : ℕ) : List Int := (l.drop s).take k

def IsMinGcdOneLen (l : List Int) (L : ℕ) : Prop :=
  (∃ s : ℕ, s + L ≤ l.length ∧ listGcd (subarray l s L) = 1) ∧
    ∀ k : ℕ, (∃ s : ℕ, s + k ≤ l.length ∧ listGcd (subarray l s k) = 1) → L ≤ k

def AllShortSubarraysGcdGt (l : List Int) (m : ℕ) : Prop :=
  ∀ (k : ℕ), 0 < k → k < m → ∀ s : ℕ, s + k ≤ l.length → 1 < listGcd (subarray l s k)

def AllOnes (l : List Int) : Prop := ∀ x ∈ l, x = 1

def Step (l l' : List Int) : Prop :=
  ∃ (i : ℕ) (_ : i + 1 < l.length),
    l' = l.set i ((Nat.gcd (l[i]).natAbs (l[i + 1]).natAbs : ℕ) : Int) ∨
      l' = l.set (i + 1) ((Nat.gcd (l[i]).natAbs (l[i + 1]).natAbs : ℕ) : Int)

def Steps : ℕ → List Int → List Int → Prop
  | 0, l, l' => l' = l
  | k + 1, l, l' => ∃ m : List Int, Steps k l m ∧ Step m l'

def mkSlice (l : List I64) (h : l.length ≤ Usize.max) : Slice I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def reverseSlice (nums : Slice I64) : Slice I64 :=
  mkSlice nums.list.toList.reverse (by
    rw [List.length_reverse, Aeneas.Data.ListN.ListN_length]
    exact nums.bound)

theorem contents_reverseSlice (nums : Slice I64) :
    contents (reverseSlice nums) = (contents nums).reverse := by
  simp [contents, reverseSlice, mkSlice, Aeneas.Data.ListN.ListN.from_to_inverse,
    List.map_reverse]

/-- Whenever the function returns a result r, the following holds. Let n = len(nums). Let g be the gcd of all elements nums[0], nums[1], ..., nums[n-1]. Let c be the number of indices i with 0 <= i < n and nums[i] = 1. If g > 1, then r = -1. If g = 1 and c > 0, then r = n - c. If g = 1 and c = 0, let L be the minimum length of a contiguous subarray of nums whose gcd is 1 (such an L exists because g = 1). Then r = L + n - 2.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_1 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r →
      (1 < listGcd (contents nums) → r.val = -1) ∧
      (listGcd (contents nums) = 1 → 0 < countOnes (contents nums) →
        r.val = ((contents nums).length : ℤ) - (countOnes (contents nums) : ℤ)) ∧
      (listGcd (contents nums) = 1 → countOnes (contents nums) = 0 →
        ∀ L : ℕ, IsMinGcdOneLen (contents nums) L →
          r.val = (L : ℤ) + ((contents nums).length : ℤ) - 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r →
      (1 < listGcd (contents nums) → r.val = -1) ∧
      (listGcd (contents nums) = 1 → 0 < countOnes (contents nums) →
        r.val = ((contents nums).length : ℤ) - (countOnes (contents nums) : ℤ)) ∧
      (listGcd (contents nums) = 1 → countOnes (contents nums) = 0 →
        ∀ L : ℕ, IsMinGcdOneLen (contents nums) L →
          r.val = (L : ℤ) + ((contents nums).length : ℤ) - 2)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (i.e., the Result is Ok, not Err).
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_2 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∃ r : I64, min_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∃ r : I64, min_operations nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if the gcd of all elements of nums is greater than 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_3 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → (r.val = -1 ↔ 1 < listGcd (contents nums)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → (r.val = -1 ↔ 1 < listGcd (contents nums))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if every element of nums is equal to 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_4 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r →
      (r.val = 0 ↔ ∀ x ∈ contents nums, x = 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r →
      (r.val = 0 ↔ ∀ x ∈ contents nums, x = 1)) := by
  sorry

/-- Whenever the function returns a result r, if there is at least one index i with nums[i] = 1, then r = len(nums) - c, where c is the number of indices i with nums[i] = 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_5 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → 0 < countOnes (contents nums) →
      r.val = ((contents nums).length : ℤ) - (countOnes (contents nums) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → 0 < countOnes (contents nums) →
      r.val = ((contents nums).length : ℤ) - (countOnes (contents nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with nums[i] = 1, the gcd of all elements is 1, and there exists an index i with 0 <= i < len(nums) - 1 such that gcd(nums[i], nums[i+1]) = 1, then r = len(nums).
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_6 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      (∃ (i : ℕ) (_ : i + 1 < (contents nums).length),
        listGcd (subarray (contents nums) i 2) = 1) →
      r.val = ((contents nums).length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      (∃ (i : ℕ) (_ : i + 1 < (contents nums).length),
        listGcd (subarray (contents nums) i 2) = 1) →
      r.val = ((contents nums).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with nums[i] = 1, the gcd of all elements is 1, and for every contiguous subarray of length strictly less than len(nums) its gcd is greater than 1, then r = 2 * len(nums) - 2.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_7 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      AllShortSubarraysGcdGt (contents nums) (contents nums).length →
      r.val = 2 * ((contents nums).length : ℤ) - 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      AllShortSubarraysGcdGt (contents nums) (contents nums).length →
      r.val = 2 * ((contents nums).length : ℤ) - 2) := by
  sorry

/-- Whenever the function returns a result r, if r != -1, then 0 <= r <= 2 * len(nums) - 2.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_8 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → r.val ≠ -1 →
      0 ≤ r.val ∧ r.val ≤ 2 * ((contents nums).length : ℤ) - 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → r.val ≠ -1 →
      0 ≤ r.val ∧ r.val ≤ 2 * ((contents nums).length : ℤ) - 2) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with nums[i] = 1 and the gcd of all elements is 1, then r >= len(nums).
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_9 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      ((contents nums).length : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      ((contents nums).length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with nums[i] = 1, the gcd of all elements is 1, and for every i with 0 <= i < len(nums) - 1 we have gcd(nums[i], nums[i+1]) > 1, then r >= len(nums) + 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_10 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      (∀ (i : ℕ) (_ : i + 1 < (contents nums).length),
        1 < listGcd (subarray (contents nums) i 2)) →
      ((contents nums).length : ℤ) + 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → countOnes (contents nums) = 0 →
      listGcd (contents nums) = 1 →
      (∀ (i : ℕ) (_ : i + 1 < (contents nums).length),
        1 < listGcd (subarray (contents nums) i 2)) →
      ((contents nums).length : ℤ) + 1 ≤ r.val) := by
  sorry

/-- For any input nums satisfying the preconditions, the result of min_operations(nums) equals the result of min_operations(reverse(nums)), where reverse(nums) is the slice with elements in reverse order (i.e., reverse(nums)[i] = nums[len(nums)-1-i]). That is, whenever both return results, they are equal.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_11 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r r' : I64,
      min_operations nums = ok r → min_operations (reverseSlice nums) = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r r' : I64,
      min_operations nums = ok r → min_operations (reverseSlice nums) = ok r' → r.val = r'.val) := by
  sorry

/-- For any two inputs nums and nums' satisfying the preconditions, if len(nums) = len(nums'), if there exists an index j with 0 <= j < len(nums) and nums[j] = 1, and if for every i with 0 <= i < len(nums), nums[i] = 1 if and only if nums'[i] = 1, then whenever min_operations(nums) returns r and min_operations(nums') returns r', we have r = r'.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_12 (nums nums' : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6)
    (hlen2' : 2 ≤ (contents nums').length) (hlen50' : (contents nums').length ≤ 50)
    (hbound' : ∀ (i : ℕ) (hi : i < (contents nums').length),
      1 ≤ (contents nums')[i] ∧ (contents nums')[i] ≤ 10 ^ 6)
    (hlen : (contents nums).length = (contents nums').length)
    (hj : ∃ (j : ℕ) (hj : j < (contents nums).length), (contents nums)[j] = 1)
    (hones : ∀ (i : ℕ) (hi : i < (contents nums).length) (hi' : i < (contents nums').length),
      ((contents nums)[i] = 1 ↔ (contents nums')[i] = 1)) :
    ∀ r r' : I64,
      min_operations nums = ok r → min_operations nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6)
    (hlen2' : 2 ≤ (contents nums').length) (hlen50' : (contents nums').length ≤ 50)
    (hbound' : ∀ (i : ℕ) (hi : i < (contents nums').length),
      1 ≤ (contents nums')[i] ∧ (contents nums')[i] ≤ 10 ^ 6)
    (hlen : (contents nums).length = (contents nums').length)
    (hj : ∃ (j : ℕ) (hj : j < (contents nums).length), (contents nums)[j] = 1)
    (hones : ∀ (i : ℕ) (hi : i < (contents nums).length) (hi' : i < (contents nums').length),
      ((contents nums)[i] = 1 ↔ (contents nums')[i] = 1)), ∀ r r' : I64,
      min_operations nums = ok r → min_operations nums' = ok r' → r.val = r'.val) := by
  sorry

/-- For any two inputs nums and nums' satisfying the preconditions, both with no element equal to 1 and both with gcd of all elements equal to 1, if they have the same length n and the same minimum length L of a contiguous subarray with gcd 1, then the result of min_operations(nums) equals the result of min_operations(nums') (whenever both return results).
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_13 (nums nums' : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6)
    (hlen2' : 2 ≤ (contents nums').length) (hlen50' : (contents nums').length ≤ 50)
    (hbound' : ∀ (i : ℕ) (hi : i < (contents nums').length),
      1 ≤ (contents nums')[i] ∧ (contents nums')[i] ≤ 10 ^ 6)
    (hlen : (contents nums).length = (contents nums').length)
    (hno1 : countOnes (contents nums) = 0) (hno1' : countOnes (contents nums') = 0)
    (hg : listGcd (contents nums) = 1) (hg' : listGcd (contents nums') = 1)
    (L : ℕ) (hL : IsMinGcdOneLen (contents nums) L)
    (hL' : IsMinGcdOneLen (contents nums') L) :
    ∀ r r' : I64,
      min_operations nums = ok r → min_operations nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6)
    (hlen2' : 2 ≤ (contents nums').length) (hlen50' : (contents nums').length ≤ 50)
    (hbound' : ∀ (i : ℕ) (hi : i < (contents nums').length),
      1 ≤ (contents nums')[i] ∧ (contents nums')[i] ≤ 10 ^ 6)
    (hlen : (contents nums).length = (contents nums').length)
    (hno1 : countOnes (contents nums) = 0) (hno1' : countOnes (contents nums') = 0)
    (hg : listGcd (contents nums) = 1) (hg' : listGcd (contents nums') = 1)
    (L : ℕ) (hL : IsMinGcdOneLen (contents nums) L)
    (hL' : IsMinGcdOneLen (contents nums') L), ∀ r r' : I64,
      min_operations nums = ok r → min_operations nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists a sequence of exactly r operations (each operation selects an index i with 0 <= i < len(nums)-1 and replaces either nums[i] or nums[i+1] with their gcd) that transforms the array nums into an array all of whose elements are 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_14 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → 0 ≤ r.val →
      ∃ k : ℕ, (k : ℤ) = r.val ∧ ∃ l' : List Int, Steps k (contents nums) l' ∧ AllOnes l' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → 0 ≤ r.val →
      ∃ k : ℕ, (k : ℤ) = r.val ∧ ∃ l' : List Int, Steps k (contents nums) l' ∧ AllOnes l') := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there is no sequence of strictly fewer than r operations (as defined in spec_14) that transforms the array nums into an array all of whose elements are 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_15 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ k : ℕ, (k : ℤ) < r.val →
        ¬ ∃ l' : List Int, Steps k (contents nums) l' ∧ AllOnes l' := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → 0 ≤ r.val →
      ∀ k : ℕ, (k : ℤ) < r.val →
        ¬ ∃ l' : List Int, Steps k (contents nums) l' ∧ AllOnes l') := by
  sorry

/-- Whenever the function returns r = -1, there is no sequence of operations (as defined in spec_14) that transforms the array nums into an array all of whose elements are 1.
  Preconditions: 2 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^6. -/
theorem spec_16 (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6) :
    ∀ r : I64, min_operations nums = ok r → r.val = -1 →
      ¬ ∃ (k : ℕ) (l' : List Int), Steps k (contents nums) l' ∧ AllOnes l' := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ (contents nums).length) (hlen50 : (contents nums).length ≤ 50)
    (hbound : ∀ (i : ℕ) (hi : i < (contents nums).length),
      1 ≤ (contents nums)[i] ∧ (contents nums)[i] ≤ 10 ^ 6), ∀ r : I64, min_operations nums = ok r → r.val = -1 →
      ¬ ∃ (k : ℕ) (l' : List Int), Steps k (contents nums) l' ∧ AllOnes l') := by
  sorry

end AegisSpec.MinOperations
