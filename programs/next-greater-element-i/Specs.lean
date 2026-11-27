import Aegis.NextGreaterElement.Code.Funs

/-!
# Specifications of `Aegis.NextGreaterElement.next_greater_element`

LeetCode problem `next-greater-element-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NextGreaterElement

namespace AegisSpec.NextGreaterElement

def contents (s : Slice I64) : List Int := s.val.map (fun x => x.val)

def vecContents (v : alloc.vec.Vec I64) : List Int := v.val.map (fun x => x.val)

def IsIndex (s : Slice I64) (x : Int) (j : Nat) : Prop :=
  j < (contents s).length ∧ (contents s)[j]! = x

def FirstGreaterAfter (s : Slice I64) (j : Nat) (x : Int) (k : Nat) : Prop :=
  j < k ∧ k < (contents s).length ∧ x < (contents s)[k]! ∧
    ∀ m : Nat, j < m → m < k → (contents s)[m]! < x

def NoGreaterAfter (s : Slice I64) (j : Nat) (x : Int) : Prop :=
  ∀ k : Nat, j < k → k < (contents s).length → (contents s)[k]! < x

def StrictlyIncreasing (s : Slice I64) : Prop :=
  ∀ j j' : Nat, j < j' → j' < (contents s).length → (contents s)[j]! < (contents s)[j']!

def StrictlyDecreasing (s : Slice I64) : Prop :=
  ∀ j j' : Nat, j < j' → j' < (contents s).length → (contents s)[j']! < (contents s)[j]!

def Pre (nums1 nums2 : Slice I64) : Prop :=
  1 ≤ (contents nums1).length ∧
  (contents nums1).length ≤ (contents nums2).length ∧
  (contents nums2).length ≤ 1000 ∧
  (∀ i : Nat, i < (contents nums1).length → 0 ≤ (contents nums1)[i]! ∧ (contents nums1)[i]! ≤ 10000) ∧
  (∀ j : Nat, j < (contents nums2).length → 0 ≤ (contents nums2)[j]! ∧ (contents nums2)[j]! ≤ 10000) ∧
  (∀ i i' : Nat, i < i' → i' < (contents nums1).length → (contents nums1)[i]! ≠ (contents nums1)[i']!) ∧
  (∀ j j' : Nat, j < j' → j' < (contents nums2).length → (contents nums2)[j]! ≠ (contents nums2)[j']!) ∧
  (∀ i : Nat, i < (contents nums1).length →
    ∃ j : Nat, j < (contents nums2).length ∧ (contents nums2)[j]! = (contents nums1)[i]!)

/-- The function returns a result r (a vector of i64) such that len(r) = len(nums1), and for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], the following holds: either (a) there exists k with j < k < len(nums2) such that nums2[k] > nums1[i], for every m with j < m < k it holds nums2[m] < nums1[i], and r[i] = nums2[k]; or (b) for every k with j < k < len(nums2) it holds nums2[k] < nums1[i], and r[i] = -1.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct (for every i, i' with 0 <= i < i' < len(nums1), nums1[i] != nums1[i']), all elements of nums2 are pairwise distinct (for every j, j' with 0 <= j < j' < len(nums2), nums2[j] != nums2[j']), and every element of nums1 appears in nums2 (for every i with 0 <= i < len(nums1) there exists j with 0 <= j < len(nums2) and nums2[j] = nums1[i]). -/
theorem spec_1 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∃ r : alloc.vec.Vec I64,
      next_greater_element nums1 nums2 = ok r ∧
      (vecContents r).length = (contents nums1).length ∧
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (∃ k : Nat,
              FirstGreaterAfter nums2 j (contents nums1)[i]! k ∧
                (vecContents r)[i]! = (contents nums2)[k]!) ∨
          (NoGreaterAfter nums2 j (contents nums1)[i]! ∧ (vecContents r)[i]! = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∃ r : alloc.vec.Vec I64,
      next_greater_element nums1 nums2 = ok r ∧
      (vecContents r).length = (contents nums1).length ∧
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (∃ k : Nat,
              FirstGreaterAfter nums2 j (contents nums1)[i]! k ∧
                (vecContents r)[i]! = (contents nums2)[k]!) ∨
          (NoGreaterAfter nums2 j (contents nums1)[i]! ∧ (vecContents r)[i]! = -1)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_2 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∃ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∃ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums1).
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_3 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      (vecContents r).length = (contents nums1).length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      (vecContents r).length = (contents nums1).length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), -1 <= r[i] <= 10000.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_4 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length → -1 ≤ (vecContents r)[i]! ∧ (vecContents r)[i]! ≤ 10000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length → -1 ≤ (vecContents r)[i]! ∧ (vecContents r)[i]! ≤ 10000) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], if r[i] != -1 then there exists a unique index k with 0 <= k < len(nums2) such that nums2[k] = r[i], and moreover j < k and r[i] > nums1[i].
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_5 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! ≠ -1 →
            ∃ k : Nat, IsIndex nums2 (vecContents r)[i]! k ∧
              (∀ k' : Nat, IsIndex nums2 (vecContents r)[i]! k' → k' = k) ∧
              j < k ∧ (contents nums1)[i]! < (vecContents r)[i]! := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! ≠ -1 →
            ∃ k : Nat, IsIndex nums2 (vecContents r)[i]! k ∧
              (∀ k' : Nat, IsIndex nums2 (vecContents r)[i]! k' → k' = k) ∧
              j < k ∧ (contents nums1)[i]! < (vecContents r)[i]!) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], if r[i] != -1 and k is the unique index with 0 <= k < len(nums2) and nums2[k] = r[i], then for every m with j < m < k it holds nums2[m] < nums1[i].
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_6 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! ≠ -1 →
            ∀ k : Nat, IsIndex nums2 (vecContents r)[i]! k →
              (∀ k' : Nat, IsIndex nums2 (vecContents r)[i]! k' → k' = k) →
                ∀ m : Nat, j < m → m < k → (contents nums2)[m]! < (contents nums1)[i]! := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! ≠ -1 →
            ∀ k : Nat, IsIndex nums2 (vecContents r)[i]! k →
              (∀ k' : Nat, IsIndex nums2 (vecContents r)[i]! k' → k' = k) →
                ∀ m : Nat, j < m → m < k → (contents nums2)[m]! < (contents nums1)[i]!) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], if r[i] = -1 then for every k with j < k < len(nums2) it holds nums2[k] < nums1[i].
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_7 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! = -1 → NoGreaterAfter nums2 j (contents nums1)[i]! := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          (vecContents r)[i]! = -1 → NoGreaterAfter nums2 j (contents nums1)[i]!) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], if for every k with j < k < len(nums2) it holds nums2[k] < nums1[i], then r[i] = -1.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_8 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          NoGreaterAfter nums2 j (contents nums1)[i]! → (vecContents r)[i]! = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          NoGreaterAfter nums2 j (contents nums1)[i]! → (vecContents r)[i]! = -1) := by
  sorry

/-- Whenever the function returns a result r, if nums2 is strictly decreasing (i.e., for every j, j' with 0 <= j < j' < len(nums2), nums2[j] > nums2[j']), then for every i with 0 <= i < len(nums1), r[i] = -1.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_9 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      StrictlyDecreasing nums2 →
        ∀ i : Nat, i < (contents nums1).length → (vecContents r)[i]! = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      StrictlyDecreasing nums2 →
        ∀ i : Nat, i < (contents nums1).length → (vecContents r)[i]! = -1) := by
  sorry

/-- Whenever the function returns a result r, if nums2 is strictly increasing (i.e., for every j, j' with 0 <= j < j' < len(nums2), nums2[j] < nums2[j']), then for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], we have: if j + 1 < len(nums2) then r[i] = nums2[j+1], and if j = len(nums2) - 1 then r[i] = -1.
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_10 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      StrictlyIncreasing nums2 →
        ∀ i : Nat, i < (contents nums1).length →
          ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
            (j + 1 < (contents nums2).length → (vecContents r)[i]! = (contents nums2)[j + 1]!) ∧
            (j = (contents nums2).length - 1 → (vecContents r)[i]! = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      StrictlyIncreasing nums2 →
        ∀ i : Nat, i < (contents nums1).length →
          ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
            (j + 1 < (contents nums2).length → (vecContents r)[i]! = (contents nums2)[j + 1]!) ∧
            (j = (contents nums2).length - 1 → (vecContents r)[i]! = -1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums1), letting j be the unique index with 0 <= j < len(nums2) and nums2[j] = nums1[i], if j + 1 < len(nums2) and nums2[j+1] > nums1[i], then r[i] = nums2[j+1].
  Preconditions: len(nums1) >= 1, len(nums1) <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1) we have 0 <= nums1[i] <= 10000, for every j with 0 <= j < len(nums2) we have 0 <= nums2[j] <= 10000, all elements of nums1 are pairwise distinct, all elements of nums2 are pairwise distinct, and every element of nums1 appears in nums2. -/
theorem spec_11 (nums1 nums2 : Slice I64) (h : Pre nums1 nums2) :
    ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          j + 1 < (contents nums2).length → (contents nums1)[i]! < (contents nums2)[j + 1]! →
            (vecContents r)[i]! = (contents nums2)[j + 1]! := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h : Pre nums1 nums2), ∀ r : alloc.vec.Vec I64, next_greater_element nums1 nums2 = ok r →
      ∀ i : Nat, i < (contents nums1).length →
        ∀ j : Nat, IsIndex nums2 (contents nums1)[i]! j →
          j + 1 < (contents nums2).length → (contents nums1)[i]! < (contents nums2)[j + 1]! →
            (vecContents r)[i]! = (contents nums2)[j + 1]!) := by
  sorry

end AegisSpec.NextGreaterElement
