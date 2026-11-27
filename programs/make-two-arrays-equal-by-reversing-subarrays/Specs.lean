import Aegis.CanBeEqual.Code.Funs

/-!
# Specifications of `Aegis.CanBeEqual.can_be_equal`

LeetCode problem `make-two-arrays-equal-by-reversing-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanBeEqual

def inRange (xs : Slice I64) : Prop := ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 1000

def count (xs : Slice I64) (v : ℤ) : ℕ := (xs.val.filter (fun x => x.val = v)).length

def nondecreasing (xs : Slice I64) : Prop :=
  ∀ (i : ℕ) (_ : i + 1 < xs.val.length), (xs.val[i]'(by omega)).val ≤ (xs.val[i + 1]'(by omega)).val

def reverseSegment (a : List I64) (l u : ℕ) : List I64 :=
  a.take l ++ ((a.drop l).take (u + 1 - l)).reverse ++ a.drop (u + 1)

def reachableByReversals (a b : Slice I64) : Prop :=
  ∃ (k : ℕ) (s : ℕ → Slice I64),
    s 0 = a ∧ s k = b ∧
      (∀ t : ℕ, t ≤ k → (s t).val.length = a.val.length) ∧
      (∀ t : ℕ, t < k →
        ∃ l u : ℕ, l ≤ u ∧ u < (s t).val.length ∧
          (s (t + 1)).val = reverseSegment (s t).val l u)

/-- Let count(xs, v) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. The function returns a result r (it does not fail), and r = true if and only if for every integer v, count(arr, v) = count(target, v).
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, and every element of target and arr is an integer between 1 and 1000 inclusive. -/
theorem spec_1 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ v : ℤ, count arr v = count target v) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ v : ℤ, count arr v = count target v)) := by
  sorry

/-- The function returns a result r; equivalently, there exists a Boolean b such that can_be_equal target arr = ok b. It does not overflow, panic, or go out of bounds.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, and every element of target and arr is an integer between 1 and 1000 inclusive. -/
theorem spec_2 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r) := by
  sorry

/-- The calls can_be_equal target arr and can_be_equal arr target both return results, and their Boolean results are equal.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, and every element of target and arr is an integer between 1 and 1000 inclusive. -/
theorem spec_3 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr) :
    ∃ r₁ r₂ : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r₁ ∧
      Aegis.CanBeEqual.can_be_equal arr target = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr), ∃ r₁ r₂ : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r₁ ∧
      Aegis.CanBeEqual.can_be_equal arr target = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- If can_be_equal target arr returns true and can_be_equal arr other returns true, then can_be_equal target other returns true.
  Preconditions: target, arr, and other are slices of 64-bit integers with len(target) = len(arr) = len(other), 1 <= len(target) <= 1000, and every element of each slice is between 1 and 1000 inclusive. -/
theorem spec_4 (target arr other : Slice I64)
    (h_len₁ : target.val.length = arr.val.length)
    (h_len₂ : arr.val.length = other.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_other : inRange other) :
    Aegis.CanBeEqual.can_be_equal target arr = ok true →
    Aegis.CanBeEqual.can_be_equal arr other = ok true →
    Aegis.CanBeEqual.can_be_equal target other = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target arr other : Slice I64)
    (h_len₁ : target.val.length = arr.val.length)
    (h_len₂ : arr.val.length = other.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_other : inRange other), Aegis.CanBeEqual.can_be_equal target arr = ok true →
    Aegis.CanBeEqual.can_be_equal arr other = ok true →
    Aegis.CanBeEqual.can_be_equal target other = ok true) := by
  sorry

/-- The calls can_be_equal target arr and can_be_equal target arr2 both return results, and their Boolean results are equal.
  Preconditions: target, arr, and arr2 are slices of 64-bit integers with len(target) = len(arr) = len(arr2), 1 <= len(target) <= 1000, every element is between 1 and 1000 inclusive, and arr2 is obtained from arr by reversing one non-empty contiguous subarray. That is, there are integers l,u with 0 <= l <= u < len(arr) such that arr2[i] = arr[i] for i < l and for i > u, and arr2[i] = arr[l+u-i] for l <= i <= u. -/
theorem spec_5 (target arr arr2 : Slice I64)
    (h_len₁ : target.val.length = arr.val.length)
    (h_len₂ : arr.val.length = arr2.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_arr2 : inRange arr2)
    (h_rev : ∃ l u : ℕ, l ≤ u ∧ u < arr.val.length ∧
      arr2.val = reverseSegment arr.val l u) :
    ∃ r₁ r₂ : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r₁ ∧
      Aegis.CanBeEqual.can_be_equal target arr2 = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target arr arr2 : Slice I64)
    (h_len₁ : target.val.length = arr.val.length)
    (h_len₂ : arr.val.length = arr2.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_arr2 : inRange arr2)
    (h_rev : ∃ l u : ℕ, l ≤ u ∧ u < arr.val.length ∧
      arr2.val = reverseSegment arr.val l u), ∃ r₁ r₂ : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r₁ ∧
      Aegis.CanBeEqual.can_be_equal target arr2 = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- The function returns a result r, and r = true if and only if target[i] = arr[i] for every i with 0 <= i < len(target).
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, every element is between 1 and 1000 inclusive, and both slices are nondecreasing: target[i] <= target[i+1] and arr[i] <= arr[i+1] for every 0 <= i < len(target)-1. -/
theorem spec_6 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_sorted_target : nondecreasing target)
    (h_sorted_arr : nondecreasing arr) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ (i : ℕ) (_ : i < target.val.length),
        (target.val[i]'(by omega)).val = (arr.val[i]'(by omega)).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_sorted_target : nondecreasing target)
    (h_sorted_arr : nondecreasing arr), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ (i : ℕ) (_ : i < target.val.length),
        (target.val[i]'(by omega)).val = (arr.val[i]'(by omega)).val)) := by
  sorry

/-- The function returns a result r, and r = true if and only if arr[i] = c for every i with 0 <= i < len(arr).
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, every element is between 1 and 1000 inclusive, and there is an integer c such that target[i] = c for every 0 <= i < len(target). -/
theorem spec_7 (target arr : Slice I64) (c : ℤ)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_const : ∀ (i : ℕ) (_ : i < target.val.length), (target.val[i]'(by omega)).val = c) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ (i : ℕ) (_ : i < arr.val.length), (arr.val[i]'(by omega)).val = c) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target arr : Slice I64) (c : ℤ)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_const : ∀ (i : ℕ) (_ : i < target.val.length), (target.val[i]'(by omega)).val = c), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧
      (r = true ↔ ∀ (i : ℕ) (_ : i < arr.val.length), (arr.val[i]'(by omega)).val = c)) := by
  sorry

/-- The function returns a result r with r = true.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, every element is between 1 and 1000 inclusive, and for every i with 0 <= i < len(target), arr[i] = target[len(target)-1-i]. -/
theorem spec_8 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_rev : ∀ (i : ℕ) (_ : i < target.val.length),
      (arr.val[i]'(by omega)).val = (target.val[target.val.length - 1 - i]'(by omega)).val) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧ r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_rev : ∀ (i : ℕ) (_ : i < target.val.length),
      (arr.val[i]'(by omega)).val = (target.val[target.val.length - 1 - i]'(by omega)).val), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r with r = false.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, every element is between 1 and 1000 inclusive, and for every i with 0 <= i < len(target) and every j with 0 <= j < len(arr), target[i] != arr[j]. -/
theorem spec_9 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_disjoint : ∀ (i : ℕ) (_ : i < target.val.length) (j : ℕ) (_ : j < arr.val.length),
      (target.val[i]'(by omega)).val ≠ (arr.val[j]'(by omega)).val) :
    ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧ r = false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr)
    (h_disjoint : ∀ (i : ℕ) (_ : i < target.val.length) (j : ℕ) (_ : j < arr.val.length),
      (target.val[i]'(by omega)).val ≠ (arr.val[j]'(by omega)).val), ∃ r : Bool, Aegis.CanBeEqual.can_be_equal target arr = ok r ∧ r = false) := by
  sorry

/-- Whenever can_be_equal target arr returns a result r with r = true, there exist a natural number k and slices a_0,...,a_k of length len(arr) such that a_0 = arr, a_k = target, and for every t with 0 <= t < k, a_{t+1} is obtained from a_t by reversing one non-empty contiguous subarray of a_t.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, and every element of target and arr is an integer between 1 and 1000 inclusive. -/
theorem spec_10 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr) :
    Aegis.CanBeEqual.can_be_equal target arr = ok true →
    reachableByReversals arr target := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr), Aegis.CanBeEqual.can_be_equal target arr = ok true →
    reachableByReversals arr target) := by
  sorry

/-- Whenever can_be_equal target arr returns a result r with r = false, there do not exist a natural number k and slices a_0,...,a_k of length len(arr) such that a_0 = arr, a_k = target, and for every t with 0 <= t < k, a_{t+1} is obtained from a_t by reversing one non-empty contiguous subarray of a_t.
  Preconditions: target and arr are slices of 64-bit integers with len(target) = len(arr), 1 <= len(target) <= 1000, and every element of target and arr is an integer between 1 and 1000 inclusive. -/
theorem spec_11 (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr) :
    Aegis.CanBeEqual.can_be_equal target arr = ok false →
    ¬ reachableByReversals arr target := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (target arr : Slice I64)
    (h_len : target.val.length = arr.val.length)
    (h_lo : 1 ≤ target.val.length)
    (h_hi : target.val.length ≤ 1000)
    (h_target : inRange target)
    (h_arr : inRange arr), Aegis.CanBeEqual.can_be_equal target arr = ok false →
    ¬ reachableByReversals arr target) := by
  sorry

end AegisSpec.CanBeEqual
