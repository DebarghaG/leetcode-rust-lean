import Aegis.MaximumTotalSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumTotalSum.maximum_total_sum`

LeetCode problem `maximize-the-total-height-of-unique-towers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumTotalSum

namespace AegisSpec.MaximumTotalSum

set_option autoImplicit false

def entryList (a : Slice I64) : List ℤ := a.val.map (fun x => x.val)

def size (a : Slice I64) : ℕ := a.val.length

def tri (n : ℕ) : ℤ := ((n * (n - 1)) / 2 : ℕ)

def ValidInput (a : Slice I64) : Prop :=
  1 ≤ size a ∧ size a ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < size a), 1 ≤ (a.val.get ⟨i, hi⟩).val ∧ (a.val.get ⟨i, hi⟩).val ≤ 1000000000

def IsHeightAssignment (a : Slice I64) (h : List ℤ) : Prop :=
  h.length = size a ∧ h.Nodup ∧
    ∀ (i : ℕ) (hi : i < size a), 1 ≤ h.getD i 0 ∧ h.getD i 0 ≤ (a.val.get ⟨i, hi⟩).val

def HasHeightAssignment (a : Slice I64) : Prop := ∃ h : List ℤ, IsHeightAssignment a h

def achievableSums (a : Slice I64) : Set ℤ :=
  {S | ∃ h : List ℤ, IsHeightAssignment a h ∧ h.sum = S}

def IsSortedRearrangement (a : Slice I64) (arr : List ℤ) : Prop :=
  arr.Pairwise (fun x y => x ≤ y) ∧ List.Perm (entryList a) arr

def IsMaxEntry (a : Slice I64) (M : ℤ) : Prop :=
  (∀ (i : ℕ) (hi : i < size a), (a.val.get ⟨i, hi⟩).val ≤ M) ∧
    (∃ (i : ℕ) (hi : i < size a), (a.val.get ⟨i, hi⟩).val = M)

def PointwiseLE (a b : Slice I64) : Prop :=
  size a = size b ∧ ∀ p ∈ a.val.zip b.val, p.1.val ≤ p.2.val

/-- The function returns a result r. A height assignment is a sequence h of length n of integers such that, for every i with 0 <= i < n, 1 <= h[i] <= maximumHeight[i], and for every i, j with 0 <= i < j < n, h[i] != h[j]. If at least one height assignment exists, then r is the largest integer S for which some height assignment has total sum S = sum of h[i] over 0 <= i < n. If no height assignment exists, then r = -1.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_1 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) :
    ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧
        (HasHeightAssignment maximumHeight → IsGreatest (achievableSums maximumHeight) r.val) ∧
        (¬ HasHeightAssignment maximumHeight → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight), ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧
        (HasHeightAssignment maximumHeight → IsGreatest (achievableSums maximumHeight) r.val) ∧
        (¬ HasHeightAssignment maximumHeight → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_2 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) :
    ∃ r : I64, maximum_total_sum maximumHeight = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight), ∃ r : I64, maximum_total_sum maximumHeight = ok r) := by
  sorry

/-- Whenever the function returns a result r, let a be a nondecreasing rearrangement of maximumHeight, so a[0] <= a[1] <= ... <= a[n-1]. Then r = -1 if and only if there exists an index k with 0 <= k < n and a[k] < k+1. Equivalently, r != -1 if and only if a[k] >= k+1 for every k with 0 <= k < n.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_3 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (a : List ℤ)
    (ha : IsSortedRearrangement maximumHeight a) :
    (r.val = -1 ↔ ∃ (k : ℕ) (hk : k < a.length), a.get ⟨k, hk⟩ < (k : ℤ) + 1) ∧
      (r.val ≠ -1 ↔ ∀ (k : ℕ) (hk : k < a.length), (k : ℤ) + 1 ≤ a.get ⟨k, hk⟩) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (a : List ℤ)
    (ha : IsSortedRearrangement maximumHeight a), (r.val = -1 ↔ ∃ (k : ℕ) (hk : k < a.length), a.get ⟨k, hk⟩ < (k : ℤ) + 1) ∧
      (r.val ≠ -1 ↔ ∀ (k : ℕ) (hk : k < a.length), (k : ℤ) + 1 ≤ a.get ⟨k, hk⟩)) := by
  sorry

/-- Assume there is an integer C such that maximumHeight[i] = C for every i with 0 <= i < n. The function returns a result r, and: if C >= n then r = n*C - n*(n-1)/2; if C < n then r = -1.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_4 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (C : ℤ)
    (hconst : ∀ (i : ℕ) (hi : i < size maximumHeight),
      (maximumHeight.val.get ⟨i, hi⟩).val = C) :
    ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧
        ((size maximumHeight : ℤ) ≤ C →
          r.val = (size maximumHeight : ℤ) * C - tri (size maximumHeight)) ∧
        (C < (size maximumHeight : ℤ) → r.val = -1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (C : ℤ)
    (hconst : ∀ (i : ℕ) (hi : i < size maximumHeight),
      (maximumHeight.val.get ⟨i, hi⟩).val = C), ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧
        ((size maximumHeight : ℤ) ≤ C →
          r.val = (size maximumHeight : ℤ) * C - tri (size maximumHeight)) ∧
        (C < (size maximumHeight : ℤ) → r.val = -1)) := by
  sorry

/-- Assume the entries maximumHeight[0], ..., maximumHeight[n-1] are pairwise distinct, meaning maximumHeight[i] != maximumHeight[j] whenever i != j. Then the function returns a result r and r = sum of maximumHeight[i] over 0 <= i < n.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_5 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight)
    (hdistinct : ∀ (i j : ℕ) (hi : i < size maximumHeight) (hj : j < size maximumHeight),
      i ≠ j → (maximumHeight.val.get ⟨i, hi⟩).val ≠ (maximumHeight.val.get ⟨j, hj⟩).val) :
    ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧ r.val = (entryList maximumHeight).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight)
    (hdistinct : ∀ (i j : ℕ) (hi : i < size maximumHeight) (hj : j < size maximumHeight),
      i ≠ j → (maximumHeight.val.get ⟨i, hi⟩).val ≠ (maximumHeight.val.get ⟨j, hj⟩).val), ∃ r : I64,
      maximum_total_sum maximumHeight = ok r ∧ r.val = (entryList maximumHeight).sum) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every index k with 0 <= k < n, r >= maximumHeight[k] + n*(n-1)/2.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_6 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) :
    ∀ (k : ℕ) (hk : k < size maximumHeight),
      (maximumHeight.val.get ⟨k, hk⟩).val + tri (size maximumHeight) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1), ∀ (k : ℕ) (hk : k < size maximumHeight),
      (maximumHeight.val.get ⟨k, hk⟩).val + tri (size maximumHeight) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= the sum of maximumHeight[i] over 0 <= i < n.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_7 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) :
    r.val ≤ (entryList maximumHeight).sum := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1), r.val ≤ (entryList maximumHeight).sum) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= n*M - n*(n-1)/2, where M is the maximum value among maximumHeight[0], ..., maximumHeight[n-1].
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_8 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) (M : ℤ)
    (hM : IsMaxEntry maximumHeight M) :
    r.val ≤ (size maximumHeight : ℤ) * M - tri (size maximumHeight) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) (M : ℤ)
    (hM : IsMaxEntry maximumHeight M), r.val ≤ (size maximumHeight : ℤ) * M - tri (size maximumHeight)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a sequence h of length n such that 1 <= h[i] <= maximumHeight[i] for every 0 <= i < n, h[i] != h[j] for every i != j, and the sum of h[i] over 0 <= i < n is exactly r.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_9 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) :
    ∃ h : List ℤ, IsHeightAssignment maximumHeight h ∧ h.sum = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1), ∃ h : List ℤ, IsHeightAssignment maximumHeight h ∧ h.sum = r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every sequence h of length n such that 1 <= h[i] <= maximumHeight[i] for every 0 <= i < n and h[i] != h[j] for every i != j, the sum of h[i] over 0 <= i < n is at most r.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_10 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) (h : List ℤ)
    (hh : IsHeightAssignment maximumHeight h) :
    h.sum ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1) (h : List ℤ)
    (hh : IsHeightAssignment maximumHeight h), h.sum ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on maximumHeight, for every permutation pi of the indices {0,1,...,n-1}, the function on the array maximumHeight' defined by maximumHeight'[i] = maximumHeight[pi(i)] returns the same result r.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_11 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (maximumHeight' : Slice I64)
    (hperm : List.Perm maximumHeight'.val maximumHeight.val) :
    maximum_total_sum maximumHeight' = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (maximumHeight' : Slice I64)
    (hperm : List.Perm maximumHeight'.val maximumHeight.val), maximum_total_sum maximumHeight' = ok r) := by
  sorry

/-- Whenever the function returns a result r with r != -1 on maximumHeight, for every array maximumHeight' of length n that satisfies the same constraints and maximumHeight'[i] >= maximumHeight[i] for every 0 <= i < n, the function on maximumHeight' returns a result r' with r' != -1 and r' >= r.
  Preconditions: Let n = len(maximumHeight). n >= 1, n <= 100000, and for every i with 0 <= i < n, 1 <= maximumHeight[i] <= 1000000000. -/
theorem spec_12 (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1)
    (maximumHeight' : Slice I64) (hpre' : ValidInput maximumHeight')
    (hge : PointwiseLE maximumHeight maximumHeight') :
    ∃ r' : I64, maximum_total_sum maximumHeight' = ok r' ∧ r'.val ≠ -1 ∧ r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (maximumHeight : Slice I64) (hpre : ValidInput maximumHeight) (r : I64)
    (hr : maximum_total_sum maximumHeight = ok r) (hrne : r.val ≠ -1)
    (maximumHeight' : Slice I64) (hpre' : ValidInput maximumHeight')
    (hge : PointwiseLE maximumHeight maximumHeight'), ∃ r' : I64, maximum_total_sum maximumHeight' = ok r' ∧ r'.val ≠ -1 ∧ r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaximumTotalSum
