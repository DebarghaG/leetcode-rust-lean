import Aegis.MaximumElementAfterDecrementingAndRearranging.Code.Funs

/-!
# Specifications of `Aegis.MaximumElementAfterDecrementingAndRearranging.maximum_element_after_decrementing_and_rearranging`

LeetCode problem `maximum-element-after-decreasing-and-rearranging`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumElementAfterDecrementingAndRearranging

open Aegis.MaximumElementAfterDecrementingAndRearranging

def listMax (l : List Int) : Int := l.foldr max 0

def arrMax (arr : List I64) : Int := listMax (arr.map fun x => x.val)

def StepAtMostOne : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: t => (y - x).natAbs ≤ 1 ∧ StepAtMostOne (y :: t)

def ArrStepAtMostOne : List I64 → Prop
  | [] => True
  | [_] => True
  | x :: y :: t => (y.val - x.val).natAbs ≤ 1 ∧ ArrStepAtMostOne (y :: t)

def IsFeasibleFinalArray (arr : List I64) (b : List Int) : Prop :=
  ∃ s : List I64,
    s.Perm arr ∧
      List.Forall₂ (fun (x : Int) (y : I64) => 1 ≤ x ∧ x ≤ y.val) b s ∧
      b.head? = some 1 ∧
      StepAtMostOne b

def IsSortedRearrangement (arr s : List I64) : Prop :=
  s.Perm arr ∧ s.Pairwise (fun x y => x.val ≤ y.val)

def greedyStep (g : Int) (x : I64) : Int := min x.val (g + 1)

def greedyChainAux : List I64 → Int → List Int
  | [], _ => []
  | x :: t, g => greedyStep g x :: greedyChainAux t (greedyStep g x)

def greedyChain (s : List I64) : List Int :=
  match s with
  | [] => []
  | _ :: t => 1 :: greedyChainAux t 1

/-- Let n = len(arr). Call an integer sequence b (i.e., b[0],...,b[n-1] are integers) of length n an arr-feasible final array if there is a permutation p of the index set {0,...,n-1} such that: (i) for every i with 0 <= i < n, 1 <= b[i] <= arr[p(i)]; (ii) b[0] = 1; and (iii) for every i with 1 <= i < n, |b[i] - b[i-1]| <= 1. The function returns Ok r, and r is the maximum of max_{0 <= j < n} b[j] over all arr-feasible final arrays b. Equivalently, r is the largest value that can occur in an integer array obtained from arr by any allowed sequence of rearrangements and decreases while satisfying the two required conditions.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_1 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r : I64,
      maximum_element_after_decrementing_and_rearranging arr = ok r ∧
        (∀ b : List Int, IsFeasibleFinalArray arr.val b → listMax b ≤ r.val) ∧
        (∃ b : List Int, IsFeasibleFinalArray arr.val b ∧ listMax b = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : I64,
      maximum_element_after_decrementing_and_rearranging arr = ok r ∧
        (∀ b : List Int, IsFeasibleFinalArray arr.val b → listMax b ≤ r.val) ∧
        (∃ b : List Int, IsFeasibleFinalArray arr.val b ∧ listMax b = r.val)) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, panic, or access out of bounds) for every input satisfying the preconditions.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_2 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(arr).
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_3 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      1 ≤ r.val ∧ r.val ≤ (arr.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      1 ≤ r.val ∧ r.val ≤ (arr.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= max_{0 <= i < len(arr)} arr[i].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_4 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      r.val ≤ arrMax arr.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      r.val ≤ arrMax arr.val) := by
  sorry

/-- Whenever the function returns Ok r, there exists an integer sequence b of length n = len(arr) for which there is a permutation p of {0,...,n-1} with 1 <= b[i] <= arr[p(i)] for every i, b[0] = 1, and |b[i] - b[i-1]| <= 1 for every 1 <= i < n, such that max_{0 <= i < n} b[i] = r.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_5 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∃ b : List Int, IsFeasibleFinalArray arr.val b ∧ listMax b = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∃ b : List Int, IsFeasibleFinalArray arr.val b ∧ listMax b = r.val) := by
  sorry

/-- Whenever the function returns Ok r, for every integer sequence b of length n = len(arr) for which there is a permutation p of {0,...,n-1} with 1 <= b[i] <= arr[p(i)] for every i, b[0] = 1, and |b[i] - b[i-1]| <= 1 for every 1 <= i < n, we have max_{0 <= i < n} b[i] <= r.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_6 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ b : List Int, IsFeasibleFinalArray arr.val b → listMax b ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ b : List Int, IsFeasibleFinalArray arr.val b → listMax b ≤ r.val) := by
  sorry

/-- Whenever the function returns Ok r, there exists an integer sequence b of length n = len(arr) for which there is a permutation p of {0,...,n-1} with 1 <= b[i] <= arr[p(i)] for every i, b[0] = 1, and |b[i] - b[i-1]| <= 1 for every 1 <= i < n, such that max_{0 <= i < n} b[i] = r and b is nondecreasing, i.e. b[0] <= b[1] <= ... <= b[n-1].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_7 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∃ b : List Int,
        IsFeasibleFinalArray arr.val b ∧ listMax b = r.val ∧
          b.Pairwise (fun x y => x ≤ y) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∃ b : List Int,
        IsFeasibleFinalArray arr.val b ∧ listMax b = r.val ∧
          b.Pairwise (fun x y => x ≤ y)) := by
  sorry

/-- If len(arr) = 2, then whenever the function returns a result r, r = 2 if max_{0 <= i < 2} arr[i] >= 2, and r = 1 otherwise.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_8 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen : arr.val.length = 2) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      (2 ≤ arrMax arr.val → r.val = 2) ∧ (arrMax arr.val < 2 → r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen : arr.val.length = 2), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      (2 ≤ arrMax arr.val → r.val = 2) ∧ (arrMax arr.val < 2 → r.val = 1)) := by
  sorry

/-- If arr[0] = 1 and for every i with 1 <= i < len(arr) we have |arr[i] - arr[i-1]| <= 1, then whenever the function returns a result r, r = max_{0 <= i < len(arr)} arr[i].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_9 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hstart : ∀ (h : 0 < arr.val.length), (arr.val.get ⟨0, h⟩).val = 1)
    (hstep : ArrStepAtMostOne arr.val) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      r.val = arrMax arr.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
    (hstart : ∀ (h : 0 < arr.val.length), (arr.val.get ⟨0, h⟩).val = 1)
    (hstep : ArrStepAtMostOne arr.val), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      r.val = arrMax arr.val) := by
  sorry

/-- Whenever the function returns Ok r, for every slice arr2 that is a permutation of arr (same length and multiset of entries), r equals the maximum, over all integer sequences c of length n for which there is a permutation q of {0,...,n-1} with 1 <= c[i] <= arr2[q(i)] for all i, c[0] = 1, and |c[i] - c[i-1]| <= 1 for all 1 <= i < n, of max_{0 <= i < n} c[i].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_10 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ arr2 : Slice I64, arr2.val.Perm arr.val →
        (∀ c : List Int, IsFeasibleFinalArray arr2.val c → listMax c ≤ r.val) ∧
          (∃ c : List Int, IsFeasibleFinalArray arr2.val c ∧ listMax c = r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ arr2 : Slice I64, arr2.val.Perm arr.val →
        (∀ c : List Int, IsFeasibleFinalArray arr2.val c → listMax c ≤ r.val) ∧
          (∃ c : List Int, IsFeasibleFinalArray arr2.val c ∧ listMax c = r.val)) := by
  sorry

/-- Whenever the function returns Ok r for arr, for every slice arr2 of length len(arr) with 1 <= arr2[i] <= 1000000000 and arr[i] <= arr2[i] for every i, r is at most the maximum, over all integer sequences c of length n for which there is a permutation q of {0,...,n-1} with 1 <= c[i] <= arr2[q(i)] for all i, c[0] = 1, and |c[i] - c[i-1]| <= 1 for all 1 <= i < n, of max_{0 <= i < n} c[i].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_11 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ arr2 : Slice I64,
        arr2.val.length = arr.val.length →
          (∀ x ∈ arr2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) →
            List.Forall₂ (fun (x y : I64) => x.val ≤ y.val) arr.val arr2.val →
              ∃ c : List Int, IsFeasibleFinalArray arr2.val c ∧ r.val ≤ listMax c := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ arr2 : Slice I64,
        arr2.val.length = arr.val.length →
          (∀ x ∈ arr2.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) →
            List.Forall₂ (fun (x y : I64) => x.val ≤ y.val) arr.val arr2.val →
              ∃ c : List Int, IsFeasibleFinalArray arr2.val c ∧ r.val ≤ listMax c) := by
  sorry

/-- Let n = len(arr), and let s be the nondecreasing rearrangement of arr, so s[0] <= s[1] <= ... <= s[n-1] and s is a permutation of arr. Whenever the function returns a result r, r = n if and only if s[i] >= i+1 for every i with 0 <= i < n.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_12 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ s : List I64, IsSortedRearrangement arr.val s →
        (r.val = (arr.val.length : Int) ↔
          ∀ (i : Nat) (hi : i < s.length), (i : Int) + 1 ≤ (s.get ⟨i, hi⟩).val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ s : List I64, IsSortedRearrangement arr.val s →
        (r.val = (arr.val.length : Int) ↔
          ∀ (i : Nat) (hi : i < s.length), (i : Int) + 1 ≤ (s.get ⟨i, hi⟩).val)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if len(arr) = 1 or every entry of arr is 1.
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_13 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      (r.val = 1 ↔ arr.val.length = 1 ∨ ∀ x ∈ arr.val, x.val = 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      (r.val = 1 ↔ arr.val.length = 1 ∨ ∀ x ∈ arr.val, x.val = 1)) := by
  sorry

/-- Let s be the nondecreasing rearrangement of arr, so s[0] <= ... <= s[n-1] and s is a permutation of arr. Define g[0] = 1 and, for 1 <= i < n, g[i] = min(s[i], g[i-1] + 1). Whenever the function returns a result r, r = g[n-1].
  Preconditions: Let n = len(arr). The input satisfies the problem constraints: 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= arr[i] <= 1000000000. -/
theorem spec_14 (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
    ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ s : List I64, IsSortedRearrangement arr.val s → (greedyChain s).getLast? = some r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen1 : 1 ≤ arr.val.length) (hlen2 : arr.val.length ≤ 100000)
    (hbound : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r : I64, maximum_element_after_decrementing_and_rearranging arr = ok r →
      ∀ s : List I64, IsSortedRearrangement arr.val s → (greedyChain s).getLast? = some r.val) := by
  sorry

end AegisSpec.MaximumElementAfterDecrementingAndRearranging
