import Aegis.DeleteDuplicatesUnsorted.Code.Funs

/-!
# Specifications of `Aegis.DeleteDuplicatesUnsorted.delete_duplicates_unsorted`

LeetCode problem `remove-duplicates-from-an-unsorted-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DeleteDuplicatesUnsorted (delete_duplicates_unsorted)

namespace AegisSpec.DeleteDuplicatesUnsorted

def values : Aegis.DeleteDuplicatesUnsorted.List → List ℤ
  | .Nil => []
  | .Cons v next => v.val :: values next

def cnt (xs : List ℤ) (v : ℤ) : ℕ := (xs.filter (fun x => x = v)).length

def SubseqOf (ys xs : List ℤ) : Prop :=
  ∃ idx : ℕ → ℕ,
    (∀ j, j + 1 < ys.length → idx j < idx (j + 1)) ∧
      (∀ j, j < ys.length → idx j < xs.length ∧ xs[idx j]? = ys[j]?)

def keepSingletons (xs : List ℤ) : List ℤ := xs.filter (fun x => cnt xs x = 1)

def nDistinct (xs : List ℤ) : ℕ := xs.toFinset.card

def nSingletonValues (xs : List ℤ) : ℕ := nDistinct (keepSingletons xs)

/-- The function returns a successful result r. Let ys be the sequence of values in r, and let cnt(xs, v) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. Then ys is exactly the subsequence of xs obtained by keeping every position i for which cnt(xs, xs[i]) = 1 and deleting every position i for which cnt(xs, xs[i]) >= 2, with all kept positions remaining in their original relative order. Equivalently, for every value v, cnt(ys, v) = 1 if cnt(xs, v) = 1, and cnt(ys, v) = 0 otherwise, and ys is a subsequence of xs in the order inherited from xs.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in the constraint range: for every i with 0 <= i < len(xs), 1 <= xs[i] <= 100000. -/
theorem spec_1 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, delete_duplicates_unsorted head = ok r ∧
      (∀ v, cnt (values r) v = if cnt (values head) v = 1 then 1 else 0) ∧
      SubseqOf (values r) (values head) ∧
      values r = keepSingletons (values head) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∃ r, delete_duplicates_unsorted head = ok r ∧
      (∀ v, cnt (values r) v = if cnt (values head) v = 1 then 1 else 0) ∧
      SubseqOf (values r) (values head) ∧
      values r = keepSingletons (values head)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a successful result r rather than failing: no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_2 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, delete_duplicates_unsorted head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∃ r, delete_duplicates_unsorted head = ok r) := by
  sorry

/-- Whenever the function returns a result r, every value v occurring in the sequence of values of r satisfies 1 <= v <= 100000.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_3 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, v ∈ values r → 1 ≤ v ∧ v ≤ 100000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, v ∈ values r → 1 ≤ v ∧ v ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r, len(values(r)) <= len(xs).
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_4 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      (values r).length ≤ (values head).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      (values r).length ≤ (values head).length) := by
  sorry

/-- Whenever the function returns a result r, len(values(r)) equals the number of distinct values v such that cnt(xs, v) = 1, where cnt(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_5 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      (values r).length = nSingletonValues (values head) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      (values r).length = nSingletonValues (values head)) := by
  sorry

/-- Whenever the function returns a result r, for every value v, v occurs in the sequence values(r) if and only if cnt(xs, v) = 1, where cnt(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_6 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, v ∈ values r ↔ cnt (values head) v = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, v ∈ values r ↔ cnt (values head) v = 1) := by
  sorry

/-- Whenever the function returns a result r, for every value v, cnt(values(r), v) = 1 if cnt(xs, v) = 1, and cnt(values(r), v) = 0 otherwise, where cnt(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_7 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, cnt (values r) v = if cnt (values head) v = 1 then 1 else 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, cnt (values r) v = if cnt (values head) v = 1 then 1 else 0) := by
  sorry

/-- Whenever the function returns a result r, the values in r are pairwise distinct: for all indices i and j with 0 <= i < j < len(values(r)), values(r)[i] != values(r)[j].
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_8 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ (i j : ℕ) (hi : i < (values r).length) (hj : j < (values r).length),
        i < j → (values r).get ⟨i, hi⟩ ≠ (values r).get ⟨j, hj⟩ := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ (i j : ℕ) (hi : i < (values r).length) (hj : j < (values r).length),
        i < j → (values r).get ⟨i, hi⟩ ≠ (values r).get ⟨j, hj⟩) := by
  sorry

/-- Whenever the function returns a result r, values(r) is a subsequence of xs: letting k = len(values(r)), there exists a strictly increasing sequence (i_j)_{0 <= j < k} of natural numbers such that for every j with 0 <= j < k, i_j < len(xs) and xs[i_j] = values(r)[j]. When k = 0, this sequence is empty and the condition is vacuous.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_9 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      SubseqOf (values r) (values head) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      SubseqOf (values r) (values head)) := by
  sorry

/-- Whenever the function returns a result r, for every value v with cnt(xs, v) >= 2, v does not occur in values(r), where cnt(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_10 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, 2 ≤ cnt (values head) v → v ∉ values r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, 2 ≤ cnt (values head) v → v ∉ values r) := by
  sorry

/-- Whenever the function returns a result r, for every value v with cnt(xs, v) = 1, there exists an index j with 0 <= j < len(values(r)) such that values(r)[j] = v, where cnt(xs, v) is the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_11 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, cnt (values head) v = 1 →
        ∃ (j : ℕ) (hj : j < (values r).length), (values r).get ⟨j, hj⟩ = v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ∀ v, cnt (values head) v = 1 →
        ∃ (j : ℕ) (hj : j < (values r).length), (values r).get ⟨j, hj⟩ = v) := by
  sorry

/-- The function returns a successful result r whose value sequence equals xs; that is, values(r) = xs and len(values(r)) = len(xs).
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). Additionally, all input values are distinct: for all i and j with 0 <= i < j < len(xs), xs[i] != xs[j]. -/
theorem spec_12 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (hnd : (values head).Nodup) :
    ∃ r, delete_duplicates_unsorted head = ok r ∧
      values r = values head ∧ (values r).length = (values head).length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (hnd : (values head).Nodup), ∃ r, delete_duplicates_unsorted head = ok r ∧
      values r = values head ∧ (values r).length = (values head).length) := by
  sorry

/-- The function returns a successful result r with values(r) = [] (the empty list, r = Nil).
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). Additionally, no present value occurs exactly once: for every value v, cnt(xs, v) != 1. -/
theorem spec_13 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (hsingle : ∀ v, cnt (values head) v ≠ 1) :
    ∃ r, delete_duplicates_unsorted head = ok r ∧ values r = [] := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (hsingle : ∀ v, cnt (values head) v ≠ 1), ∃ r, delete_duplicates_unsorted head = ok r ∧ values r = []) := by
  sorry

/-- The function returns a successful result r with values(r) = [xs[0]], that is, r = Cons(xs[0], Nil).
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). Additionally, len(xs) = 1. -/
theorem spec_14 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (h1 : (values head).length = 1) :
    ∃ r, delete_duplicates_unsorted head = ok r ∧
      values r = [(values head).get ⟨0, by omega⟩] := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000)
    (h1 : (values head).length = 1), ∃ r, delete_duplicates_unsorted head = ok r ∧
      values r = [(values head).get ⟨0, by omega⟩]) := by
  sorry

/-- Whenever the function returns a nonempty result r, applying delete_duplicates_unsorted to r returns a successful result r' with values(r') = values(r).
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_15 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r → values r ≠ [] →
      ∃ r', delete_duplicates_unsorted r = ok r' ∧ values r' = values r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r → values r ≠ [] →
      ∃ r', delete_duplicates_unsorted r = ok r' ∧ values r' = values r) := by
  sorry

/-- Whenever the function returns a result r: if there exists an index i with 0 <= i < len(xs) and cnt(xs, xs[i]) = 1, and i0 is the least such index, then values(r) is nonempty and values(r)[0] = xs[i0]; if no such index exists, then values(r) = [].
  Preconditions: Let xs be the sequence of values in head from front to back. The list is finite and nonempty: 1 <= len(xs) <= 100000. Every node value lies in 1 <= xs[i] <= 100000 for all 0 <= i < len(xs). -/
theorem spec_16 (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, delete_duplicates_unsorted head = ok r →
      ((∀ (i0 : ℕ) (hi0 : i0 < (values head).length),
          cnt (values head) ((values head).get ⟨i0, hi0⟩) = 1 →
          (∀ (j : ℕ) (hj : j < (values head).length), j < i0 →
            cnt (values head) ((values head).get ⟨j, hj⟩) ≠ 1) →
          (values r).head? = some ((values head).get ⟨i0, hi0⟩)) ∧
        ((∀ (i : ℕ) (hi : i < (values head).length),
            cnt (values head) ((values head).get ⟨i, hi⟩) ≠ 1) → values r = [])) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (head : Aegis.DeleteDuplicatesUnsorted.List)
    (hne : 1 ≤ (values head).length) (hlen : (values head).length ≤ 100000)
    (hbound : ∀ v, v ∈ values head → 1 ≤ v ∧ v ≤ 100000), ∀ r, delete_duplicates_unsorted head = ok r →
      ((∀ (i0 : ℕ) (hi0 : i0 < (values head).length),
          cnt (values head) ((values head).get ⟨i0, hi0⟩) = 1 →
          (∀ (j : ℕ) (hj : j < (values head).length), j < i0 →
            cnt (values head) ((values head).get ⟨j, hj⟩) ≠ 1) →
          (values r).head? = some ((values head).get ⟨i0, hi0⟩)) ∧
        ((∀ (i : ℕ) (hi : i < (values head).length),
            cnt (values head) ((values head).get ⟨i, hi⟩) ≠ 1) → values r = []))) := by
  sorry

end AegisSpec.DeleteDuplicatesUnsorted
