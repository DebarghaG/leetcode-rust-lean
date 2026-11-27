import Aegis.SortLinkedList.Code.Funs

/-!
# Specifications of `Aegis.SortLinkedList.sort_linked_list`

LeetCode problem `sort-linked-list-already-sorted-using-absolute-values`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

def Aegis.SortLinkedList.List.val : Aegis.SortLinkedList.List → _root_.List Int
  | Aegis.SortLinkedList.List.Nil => []
  | Aegis.SortLinkedList.List.Cons v next => _root_.List.cons v.val next.val

namespace AegisSpec.SortLinkedList

def Nondec (xs : List Int) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < xs.length),
    xs.get ⟨i, Nat.lt_of_succ_lt hi⟩ ≤ xs.get ⟨i + 1, hi⟩

def countVal (xs : List Int) (v : Int) : Nat := (xs.filter (fun x => x = v)).length

def countAbs (xs : List Int) (v : Int) : Nat := (xs.filter (fun x => |x| = v)).length

def negs (xs : List Int) : List Int := xs.filter (fun x => x < 0)

def nonnegs (xs : List Int) : List Int := xs.filter (fun x => 0 ≤ x)

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then ys is non-decreasing (for every i with 0 <= i < len(ys)-1, ys[i] <= ys[i+1]) and has the same multiset as xs (for every integer v, the number of indices i with 0 <= i < len(ys) and ys[i] = v equals the number of indices i with 0 <= i < len(xs) and xs[i] = v). Equivalently, ys is the unique non-decreasing rearrangement of xs.
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_1 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      Nondec r.val ∧ (∀ (v : Int), countVal r.val v = countVal head.val v) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      Nondec r.val ∧ (∀ (v : Int), countVal r.val v = countVal head.val v)) := by
  sorry

/-- For every input satisfying the preconditions, sort_linked_list head returns Result.ok r for some list r; it does not return a failure (no overflow, out-of-bounds, or panic).
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_2 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∃ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∃ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then len(ys) = len(xs).
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_3 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then for every i with 0 <= i < len(ys), -5000 <= ys[i] <= 5000.
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_4 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        -5000 ≤ r.val.get ⟨i, hi⟩ ∧ r.val.get ⟨i, hi⟩ ≤ 5000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        -5000 ≤ r.val.get ⟨i, hi⟩ ∧ r.val.get ⟨i, hi⟩ ≤ 5000) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then for every i with 0 <= i < len(ys)-1, ys[i] <= ys[i+1].
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_5 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      Nondec r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      Nondec r.val) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then for every integer v, the number of indices i with 0 <= i < len(ys) and ys[i] = v equals the number of indices i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_6 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), countVal r.val v = countVal head.val v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), countVal r.val v = countVal head.val v) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then len(ys) = len(xs), and ys[0] is a minimum of xs: for every i with 0 <= i < len(xs), xs[i] >= ys[0], and there exists i with 0 <= i < len(xs) and xs[i] = ys[0].
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_7 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length ∧
      ∀ (w : Int), r.val[0]? = some w →
        (∀ (i : Nat) (hi : i < head.val.length), w ≤ head.val.get ⟨i, hi⟩) ∧
        (∃ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ = w) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length ∧
      ∀ (w : Int), r.val[0]? = some w →
        (∀ (i : Nat) (hi : i < head.val.length), w ≤ head.val.get ⟨i, hi⟩) ∧
        (∃ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ = w)) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then len(ys) = len(xs), and ys[len(xs)-1] is a maximum of xs: for every i with 0 <= i < len(xs), xs[i] <= ys[len(xs)-1], and there exists i with 0 <= i < len(xs) and xs[i] = ys[len(xs)-1].
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_8 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length ∧
      ∀ (w : Int), r.val[head.val.length - 1]? = some w →
        (∀ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ ≤ w) ∧
        (∃ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ = w) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      r.val.length = head.val.length ∧
      ∀ (w : Int), r.val[head.val.length - 1]? = some w →
        (∀ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ ≤ w) ∧
        (∃ (i : Nat) (hi : i < head.val.length), head.val.get ⟨i, hi⟩ = w)) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Define neg(xs) to be the sequence of those xs[i] with xs[i] < 0, taken in increasing index order, and define neg(ys) similarly from ys. Then neg(ys) is the reverse of neg(xs): len(neg(ys)) = len(neg(xs)) and for every k with 0 <= k < len(neg(xs)), neg(ys)[k] = neg(xs)[len(neg(xs))-1-k].
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_9 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      negs r.val = (negs head.val).reverse := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      negs r.val = (negs head.val).reverse) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Define nonneg(xs) to be the sequence of those xs[i] with xs[i] >= 0, taken in increasing index order, and define nonneg(ys) similarly from ys. Then nonneg(ys) = nonneg(xs): len(nonneg(ys)) = len(nonneg(xs)) and for every k with 0 <= k < len(nonneg(xs)), nonneg(ys)[k] = nonneg(xs)[k].
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_10 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      nonnegs r.val = nonnegs head.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      nonnegs r.val = nonnegs head.val) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then for every integer v with v >= 0, the number of indices i with 0 <= i < len(ys) and |ys[i]| = v equals the number of indices i with 0 <= i < len(xs) and |xs[i]| = v.
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_11 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), 0 ≤ v → countAbs r.val v = countAbs head.val v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), 0 ≤ v → countAbs r.val v = countAbs head.val v) := by
  sorry

/-- Whenever sort_linked_list head returns Result.ok r, let ys be the sequence of values of the nodes of r from front to back. Then for every integer v, there exists an index i with 0 <= i < len(ys) and ys[i] = v if and only if there exists an index i with 0 <= i < len(xs) and xs[i] = v.
  Preconditions: Let xs be the sequence of values of the nodes of head from front to back. The preconditions are: 1 <= len(xs) <= 100000; for every i with 0 <= i < len(xs), -5000 <= xs[i] <= 5000; and for every i, j with 0 <= i < j < len(xs), |xs[i]| <= |xs[j]|, where |v| is the usual absolute value (v if v >= 0, -v otherwise). -/
theorem spec_12 (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|) :
    ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), v ∈ r.val ↔ v ∈ head.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.SortLinkedList.List)
    (h_len_pos : 1 ≤ head.val.length) (h_len_le : head.val.length ≤ 100000)
    (h_bounded : ∀ (i : Nat) (hi : i < head.val.length),
      -5000 ≤ head.val.get ⟨i, hi⟩ ∧ head.val.get ⟨i, hi⟩ ≤ 5000)
    (h_abs_mono : ∀ (i j : Nat) (hi : i < head.val.length) (hj : j < head.val.length),
      i < j → |head.val.get ⟨i, hi⟩| ≤ |head.val.get ⟨j, hj⟩|), ∀ (r : Aegis.SortLinkedList.List), Aegis.SortLinkedList.sort_linked_list head = ok r →
      ∀ (v : Int), v ∈ r.val ↔ v ∈ head.val) := by
  sorry

end AegisSpec.SortLinkedList
