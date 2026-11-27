import Aegis.SortList.Code.Funs

/-!
# Specifications of `Aegis.SortList.sort_list`

LeetCode problem `sort-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortList

def vals : Aegis.SortList.List → List Int
  | .Nil => []
  | .Cons v next => v.val :: vals next

def len (l : Aegis.SortList.List) : Nat := (vals l).length

def get (l : Aegis.SortList.List) (i : Nat) : Int := (vals l).getD i 0

def count (l : Aegis.SortList.List) (v : Int) : Nat := (vals l).countP (fun w => w == v)

def NonDecr (l : Aegis.SortList.List) : Prop :=
  ∀ i, i + 1 < len l → get l i ≤ get l (i + 1)

def NonIncr (l : Aegis.SortList.List) : Prop :=
  ∀ i, i + 1 < len l → get l (i + 1) ≤ get l i

def StrictIncr (l : Aegis.SortList.List) : Prop :=
  ∀ i j, i < j → j < len l → get l i < get l j

def Bounds (l : Aegis.SortList.List) : Prop :=
  ∀ i, i < len l → -100000 ≤ get l i ∧ get l i ≤ 100000

def IsMaxVal (l : Aegis.SortList.List) (m : Int) : Prop :=
  (∀ i, i < len l → get l i ≤ m) ∧ ∃ j, j < len l ∧ get l j = m

/-- The function returns a result r (a linked list) such that: (1) len(r) = len(head); (2) for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(head) and head[i] = v; (3) for every index i with 0 <= i < len(r)-1, r[i] <= r[i+1]. Here len(L) is the number of nodes in L and L[i] is the value of the i-th node (0-indexed).
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_1 (head : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head) :
    ∃ r, Aegis.SortList.sort_list head = ok r ∧
      len r = len head ∧
      (∀ v : Int, count r v = count head v) ∧
      NonDecr r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head), ∃ r, Aegis.SortList.sort_list head = ok r ∧
      len r = len head ∧
      (∀ v : Int, count r v = count head v) ∧
      NonDecr r) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, or out-of-bounds) on any input satisfying the preconditions.
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_2 (head : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head) :
    ∃ r, Aegis.SortList.sort_list head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head), ∃ r, Aegis.SortList.sort_list head = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head), where len(L) is the number of nodes in L.
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_3 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(head) and head[i] = v. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_4 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    ∀ v : Int, count r v = count head v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r), ∀ v : Int, count r v = count head v) := by
  sorry

/-- Whenever the function returns a result r, r is sorted in non-decreasing order: for every index i with 0 <= i < len(r)-1, r[i] <= r[i+1]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_5 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    NonDecr r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r), NonDecr r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head) and for every index i with 0 <= i < len(head), r[i] = head[i]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and for every i with 0 <= i < len(head)-1, head[i] <= head[i+1]. -/
theorem spec_6 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hsorted : NonDecr head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head ∧ ∀ i, i < len head → get r i = get head i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hsorted : NonDecr head)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head ∧ ∀ i, i < len head → get r i = get head i) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), -100000 <= r[i] <= 100000. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000 and for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000. -/
theorem spec_7 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    Bounds r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hres : Aegis.SortList.sort_list head = ok r), Bounds r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head), and there exists an index j with 0 <= j < len(head) such that r[0] = head[j] and for every index i with 0 <= i < len(head), head[i] >= head[j]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and len(head) > 0. -/
theorem spec_8 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hpos : 0 < len head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head ∧
      ∃ j, j < len head ∧ get r 0 = get head j ∧
        ∀ i, i < len head → get head i ≥ get head j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hpos : 0 < len head)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head ∧
      ∃ j, j < len head ∧ get r 0 = get head j ∧
        ∀ i, i < len head → get head i ≥ get head j) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head) and r[len(r)-1] = max{ head[i] | 0 <= i < len(head) }. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and len(head) > 0. -/
theorem spec_9 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hpos : 0 < len head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head ∧ ∃ m : Int, IsMaxVal head m ∧ get r (len r - 1) = m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hpos : 0 < len head)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head ∧ ∃ m : Int, IsMaxVal head m ∧ get r (len r - 1) = m) := by
  sorry

/-- Whenever the function returns a result r, r is strictly increasing: for every i and j with 0 <= i < j < len(r), r[i] < r[j]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and for every i and j with 0 <= i < j < len(head), head[i] != head[j]. -/
theorem spec_10 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hdistinct : ∀ i j, i < j → j < len head → get head i ≠ get head j)
    (hres : Aegis.SortList.sort_list head = ok r) :
    StrictIncr r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hdistinct : ∀ i j, i < j → j < len head → get head i ≠ get head j)
    (hres : Aegis.SortList.sort_list head = ok r), StrictIncr r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head) and for every index i with 0 <= i < len(head), r[i] = head[len(head)-1-i]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and for every i with 0 <= i < len(head)-1, head[i] >= head[i+1]. -/
theorem spec_11 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hrevsorted : NonIncr head)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head ∧ ∀ i, i < len head → get r i = get head (len head - 1 - i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (hrevsorted : NonIncr head)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head ∧ ∀ i, i < len head → get r i = get head (len head - 1 - i)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head) and r[0] < r[len(r)-1]. Here len(L) is the number of nodes in L and L[i] is the value at 0-based index i.
  Preconditions: 0 <= len(head) <= 50000, for every i with 0 <= i < len(head), -100000 <= head[i] <= 100000, and there exist i and j with 0 <= i < len(head), 0 <= j < len(head), and head[i] != head[j]. -/
theorem spec_12 (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (i j : Nat) (hi : i < len head) (hj : j < len head) (hne : get head i ≠ get head j)
    (hres : Aegis.SortList.sort_list head = ok r) :
    len r = len head ∧ get r 0 < get r (len r - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.SortList.List) (r : Aegis.SortList.List)
    (hlen : len head ≤ 50000)
    (hval : Bounds head)
    (i j : Nat) (hi : i < len head) (hj : j < len head) (hne : get head i ≠ get head j)
    (hres : Aegis.SortList.sort_list head = ok r), len r = len head ∧ get r 0 < get r (len r - 1)) := by
  sorry

end AegisSpec.SortList
