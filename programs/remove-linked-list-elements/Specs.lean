import Aegis.RemoveElements.Code.Funs

/-!
# Specifications of `Aegis.RemoveElements.remove_elements`

LeetCode problem `remove-linked-list-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveElements

open Aegis.RemoveElements

def elems : List → _root_.List ℤ
  | List.Nil => []
  | List.Cons v rest => v.val :: elems rest

def len (l : List) : ℕ := (elems l).length

def count (x : ℤ) (l : List) : ℕ := ((elems l).filter (fun y => decide (y = x))).length

def removeVal (x : ℤ) (l : List) : _root_.List ℤ :=
  (elems l).filter (fun y => decide (y ≠ x))

lemma removeVal_eq (x : ℤ) (l : List) :
    removeVal x l = (elems l).filter (fun y => decide (y ≠ x)) := rfl

/-- The function returns a result r and the sequence of values in r equals the sequence of values in head with every occurrence of val removed, preserving order. Formally, let elems(l) be the sequence of values stored in the linked list l from head to tail (elems(Nil) = [], elems(Cons(v, rest)) = v :: elems(rest)). Then elems(r) = filter (fun x => x != val) elems(head).
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_1 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50) :
    ∃ r : List, Aegis.RemoveElements.remove_elements head val = ok r ∧
      elems r = removeVal val.val head := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50), ∃ r : List, Aegis.RemoveElements.remove_elements head val = ok r ∧
      elems r = removeVal val.val head) := by
  sorry

/-- For every head and val satisfying the preconditions, the function returns a result r (it does not fail).
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_2 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50) :
    ∃ r : List, Aegis.RemoveElements.remove_elements head val = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50), ∃ r : List, Aegis.RemoveElements.remove_elements head val = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(head) - count(val, head), where len(l) is the number of nodes in l (equivalently, the length of elems(l)) and count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_3 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    len r = len head - count val.val head := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), len r = len head - count val.val head) := by
  sorry

/-- Whenever the function returns a result r, every value stored in r is not equal to val. Equivalently, count(val, r) = 0, where count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_4 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    (∀ x ∈ elems r, x ≠ val.val) ∧ count val.val r = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), (∀ x ∈ elems r, x ≠ val.val) ∧ count val.val r = 0) := by
  sorry

/-- Whenever the function returns a result r, elems(r) is a subsequence of elems(head): there exists a strictly increasing function f from the set of indices {0, ..., len(r)-1} to the set of indices {0, ..., len(head)-1} such that for every i, elems(r)[i] = elems(head)[f(i)]. Here elems(l) is the sequence of values stored in l from head to tail (elems(Nil) = [], elems(Cons(v, rest)) = v :: elems(rest)), and len(l) is the number of nodes in l.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_5 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    ∃ f : Fin (len r) → Fin (len head),
      (∀ i j : Fin (len r), i < j → f i < f j) ∧
      (∀ i : Fin (len r),
        (elems r).get ⟨i.1, i.2⟩ = (elems head).get ⟨(f i).1, (f i).2⟩) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), ∃ f : Fin (len r) → Fin (len head),
      (∀ i j : Fin (len r), i < j → f i < f j) ∧
      (∀ i : Fin (len r),
        (elems r).get ⟨i.1, i.2⟩ = (elems head).get ⟨(f i).1, (f i).2⟩)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v with v != val, count(v, r) = count(v, head), where count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_6 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    ∀ v : ℤ, v ≠ val.val → count v r = count v head := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), ∀ v : ℤ, v ≠ val.val → count v r = count v head) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, count(v, r) = if v = val then 0 else count(v, head), where count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_7 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    ∀ v : ℤ, count v r = if v = val.val then 0 else count v head := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), ∀ v : ℤ, count v r = if v = val.val then 0 else count v head) := by
  sorry

/-- If head = Nil, then whenever the function returns a result r, r = Nil (equivalently, elems(r) = [], where elems(l) is the sequence of values stored in l from head to tail).
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_8 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hhead : head = List.Nil)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    r = List.Nil ∧ elems r = [] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hhead : head = List.Nil)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), r = List.Nil ∧ elems r = []) := by
  sorry

/-- If count(val, head) = 0, then whenever the function returns a result r, elems(r) = elems(head), where elems(l) is the sequence of values stored in l from head to tail and count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_9 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hno : count val.val head = 0)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    elems r = elems head := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hno : count val.val head = 0)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), elems r = elems head) := by
  sorry

/-- If every node in head has stored value equal to val (i.e., count(val, head) = len(head)), then whenever the function returns a result r, r = Nil (equivalently, elems(r) = []), where len(l) is the number of nodes in l, count(v, l) is the number of nodes in l whose stored value equals v, and elems(l) is the sequence of values stored in l from head to tail.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_10 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hall : count val.val head = len head)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    r = List.Nil ∧ elems r = [] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (hall : count val.val head = len head)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), r = List.Nil ∧ elems r = []) := by
  sorry

/-- Whenever the function returns a result r, if head is not Nil and there is at least one node in head whose value is not equal to val, then the first node of r (i.e., r's head) has value equal to the value of the first node in head whose value is not equal to val. If no such node exists in head (i.e., count(val, head) = len(head)), then r = Nil. Here len(l) is the number of nodes in l and count(v, l) is the number of nodes in l whose stored value equals v.
  Preconditions: 0 <= len(head) <= 10000; every value stored in head is between 1 and 50 inclusive; 0 <= val <= 50. -/
theorem spec_11 (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r) :
    (head ≠ List.Nil ∧ count val.val head < len head →
        (elems r).head? = (removeVal val.val head).head?) ∧
      (count val.val head = len head → r = List.Nil) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : List) (val : Aeneas.Std.I64)
    (hlen : 0 ≤ len head ∧ len head ≤ 10000)
    (hin : ∀ x ∈ elems head, 1 ≤ x ∧ x ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 50)
    (r : List) (hr : Aegis.RemoveElements.remove_elements head val = ok r), (head ≠ List.Nil ∧ count val.val head < len head →
        (elems r).head? = (removeVal val.val head).head?) ∧
      (count val.val head = len head → r = List.Nil)) := by
  sorry

end AegisSpec.RemoveElements
