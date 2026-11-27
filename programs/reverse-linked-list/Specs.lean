import Aegis.ReverseList.Code.Funs

/-!
# Specifications of `Aegis.ReverseList.reverse_list`

LeetCode problem `reverse-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ReverseList

abbrev RustList : Type := Aegis.ReverseList.List

def nodeCount : RustList → Nat
  | .Nil => 0
  | .Cons _ tl => nodeCount tl + 1

def nodeValues : RustList → List Int
  | .Nil => []
  | .Cons v tl => v.val :: nodeValues tl

def nodeCountAtMost (n : Nat) (l : RustList) : Prop :=
  nodeCount l ≤ n

def nodeValuesWithin (lo hi : Int) (l : RustList) : Prop :=
  ∀ v ∈ nodeValues l, lo ≤ v ∧ v ≤ hi

/-- Let n be the number of nodes in head. Whenever reverse_list head returns a result r, if xs is the sequence of node values of head read from head to tail and ys is the sequence of node values of r read from head to tail, then len(ys) = n and, for every i with 0 <= i < n, ys[i] = xs[n - 1 - i].
  Preconditions: The input list head has at most 5000 nodes, and every node value in head lies in the inclusive range [-5000, 5000]. -/
theorem spec_1 (head : RustList)
    (h_len : nodeCountAtMost 5000 head)
    (h_range : nodeValuesWithin (-5000) 5000 head) :
    ∀ r : RustList, Aegis.ReverseList.reverse_list head = ok r →
      (nodeValues r).length = nodeCount head ∧
        ∀ i : Nat, i < nodeCount head →
          (nodeValues r)[i]? = (nodeValues head)[nodeCount head - 1 - i]? := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : RustList)
    (h_len : nodeCountAtMost 5000 head)
    (h_range : nodeValuesWithin (-5000) 5000 head), ∀ r : RustList, Aegis.ReverseList.reverse_list head = ok r →
      (nodeValues r).length = nodeCount head ∧
        ∀ i : Nat, i < nodeCount head →
          (nodeValues r)[i]? = (nodeValues head)[nodeCount head - 1 - i]?) := by
  sorry

/-- For every head satisfying the preconditions, reverse_list head returns a result r; it does not fail.
  Preconditions: The input list head has at most 5000 nodes, and every node value in head lies in the inclusive range [-5000, 5000]. -/
theorem spec_2 (head : RustList)
    (h_len : nodeCountAtMost 5000 head)
    (h_range : nodeValuesWithin (-5000) 5000 head) :
    ∃ r : RustList, Aegis.ReverseList.reverse_list head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : RustList)
    (h_len : nodeCountAtMost 5000 head)
    (h_range : nodeValuesWithin (-5000) 5000 head), ∃ r : RustList, Aegis.ReverseList.reverse_list head = ok r) := by
  sorry

end AegisSpec.ReverseList
