import Aegis.HasCycle.Code.Funs

/-!
# Specifications of `Aegis.HasCycle.has_cycle`

LeetCode problem `linked-list-cycle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasCycle

def nodeVals : Aegis.HasCycle.List → List Int
  | .Nil => []
  | .Cons h t => h.val :: nodeVals t

def nodeCount : Aegis.HasCycle.List → Nat
  | .Nil => 0
  | .Cons _ t => nodeCount t + 1

/-- The function returns a result `r` and `r = false`.
  Preconditions: `head` is any finite value of type `List` whose length is at most 10000 and whose every node value lies in [-100000, 100000] (the original problem's constraints). No condition on `pos` is needed because `pos` is not a parameter. -/
theorem spec_1 (head : Aegis.HasCycle.List)
    (hlen : nodeCount head ≤ 10000)
    (hval : ∀ x ∈ nodeVals head, -100000 ≤ x ∧ x ≤ 100000) :
    ∃ r, Aegis.HasCycle.has_cycle head = ok r ∧ r = false := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.HasCycle.List)
    (hlen : nodeCount head ≤ 10000)
    (hval : ∀ x ∈ nodeVals head, -100000 ≤ x ∧ x ≤ 100000), ∃ r, Aegis.HasCycle.has_cycle head = ok r ∧ r = false) := by
  sorry

/-- The evaluation of `has_cycle head` terminates without failing: it does not panic, overflow, or access out of bounds, and it returns exactly one Boolean value.
  Preconditions: `head` is any finite value of type `List` whose length is at most 10000 and whose every node value lies in [-100000, 100000]. -/
theorem spec_2 (head : Aegis.HasCycle.List)
    (hlen : nodeCount head ≤ 10000)
    (hval : ∀ x ∈ nodeVals head, -100000 ≤ x ∧ x ≤ 100000) :
    ∃ r, Aegis.HasCycle.has_cycle head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.HasCycle.List)
    (hlen : nodeCount head ≤ 10000)
    (hval : ∀ x ∈ nodeVals head, -100000 ≤ x ∧ x ≤ 100000), ∃ r, Aegis.HasCycle.has_cycle head = ok r) := by
  sorry

end AegisSpec.HasCycle
