import Aegis.SwapPairs.Code.Funs

/-!
# Specifications of `Aegis.SwapPairs.swap_pairs`

LeetCode problem `swap-nodes-in-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aegis.SwapPairs

def List.val : List → _root_.List Aeneas.Std.I64
  | List.Nil => []
  | List.Cons v rest => v :: rest.val

def List.nth? (l : List) (i : Nat) : Option Int :=
  (l.val[i]?).map (fun v => v.val)

def List.countVal (l : List) (v : Int) : Nat :=
  l.val.countP (fun x => x.val == v)

end Aegis.SwapPairs

namespace AegisSpec.SwapPairs

/-- The function returns a result r (it does not fail) such that len(r) = len(head), and for every integer k with 0 <= k and 2*k + 1 < len(head): r[2*k] = head[2*k+1] and r[2*k+1] = head[2*k]; moreover, if len(head) is odd, then r[len(head)-1] = head[len(head)-1].
  Preconditions: len(head) <= 100 and for every i with 0 <= i < len(head), 0 <= head[i] <= 100. -/
theorem spec_1 (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100) :
    ∃ r : Aegis.SwapPairs.List,
      Aegis.SwapPairs.swap_pairs head = ok r ∧
        r.val.length = head.val.length ∧
        (∀ (k : Nat), 2 * k + 1 < head.val.length →
          r.nth? (2 * k) = head.nth? (2 * k + 1) ∧
            r.nth? (2 * k + 1) = head.nth? (2 * k)) ∧
        (Odd head.val.length →
          r.nth? (head.val.length - 1) = head.nth? (head.val.length - 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100), ∃ r : Aegis.SwapPairs.List,
      Aegis.SwapPairs.swap_pairs head = ok r ∧
        r.val.length = head.val.length ∧
        (∀ (k : Nat), 2 * k + 1 < head.val.length →
          r.nth? (2 * k) = head.nth? (2 * k + 1) ∧
            r.nth? (2 * k + 1) = head.nth? (2 * k)) ∧
        (Odd head.val.length →
          r.nth? (head.val.length - 1) = head.nth? (head.val.length - 1))) := by
  sorry

/-- Whenever the function returns a result r, for every integer value v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(head) and head[j] = v.
  Preconditions: len(head) <= 100 and for every i with 0 <= i < len(head), 0 <= head[i] <= 100. -/
theorem spec_2 (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100) :
    ∀ (r : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs head = ok r →
      ∀ (v : Int), r.countVal v = head.countVal v := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100), ∀ (r : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs head = ok r →
      ∀ (v : Int), r.countVal v = head.countVal v) := by
  sorry

/-- Whenever the function returns a result r on input head, and then returns a result r' on input r, we have r' = head.
  Preconditions: len(head) <= 100 and for every i with 0 <= i < len(head), 0 <= head[i] <= 100. -/
theorem spec_3 (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100) :
    ∀ (r : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs head = ok r →
      ∀ (r' : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs r = ok r' → r' = head := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.SwapPairs.List)
    (h_len : head.val.length ≤ 100)
    (h_bounds : ∀ (i : Nat) (hi : i < head.val.length),
      0 ≤ (head.val[i]).val ∧ (head.val[i]).val ≤ 100), ∀ (r : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs head = ok r →
      ∀ (r' : Aegis.SwapPairs.List), Aegis.SwapPairs.swap_pairs r = ok r' → r' = head) := by
  sorry

end AegisSpec.SwapPairs
