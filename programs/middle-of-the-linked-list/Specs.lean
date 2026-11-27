import Aegis.MiddleNode.Code.Funs

/-!
# Specifications of `Aegis.MiddleNode.middle_node`

LeetCode problem `middle-of-the-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aegis.MiddleNode.List

def val : List → _root_.List Int
  | Nil => []
  | Cons x xs => x.val :: val xs

def len (l : List) : Nat := l.val.length

def get (l : List) (i : Nat) : Int := l.val.getD i 0

end Aegis.MiddleNode.List

namespace AegisSpec.MiddleNode

/-- The function returns a result r (it does not fail). Let k = floor(n/2). Then len(r) = n - k, and for every j with 0 <= j < len(r), r[j] = head[k + j]. Equivalently, r is exactly the suffix of head that starts at 0-based index k, i.e. at the middle node (the second middle node when n is even).
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. Indices are 0-based; integer division rounds down. -/
theorem spec_1 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∃ r, Aegis.MiddleNode.middle_node head = ok r ∧
      r.len = head.len - head.len / 2 ∧
      (∀ j, j < r.len → r.get j = head.get (head.len / 2 + j)) ∧
      r.val = head.val.drop (head.len / 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∃ r, Aegis.MiddleNode.middle_node head = ok r ∧
      r.len = head.len - head.len / 2 ∧
      (∀ j, j < r.len → r.get j = head.get (head.len / 2 + j)) ∧
      r.val = head.val.drop (head.len / 2)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (Ok r); it does not fail.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_2 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∃ r, Aegis.MiddleNode.middle_node head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∃ r, Aegis.MiddleNode.middle_node head = ok r) := by
  sorry

/-- Whenever the function returns a result r, with n = len(head), len(r) = n - floor(n/2) = ceil(n/2).
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_3 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      r.len = head.len - head.len / 2 ∧ r.len = (head.len + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      r.len = head.len - head.len / 2 ∧ r.len = (head.len + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1; the returned list is not Nil.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_4 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      1 ≤ r.len ∧ r ≠ Aegis.MiddleNode.List.Nil := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      1 ≤ r.len ∧ r ≠ Aegis.MiddleNode.List.Nil) := by
  sorry

/-- Whenever the function returns a result r, if len(head) >= 2 then len(r) < len(head); the returned list is a proper suffix of the input.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_5 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r → 2 ≤ head.len →
      r.len < head.len ∧ ∃ k, 0 < k ∧ r.val = head.val.drop k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r → 2 ≤ head.len →
      r.len < head.len ∧ ∃ k, 0 < k ∧ r.val = head.val.drop k) := by
  sorry

/-- Whenever the function returns a result r, let n = len(head) and k = floor(n/2). For every j with 0 <= j < len(r), r[j] = head[k + j].
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_6 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∀ j, j < r.len → r.get j = head.get (head.len / 2 + j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∀ j, j < r.len → r.get j = head.get (head.len / 2 + j)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index k with 0 <= k <= len(head) such that len(r) = len(head) - k and for every j with 0 <= j < len(r), r[j] = head[k + j]. That is, r is a suffix of head.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_7 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∃ k, k ≤ head.len ∧ r.len = head.len - k ∧
        ∀ j, j < r.len → r.get j = head.get (k + j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∃ k, k ≤ head.len ∧ r.len = head.len - k ∧
        ∀ j, j < r.len → r.get j = head.get (k + j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[len(r)-1] = head[len(head)-1]; the last node of the input is also the last node of the result.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_8 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      1 ≤ r.len ∧ r.get (r.len - 1) = head.get (head.len - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      1 ≤ r.len ∧ r.get (r.len - 1) = head.get (head.len - 1)) := by
  sorry

/-- Whenever the function returns a result r, if n = len(head) is odd, then the first node of r is the unique middle node of head: the number of nodes of head before r[0] is floor(n/2), and the number of nodes of r after its first node is len(r)-1 = floor(n/2).
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_9 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r → Odd head.len →
      r.val = head.val.drop (head.len / 2) ∧
        r.get 0 = head.get (head.len / 2) ∧
        r.len - 1 = head.len / 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r → Odd head.len →
      r.val = head.val.drop (head.len / 2) ∧
        r.get 0 = head.get (head.len / 2) ∧
        r.len - 1 = head.len / 2) := by
  sorry

/-- Whenever the function returns a result r, if n = len(head) is even, then the first node of r is the second of the two middle nodes: the number of nodes of head before r[0] is n/2, and the number of nodes of r after its first node is len(r)-1 = n/2 - 1.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_10 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r → Even head.len →
      r.val = head.val.drop (head.len / 2) ∧
        r.get 0 = head.get (head.len / 2) ∧
        r.len - 1 = head.len / 2 - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r → Even head.len →
      r.val = head.val.drop (head.len / 2) ∧
        r.get 0 = head.get (head.len / 2) ∧
        r.len - 1 = head.len / 2 - 1) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer m such that 0 <= m < len(head), m = floor(len(head)/2), and r[0] = head[m].
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_11 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∃ m : Nat, m < head.len ∧ m = head.len / 2 ∧ r.get 0 = head.get m := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∃ m : Nat, m < head.len ∧ m = head.len / 2 ∧ r.get 0 = head.get m) := by
  sorry

/-- Whenever the function returns a result r, if there is an integer v such that for every i with 0 <= i < len(head), head[i] = v, then for every j with 0 <= j < len(r), r[j] = v.
  Preconditions: Let n = len(head). The preconditions are 1 <= n <= 100 and, for every i with 0 <= i < n, 1 <= head[i] <= 100. -/
theorem spec_12 (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100) :
    ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∀ v : Int, (∀ i, i < head.len → head.get i = v) →
        ∀ j, j < r.len → r.get j = v := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.MiddleNode.List)
    (hn_pos : 1 ≤ head.len) (hn_le : head.len ≤ 100)
    (hbound : ∀ i, i < head.len → 1 ≤ head.get i ∧ head.get i ≤ 100), ∀ r, Aegis.MiddleNode.middle_node head = ok r →
      ∀ v : Int, (∀ i, i < head.len → head.get i = v) →
        ∀ j, j < r.len → r.get j = v) := by
  sorry

end AegisSpec.MiddleNode
