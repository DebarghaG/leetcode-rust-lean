import Aegis.RemoveNthFromEnd.Code.Funs

/-!
# Specifications of `Aegis.RemoveNthFromEnd.remove_nth_from_end`

LeetCode problem `remove-nth-node-from-end-of-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveNthFromEnd

def values : Aegis.RemoveNthFromEnd.List → List Int
  | .Nil => []
  | .Cons v next => v.val :: values next

def size (head : Aegis.RemoveNthFromEnd.List) : Nat := (values head).length

def removeIdx (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64) : Nat :=
  size head - n.val.toNat

def elemAt (L : List Int) (i : Nat) : Int := (L[i]?).getD 0

def IsValueSubsequence (l A : List Int) : Prop :=
  ∃ p : List Nat,
    p.length = l.length ∧
      p.Pairwise (· < ·) ∧
        (∀ x ∈ p, x < A.length) ∧
          (∀ (i x : Nat), p[i]? = some x → l[i]? = A[x]?)

/-- Let A = [a_0, a_1, ..., a_{sz-1}] be the sequence of values of the nodes of head in order from the head to Nil, and let j = sz - n. Then remove_nth_from_end head n returns a result r (it does not fail) such that values(r) is the sequence obtained from A by deleting the single entry a_j at 0-based index j. Equivalently, len(r) = sz - 1 and, for every i with 0 <= i < sz - 1, r[i] = a_i when i < j and r[i] = a_{i+1} when i >= j. If sz = 1 then the result is Nil (the empty sequence).
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_1 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        values r = (values head).eraseIdx (removeIdx head n) ∧
          size r = size head - 1 ∧
            (∀ i, i < removeIdx head n → (values r)[i]? = (values head)[i]?) ∧
              (∀ i, removeIdx head n ≤ i → i < size head - 1 →
                (values r)[i]? = (values head)[i + 1]?) ∧
                (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        values r = (values head).eraseIdx (removeIdx head n) ∧
          size r = size head - 1 ∧
            (∀ i, i < removeIdx head n → (values r)[i]? = (values head)[i]?) ∧
              (∀ i, removeIdx head n ≤ i → i < size head - 1 →
                (values r)[i]? = (values head)[i + 1]?) ∧
                (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil)) := by
  sorry

/-- For every head and n satisfying the preconditions, remove_nth_from_end head n returns some result r; evaluation does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_2 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r) := by
  sorry

/-- Let sz = len(head). For every head and n satisfying the preconditions, whenever remove_nth_from_end head n returns a result r, the number of nodes in r is len(r) = sz - 1.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_3 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r → size r = size head - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r → size r = size head - 1) := by
  sorry

/-- Let sz = len(head). For every head and n satisfying the preconditions, whenever remove_nth_from_end head n returns a result r, r = Nil if and only if sz = 1. In that case n = 1 and the single node has been removed.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_4 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ((r = Aegis.RemoveNthFromEnd.List.Nil ↔ size head = 1) ∧
          (size head = 1 → n.val = 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ((r = Aegis.RemoveNthFromEnd.List.Nil ↔ size head = 1) ∧
          (size head = 1 → n.val = 1))) := by
  sorry

/-- Let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, and let r be the result returned by remove_nth_from_end head n (it does not fail). Then len(r) = sz - 1 and, for every i with 0 <= i < sz - 1, r[i] = a_i; thus exactly the final node is removed. In the case sz = 1 the result is r = Nil (the empty list).
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and n = 1. -/
theorem spec_5 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn : n.val = 1) :
    ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        size r = size head - 1 ∧
          (∀ i, i < size head - 1 → (values r)[i]? = (values head)[i]?) ∧
            (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn : n.val = 1), ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        size r = size head - 1 ∧
          (∀ i, i < size head - 1 → (values r)[i]? = (values head)[i]?) ∧
            (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil)) := by
  sorry

/-- Let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head. Whenever remove_nth_from_end head n returns a result r, len(r) = sz - 1 and, for every i with 0 <= i < sz - 1, r[i] = a_{i+1}; in particular r = Nil when sz = 1. Thus exactly the original first node is removed and the remaining list is returned in the same order.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and n = sz. -/
theorem spec_6 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn : n.val = (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        (size r = size head - 1 ∧
          (∀ i, i < size head - 1 → (values r)[i]? = (values head)[i + 1]?) ∧
            (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn : n.val = (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        (size r = size head - 1 ∧
          (∀ i, i < size head - 1 → (values r)[i]? = (values head)[i + 1]?) ∧
            (size head = 1 → r = Aegis.RemoveNthFromEnd.List.Nil))) := by
  sorry

/-- Let sz = len(head), let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, and let j = sz - n. Whenever remove_nth_from_end head n returns a result r, for every index i with 0 <= i < j, r[i] = a_i. (If j = 0 this condition is vacuous.)
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_7 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ i, i < removeIdx head n → (values r)[i]? = (values head)[i]? := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ i, i < removeIdx head n → (values r)[i]? = (values head)[i]?) := by
  sorry

/-- Let sz = len(head), let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, and let j = sz - n. Whenever remove_nth_from_end head n returns a result r, for every index i with j <= i < sz - 1, r[i] = a_{i+1}. (If j = sz - 1 this condition is vacuous.)
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_8 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ i, removeIdx head n ≤ i → i < size head - 1 →
          (values r)[i]? = (values head)[i + 1]? := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ i, removeIdx head n ≤ i → i < size head - 1 →
          (values r)[i]? = (values head)[i + 1]?) := by
  sorry

/-- Let sz = len(head), let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, let j = sz - n, and let r be any result returned by remove_nth_from_end head n. For every integer v, let count(v, L) be the number of indices i with L[i] = v. Then count(v, r) = count(v, A) - 1 if v = a_j, and count(v, r) = count(v, A) otherwise.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_9 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ v : Int,
          (values r).count v =
            (values head).count v -
              (if v = elemAt (values head) (removeIdx head n) then 1 else 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        ∀ v : Int,
          (values r).count v =
            (values head).count v -
              (if v = elemAt (values head) (removeIdx head n) then 1 else 0)) := by
  sorry

/-- Let sz = len(head), let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, and let r be any result returned by remove_nth_from_end head n. There is an increasing sequence of indices (p_i) for 0 <= i < len(r) with 0 <= p_i < sz such that r[i] = A[p_i] for every i. Thus values(r) is a subsequence of A, preserving the original relative order.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_10 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        IsValueSubsequence (values r) (values head) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        IsValueSubsequence (values r) (values head)) := by
  sorry

/-- Let sz = len(head), let A = [a_0, ..., a_{sz-1}] be the sequence of values of the nodes of head, and let j = sz - n. Whenever remove_nth_from_end head n returns a result r, inserting the value a_j into values(r) immediately before position j (where position j = len(values(r)) means appending at the end) produces exactly A. Equivalently, values(r) is A with the single occurrence at index j deleted.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_11 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)) :
    ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        (values r).take (removeIdx head n) ++
              [elemAt (values head) (removeIdx head n)] ++
            (values r).drop (removeIdx head n) =
          values head := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64)
    (hsz_pos : 1 ≤ size head) (hsz_le : size head ≤ 30)
    (hvals : ∀ v, v ∈ values head → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (size head : Int)), ∀ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r →
        (values r).take (removeIdx head n) ++
              [elemAt (values head) (removeIdx head n)] ++
            (values r).drop (removeIdx head n) =
          values head) := by
  sorry

/-- Evaluating remove_nth_from_end head n leaves the argument unchanged: after the call, head still denotes the original sequence A of length sz. The returned list is a fresh List and no input node value is mutated.
  Preconditions: Let sz = len(head). 1 <= sz <= 30; every value occurring in head is an integer v with 0 <= v <= 100; and 1 <= n <= sz. -/
theorem spec_12 (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64) (A : List Int)
    (hA : values head = A)
    (hsz_pos : 1 ≤ A.length) (hsz_le : A.length ≤ 30)
    (hvals : ∀ v, v ∈ A → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (A.length : Int)) :
    ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        values head = A ∧
          (∀ v, v ∈ values r → v ∈ A) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.RemoveNthFromEnd.List) (n : Std.I64) (A : List Int)
    (hA : values head = A)
    (hsz_pos : 1 ≤ A.length) (hsz_le : A.length ≤ 30)
    (hvals : ∀ v, v ∈ A → 0 ≤ v ∧ v ≤ 100)
    (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ (A.length : Int)), ∃ r : Aegis.RemoveNthFromEnd.List,
      Aegis.RemoveNthFromEnd.remove_nth_from_end head n = ok r ∧
        values head = A ∧
          (∀ v, v ∈ values r → v ∈ A)) := by
  sorry

end AegisSpec.RemoveNthFromEnd
