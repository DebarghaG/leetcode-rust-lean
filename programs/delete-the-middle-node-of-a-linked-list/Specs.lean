import Aegis.DeleteMiddle.Code.Funs

/-!
# Specifications of `Aegis.DeleteMiddle.delete_middle`

LeetCode problem `delete-the-middle-node-of-a-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DeleteMiddle

def vals : Aegis.DeleteMiddle.List → List ℤ
  | Aegis.DeleteMiddle.List.Nil => []
  | Aegis.DeleteMiddle.List.Cons v next => v.val :: vals next

def size (head : Aegis.DeleteMiddle.List) : ℕ := (vals head).length

def count (xs : List ℤ) (v : ℤ) : ℕ := (xs.filter (fun w => w = v)).length

/-- Let vals(x) be the sequence of i64 values of the nodes of x from front to back, and let m = floor(n/2). The function returns a result r and vals(r) = vals(head)[0..m] ++ vals(head)[m+1..n]; equivalently, r is exactly the list obtained from head by deleting the 0-based node at index m. In particular, if n = 1 then r is Nil.
  Preconditions: Let n be the number of nodes in head. Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_1 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      vals r = (vals head).take (size head / 2) ++
        (vals head).drop (size head / 2 + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      vals r = (vals head).take (size head / 2) ++
        (vals head).drop (size head / 2 + 1)) := by
  sorry

/-- The function returns a result r for some List r; it does not fail.
  Preconditions: Let n be the number of nodes in head. Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_2 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back. The function returns a result r and len(vals(r)) = n - 1.
  Preconditions: Let n be the number of nodes in head. Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_3 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      (vals r).length = size head - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      (vals r).length = size head - 1) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back. The function returns a result r and, for every i with 0 <= i < m, vals(r)[i] = vals(head)[i].
  Preconditions: Let n be the number of nodes in head, and let m = floor(n/2). Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_4 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ i : ℕ, i < size head / 2 → (vals r)[i]? = (vals head)[i]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ i : ℕ, i < size head / 2 → (vals r)[i]? = (vals head)[i]?) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back. The function returns a result r and, for every j with m <= j < n - 1, vals(r)[j] = vals(head)[j + 1].
  Preconditions: Let n be the number of nodes in head, and let m = floor(n/2). Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_5 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ j : ℕ, size head / 2 ≤ j → j < size head - 1 →
        (vals r)[j]? = (vals head)[j + 1]? := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ j : ℕ, size head / 2 ≤ j → j < size head - 1 →
        (vals r)[j]? = (vals head)[j + 1]?) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back. The function returns a result r and len(vals(r)) >= 1 and vals(r)[0] = vals(head)[0].
  Preconditions: Let n be the number of nodes in head. Assume 1 <= n <= 100000, every node value lies in [1, 100000], and n >= 2. -/
theorem spec_6 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hn_ge : 2 ≤ size head) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      1 ≤ (vals r).length ∧ (vals r)[0]? = (vals head)[0]? := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hn_ge : 2 ≤ size head), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      1 ≤ (vals r).length ∧ (vals r)[0]? = (vals head)[0]?) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back. The function returns a result r and len(vals(r)) >= 1 and vals(r)[n - 2] = vals(head)[n - 1].
  Preconditions: Let n be the number of nodes in head. Assume 1 <= n <= 100000, every node value lies in [1, 100000], and n >= 3. -/
theorem spec_7 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hn_ge : 3 ≤ size head) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      1 ≤ (vals r).length ∧
      (vals r)[size head - 2]? = (vals head)[size head - 1]? := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000)
    (hn_ge : 3 ≤ size head), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      1 ≤ (vals r).length ∧
      (vals r)[size head - 2]? = (vals head)[size head - 1]?) := by
  sorry

/-- Let vals(x) be the sequence of values of the nodes of x from front to back, and let count(xs, v) be the number of occurrences of value v in the sequence xs. The function returns a result r and, for every i64 value v, count(vals(r), v) = count(vals(head), v) - (if v = vals(head)[m] then 1 else 0).
  Preconditions: Let n be the number of nodes in head, and let m = floor(n/2). Assume 1 <= n <= 100000 and every node value lies in [1, 100000]. -/
theorem spec_8 (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ v : ℤ,
        count (vals r) v =
          count (vals head) v -
            (if (vals head)[size head / 2]? = some v then 1 else 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.DeleteMiddle.List)
    (hn_lo : 1 ≤ size head) (hn_hi : size head ≤ 100000)
    (hval : ∀ v ∈ vals head, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.DeleteMiddle.delete_middle head = ok r ∧
      ∀ v : ℤ,
        count (vals r) v =
          count (vals head) v -
            (if (vals head)[size head / 2]? = some v then 1 else 0)) := by
  sorry

end AegisSpec.DeleteMiddle
