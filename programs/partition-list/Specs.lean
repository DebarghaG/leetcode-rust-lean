import Aegis.Partition.Code.Funs

/-!
# Specifications of `Aegis.Partition.partition`

LeetCode problem `partition-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Partition

def nodes : Aegis.Partition.List → List Std.I64
  | .Nil => []
  | .Cons v rest => v :: nodes rest

def vals (head : Aegis.Partition.List) : List Int := (nodes head).map (fun v => v.val)

def len (head : Aegis.Partition.List) : Nat := (vals head).length

def below (l : List Int) (x : Int) : List Int := l.filter (fun v => v < x)

def atLeast (l : List Int) (x : Int) : List Int := l.filter (fun v => x ≤ v)

def countVal (l : List Int) (v : Int) : Nat := (l.filter (fun w => w = v)).length

def firstBelow : List Int → Int → Option Nat
  | [], _ => none
  | v :: rest, x => if v < x then some 0 else (firstBelow rest x).map (fun n => n + 1)

def firstAtLeast : List Int → Int → Option Nat
  | [], _ => none
  | v :: rest, x => if x ≤ v then some 0 else (firstAtLeast rest x).map (fun n => n + 1)

def lastAtLeast : List Int → Int → Option Nat
  | [], _ => none
  | v :: rest, x =>
      match lastAtLeast rest x with
      | some n => some (n + 1)
      | none => if x ≤ v then some 0 else none

/-- Whenever partition returns a result r, the following holds. Let a_0,...,a_{n-1} be the values of the nodes of head in order, where n = len(head), and let b_0,...,b_{m-1} be the values of the nodes of r in order, where m = len(r). Then m = n and b equals the concatenation of (the subsequence of a consisting of all a_i with a_i < x, in the original order) followed by (the subsequence of a consisting of all a_i with a_i >= x, in the original order). Equivalently, if k is the number of indices i with a_i < x, then b_0,...,b_{k-1} are exactly the entries of a that are < x in their original order, and b_k,...,b_{n-1} are exactly the entries of a that are >= x in their original order.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_1 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      vals r = below (vals head) x.val ++ atLeast (vals head) x.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      vals r = below (vals head) x.val ++ atLeast (vals head) x.val) := by
  sorry

/-- For every input satisfying the preconditions, partition returns a result r for some List r; it never fails (no Err, panic, or overflow).
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_2 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∃ r, Aegis.Partition.partition head x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∃ r, Aegis.Partition.partition head x = ok r) := by
  sorry

/-- Whenever partition returns a result r, len(r) = len(head).
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_3 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r → (vals r).length = (vals head).length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r → (vals r).length = (vals head).length) := by
  sorry

/-- Whenever partition returns a result r, for every integer v, the number of indices i with 0 <= i < len(head) and head's i-th node value = v equals the number of indices j with 0 <= j < len(r) and r's j-th node value = v.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_4 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      ∀ v : Int, countVal (vals head) v = countVal (vals r) v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      ∀ v : Int, countVal (vals head) v = countVal (vals r) v) := by
  sorry

/-- Whenever partition returns a result r, there exists an integer k with 0 <= k <= len(r) such that every r's j-th node value with 0 <= j < k is < x, and every r's j-th node value with k <= j < len(r) is >= x.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_5 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      ∃ k, k ≤ (vals r).length ∧
        (∀ v ∈ (vals r).take k, v < x.val) ∧
        (∀ v ∈ List.drop k (vals r), x.val ≤ v) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      ∃ k, k ≤ (vals r).length ∧
        (∀ v ∈ (vals r).take k, v < x.val) ∧
        (∀ v ∈ List.drop k (vals r), x.val ≤ v)) := by
  sorry

/-- Whenever partition returns a result r, the subsequence of r consisting of exactly those node values that are < x, in their order in r, is equal to the subsequence of head consisting of exactly those node values that are < x, in their order in head.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_6 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      below (vals r) x.val = below (vals head) x.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      below (vals r) x.val = below (vals head) x.val) := by
  sorry

/-- Whenever partition returns a result r, the subsequence of r consisting of exactly those node values that are >= x, in their order in r, is equal to the subsequence of head consisting of exactly those node values that are >= x, in their order in head.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_7 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      atLeast (vals r) x.val = atLeast (vals head) x.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      atLeast (vals r) x.val = atLeast (vals head) x.val) := by
  sorry

/-- Whenever partition returns a result r, the number of indices i with 0 <= i < len(head) and head's i-th node value < x equals the number of indices j with 0 <= j < len(r) and r's j-th node value < x.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_8 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      (below (vals head) x.val).length = (below (vals r) x.val).length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      (below (vals head) x.val).length = (below (vals r) x.val).length) := by
  sorry

/-- Whenever partition returns a result r, if there exists at least one node value of head that is < x, then the first node value of r equals the first node value of head that is < x; that is, r's 0-th node value = head's t-th node value, where t is the smallest index with 0 <= t < len(head) and head's t-th node value < x.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_9 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ v < x.val) →
      ∀ t, firstBelow (vals head) x.val = some t → (vals r)[0]? = (vals head)[t]? := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ v < x.val) →
      ∀ t, firstBelow (vals head) x.val = some t → (vals r)[0]? = (vals head)[t]?) := by
  sorry

/-- Whenever partition returns a result r, if there exists at least one node value of head that is >= x, then the last node value of r equals the last node value of head that is >= x; that is, r's (len(r)-1)-th node value = head's t-th node value, where t is the largest index with 0 <= t < len(head) and head's t-th node value >= x.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_10 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ x.val ≤ v) →
      ∀ t, lastAtLeast (vals head) x.val = some t → (vals r).getLast? = (vals head)[t]? := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ x.val ≤ v) →
      ∀ t, lastAtLeast (vals head) x.val = some t → (vals r).getLast? = (vals head)[t]?) := by
  sorry

/-- Whenever partition returns a result r, if there exists at least one node value of head that is >= x, and k is the number of node values of head that are < x, then r's k-th node value equals the first node value of head that is >= x.
  Preconditions: The list head has between 0 and 200 nodes; every node value of head lies in [-100, 100]; and -200 <= x <= 200, viewing x as its integer value. -/
theorem spec_11 (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200) :
    ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ x.val ≤ v) →
      ∀ t, firstAtLeast (vals head) x.val = some t →
        (vals r)[(below (vals head) x.val).length]? = (vals head)[t]? := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.Partition.List) (x : Std.I64)
    (hhead : len head ≤ 200)
    (hvals : ∀ v ∈ vals head, -100 ≤ v ∧ v ≤ 100)
    (hx : -200 ≤ x.val ∧ x.val ≤ 200), ∀ r, Aegis.Partition.partition head x = ok r →
      (∃ v, v ∈ vals head ∧ x.val ≤ v) →
      ∀ t, firstAtLeast (vals head) x.val = some t →
        (vals r)[(below (vals head) x.val).length]? = (vals head)[t]?) := by
  sorry

end AegisSpec.Partition
