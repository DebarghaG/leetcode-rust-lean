import Aegis.DeleteDuplicates.Code.Funs

/-!
# Specifications of `Aegis.DeleteDuplicates.delete_duplicates`

LeetCode problem `remove-duplicates-from-sorted-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DeleteDuplicates

  def vals : Aegis.DeleteDuplicates.List → List Int
    | Aegis.DeleteDuplicates.List.Nil => []
    | Aegis.DeleteDuplicates.List.Cons v rest => v.val :: vals rest

  def distinctAux (seen : List Int) : List Int → List Int
    | [] => []
    | x :: xs =>
      if seen.contains x then distinctAux seen xs else x :: distinctAux (x :: seen) xs

  def distinct (s : List Int) : List Int := distinctAux [] s

  def Occurs (v : Int) (l : Aegis.DeleteDuplicates.List) : Prop :=
    ∃ i : Nat, ∃ (_ : i < (vals l).length), (vals l)[i] = v

  def countStarts : List Int → Nat
    | [] => 0
    | x :: rest => go x rest
  where
    go : Int → List Int → Nat
      | _, [] => 1
      | x, y :: rest => (if x < y then 1 else 0) + go y rest

  def Precond (head : Aegis.DeleteDuplicates.List) : Prop :=
    (vals head).length ≤ 300 ∧
      (∀ (i : Nat) (_ : i < (vals head).length), -100 ≤ (vals head)[i] ∧ (vals head)[i] ≤ 100) ∧
      (∀ (i : Nat) (_ : i + 1 < (vals head).length), (vals head)[i] ≤ (vals head)[i + 1])

  /-- Writing vals(l) for the sequence of values stored in the nodes of list l from head to tail, whenever the function returns a result r, vals(r) = distinct(vals(head)), where distinct(s) is the sequence obtained from s by keeping the first occurrence of each value and deleting all later occurrences of that value. Because the input is sorted nondecreasing, this is equivalently the strictly increasing sequence of the distinct values occurring in head.
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_1 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r) :
      vals r = distinct (vals head) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r), vals r = distinct (vals head)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_2 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l, whenever the function returns a result r, vals(r) is a subsequence of vals(head): there is a strictly increasing sequence of indices j_0 < j_1 < ... < j_{m-1} with m = len(r) and 0 <= j_k < len(head) for all k, such that r[k] = head[j_k] for every k with 0 <= k < m. (When m = 0 the sequence of indices is empty.)
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_3 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r) :
      (vals r).Sublist (vals head) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r), (vals r).Sublist (vals head)) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l, whenever the function returns a result r, for every i with 0 <= i < len(r)-1, r[i] < r[i+1].
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_4 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
      (i : Nat) (hi : i + 1 < (vals r).length) :
      (vals r)[i] < (vals r)[i + 1] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
        (i : Nat) (hi : i + 1 < (vals r).length), (vals r)[i] < (vals r)[i + 1]) := by
    sorry

  /-- Writing occurs(v, l) to mean that some node of l has value v (i.e. there is i with 0 <= i < len(l) and the i-th node value of l equals v), whenever the function returns a result r, for every i64 v, occurs(v, r) iff occurs(v, head).
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_5 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
      (v : Aeneas.Std.I64) :
      Occurs v.val r ↔ Occurs v.val head := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
        (v : Aeneas.Std.I64), Occurs v.val r ↔ Occurs v.val head) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l, whenever the function returns a result r, if len(head) > 0 then len(r) > 0 and r[0] = head[0].
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_6 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
      (hne : 0 < (vals head).length) :
      ∃ (_ : 0 < (vals r).length), (vals r)[0] = (vals head)[0] := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
        (hne : 0 < (vals head).length), ∃ (_ : 0 < (vals r).length), (vals r)[0] = (vals head)[0]) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l, whenever the function returns a result r, if len(head) > 0 then len(r) > 0 and r[len(r)-1] = head[len(head)-1].
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_7 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
      (hne : 0 < (vals head).length) :
      ∃ (_ : 0 < (vals r).length),
        (vals r)[(vals r).length - 1] = (vals head)[(vals head).length - 1] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
        (hne : 0 < (vals head).length), ∃ (_ : 0 < (vals r).length),
          (vals r)[(vals r).length - 1] = (vals head)[(vals head).length - 1]) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l and len(l) for its length, whenever the function returns a result r, len(r) equals the number of indices i such that 0 <= i < len(head) and (i = 0 or head[i] > head[i-1]).
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_8 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r) :
      (vals r).length = countStarts (vals head) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r), (vals r).length = countStarts (vals head)) := by
    sorry

  /-- Writing vals(l) for the sequence of values in l, whenever the function returns a result r, for every i with 0 <= i < len(r), -100 <= r[i] <= 100.
    Preconditions: Let n = len(head). Assume 0 <= n <= 300. For every i with 0 <= i < n, the value of the i-th node of head (0-based) is between -100 and 100 inclusive. For every i with 0 <= i < n-1, head[i] <= head[i+1] (the list is sorted nondecreasing; equal adjacent values are duplicates). -/
  theorem spec_9 (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
      (r : Aegis.DeleteDuplicates.List)
      (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
      (i : Nat) (hi : i < (vals r).length) :
      -100 ≤ (vals r)[i] ∧ (vals r)[i] ≤ 100 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hpre : Precond head)
        (r : Aegis.DeleteDuplicates.List)
        (hres : Aegis.DeleteDuplicates.delete_duplicates head = ok r)
        (i : Nat) (hi : i < (vals r).length), -100 ≤ (vals r)[i] ∧ (vals r)[i] ≤ 100) := by
    sorry

  end AegisSpec.DeleteDuplicates
