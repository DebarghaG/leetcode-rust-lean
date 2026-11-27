import Aegis.InsertionSortList.Code.Funs

/-!
# Specifications of `Aegis.InsertionSortList.insertion_sort_list`

LeetCode problem `insertion-sort-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.InsertionSortList

  abbrev NList : Type := Aegis.InsertionSortList.List

  def values : NList → List Int
    | .Nil => []
    | .Cons v next => v.val :: values next

  def countOcc (x : Int) (l : List Int) : Nat :=
    l.countP (fun y => decide (y = x))

  def Nondecreasing (l : List Int) : Prop :=
    ∀ (i : Nat) (hi : i + 1 < l.length),
      l[i]'(Nat.lt_of_le_of_lt (Nat.le_succ i) hi) ≤ l[i+1]'hi

  def BoundedVals (l : List Int) : Prop :=
    ∀ v ∈ l, (-5000 : Int) ≤ v ∧ v ≤ 5000

  def listMin (l : List Int) : Option Int := l.min?

  def listMax (l : List Int) : Option Int := l.max?

  /-- The function returns a result r and vals(r) is the nondecreasing rearrangement of vals(head): (1) len(vals(r)) = n; (2) for every i with 0 <= i < len(vals(r))-1, vals(r)[i] <= vals(r)[i+1]; (3) for every integer x, the number of occurrences of x in vals(r) equals the number of occurrences of x in vals(head).
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_1 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∃ r, Aegis.InsertionSortList.insertion_sort_list head = ok r ∧
        (values r).length = (values head).length ∧
        Nondecreasing (values r) ∧
        (∀ x : Int, countOcc x (values r) = countOcc x (values head)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∃ r, Aegis.InsertionSortList.insertion_sort_list head = ok r ∧
          (values r).length = (values head).length ∧
          Nondecreasing (values r) ∧
          (∀ x : Int, countOcc x (values r) = countOcc x (values head))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_2 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∃ r, Aegis.InsertionSortList.insertion_sort_list head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∃ r, Aegis.InsertionSortList.insertion_sort_list head = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(vals(r)) = len(vals(head)).
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_3 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        (values r).length = (values head).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          (values r).length = (values head).length) := by
    sorry

  /-- Whenever the function returns a result r, vals(r) is nondecreasing: for every i with 0 <= i < len(vals(r))-1, vals(r)[i] <= vals(r)[i+1].
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_4 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        Nondecreasing (values r) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          Nondecreasing (values r)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x, the number of occurrences of x in vals(r) equals the number of occurrences of x in vals(head).
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_5 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        (∀ x : Int, countOcc x (values r) = countOcc x (values head)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          (∀ x : Int, countOcc x (values r) = countOcc x (values head))) := by
    sorry

  /-- Whenever the function returns a result r, len(vals(r)) >= 1 and vals(r)[0] = min { vals(head)[j] | 0 <= j < len(vals(head)) }.
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_6 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        1 ≤ (values r).length ∧ (values r)[0]? = listMin (values head) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          1 ≤ (values r).length ∧ (values r)[0]? = listMin (values head)) := by
    sorry

  /-- Whenever the function returns a result r, len(vals(r)) >= 1 and vals(r)[len(vals(r))-1] = max { vals(head)[j] | 0 <= j < len(vals(head)) }.
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_7 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        1 ≤ (values r).length ∧
          (values r)[(values r).length - 1]? = listMax (values head) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          1 ≤ (values r).length ∧
            (values r)[(values r).length - 1]? = listMax (values head)) := by
    sorry

  /-- Whenever the function returns a result r, every value v occurring in vals(r) satisfies -5000 <= v <= 5000.
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_8 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        BoundedVals (values r) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          BoundedVals (values r)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(vals(head)), there exists i with 0 <= i < len(vals(r)) and vals(r)[i] = vals(head)[j].
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_9 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        (∀ (j : Nat), j < (values head).length →
          ∃ (i : Nat), i < (values r).length ∧
            (values r)[i]? = (values head)[j]?) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          (∀ (j : Nat), j < (values head).length →
            ∃ (i : Nat), i < (values r).length ∧
              (values r)[i]? = (values head)[j]?)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(vals(r)), there exists j with 0 <= j < len(vals(head)) and vals(r)[i] = vals(head)[j].
    Preconditions: Write vals(l) for the sequence of values of the Cons nodes of a finite List l, from head to tail. Let n = len(vals(head)). Assume 1 <= n <= 5000, and for every i with 0 <= i < n, -5000 <= vals(head)[i] <= 5000. -/
  theorem spec_10 (head : NList)
      (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
      (hbnd : BoundedVals (values head)) :
      ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
        (∀ (i : Nat), i < (values r).length →
          ∃ (j : Nat), j < (values head).length ∧
            (values r)[i]? = (values head)[j]?) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (head : NList)
        (hpos : 1 ≤ (values head).length) (hmax : (values head).length ≤ 5000)
        (hbnd : BoundedVals (values head)), ∀ r, Aegis.InsertionSortList.insertion_sort_list head = ok r →
          (∀ (i : Nat), i < (values r).length →
            ∃ (j : Nat), j < (values head).length ∧
              (values r)[i]? = (values head)[j]?)) := by
    sorry

  end AegisSpec.InsertionSortList
