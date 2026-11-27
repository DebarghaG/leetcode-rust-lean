import Aegis.ReverseBetween.Code.Funs

/-!
# Specifications of `Aegis.ReverseBetween.reverse_between`

LeetCode problem `reverse-linked-list-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReverseBetween

  def vals : Aegis.ReverseBetween.List → List Int
    | Aegis.ReverseBetween.List.Nil => []
    | Aegis.ReverseBetween.List.Cons v next => v.val :: vals next

  def countOcc (xs : List Int) (v : Int) : Nat :=
    List.length (List.filter (fun x => decide (x = v)) xs)

  def atPos (xs : List Int) (p : Int) : Option Int :=
    xs[(p - 1).toNat]?

  /-- Whenever reverse_between head left right returns a result r, let xs be the sequence of values of head in order (xs[0],...,xs[n-1]) and let ys be the sequence of values of r in order. Then len(ys) = n, and for every integer position p with 1 <= p <= n: if p < left or p > right then ys[p-1] = xs[p-1], and if left <= p <= right then ys[p-1] = xs[left + right - p - 1].
    Preconditions: Let n = len(head) be the number of nodes in head. The list head is nonempty (1 <= n <= 500), every node value lies in [-500, 500], and the mathematical values of left and right satisfy 1 <= left <= right <= n. -/
  theorem spec_1
      (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
      (hne : 1 ≤ List.length (vals head))
      (hlen : List.length (vals head) ≤ 500)
      (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
      (hleft : 1 ≤ left.val)
      (hord : left.val ≤ right.val)
      (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)) :
      ∀ r : Aegis.ReverseBetween.List,
        Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r →
        List.length (vals r) = List.length (vals head) ∧
          (∀ p : Int, 1 ≤ p → p ≤ ((List.length (vals head) : Nat) : Int) →
            ((p < left.val ∨ right.val < p) →
                atPos (vals r) p = atPos (vals head) p) ∧
            ((left.val ≤ p ∧ p ≤ right.val) →
                atPos (vals r) p = atPos (vals head) (left.val + right.val - p))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
        (hne : 1 ≤ List.length (vals head))
        (hlen : List.length (vals head) ≤ 500)
        (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
        (hleft : 1 ≤ left.val)
        (hord : left.val ≤ right.val)
        (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)), ∀ r : Aegis.ReverseBetween.List,
          Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r →
          List.length (vals r) = List.length (vals head) ∧
            (∀ p : Int, 1 ≤ p → p ≤ ((List.length (vals head) : Nat) : Int) →
              ((p < left.val ∨ right.val < p) →
                  atPos (vals r) p = atPos (vals head) p) ∧
              ((left.val ≤ p ∧ p ≤ right.val) →
                  atPos (vals r) p = atPos (vals head) (left.val + right.val - p)))) := by
    sorry

  /-- On every input satisfying the preconditions, reverse_between head left right returns a result r; it does not fail, panic, overflow, or access an out-of-range position.
    Preconditions: Let n = len(head) be the number of nodes in head. The list head is nonempty (1 <= n <= 500), every node value lies in [-500, 500], and the mathematical values of left and right satisfy 1 <= left <= right <= n. -/
  theorem spec_2
      (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
      (hne : 1 ≤ List.length (vals head))
      (hlen : List.length (vals head) ≤ 500)
      (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
      (hleft : 1 ≤ left.val)
      (hord : left.val ≤ right.val)
      (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)) :
      ∃ r : Aegis.ReverseBetween.List,
        Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
        (hne : 1 ≤ List.length (vals head))
        (hlen : List.length (vals head) ≤ 500)
        (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
        (hleft : 1 ≤ left.val)
        (hord : left.val ≤ right.val)
        (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)), ∃ r : Aegis.ReverseBetween.List,
          Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever reverse_between head left right returns a result r, let xs be the sequence of values of head and ys the sequence of values of r. For every integer value v, the number of indices i with 0 <= i < n and xs[i] = v equals the number of indices j with 0 <= j < len(ys) and ys[j] = v.
    Preconditions: Let n = len(head) be the number of nodes in head. The list head is nonempty (1 <= n <= 500), every node value lies in [-500, 500], and the mathematical values of left and right satisfy 1 <= left <= right <= n. -/
  theorem spec_3
      (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
      (hne : 1 ≤ List.length (vals head))
      (hlen : List.length (vals head) ≤ 500)
      (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
      (hleft : 1 ≤ left.val)
      (hord : left.val ≤ right.val)
      (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)) :
      ∀ r : Aegis.ReverseBetween.List,
        Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r →
        ∀ v : Int, countOcc (vals head) v = countOcc (vals r) v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.ReverseBetween.List) (left right : Aeneas.Std.I64)
        (hne : 1 ≤ List.length (vals head))
        (hlen : List.length (vals head) ≤ 500)
        (hval : ∀ v ∈ vals head, -500 ≤ v ∧ v ≤ 500)
        (hleft : 1 ≤ left.val)
        (hord : left.val ≤ right.val)
        (hright : right.val ≤ ((List.length (vals head) : Nat) : Int)), ∀ r : Aegis.ReverseBetween.List,
          Aegis.ReverseBetween.reverse_between head left right = Aeneas.Std.Result.ok r →
          ∀ v : Int, countOcc (vals head) v = countOcc (vals r) v) := by
    sorry

  end AegisSpec.ReverseBetween
