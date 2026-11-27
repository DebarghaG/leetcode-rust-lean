import Aegis.MergeTwoLists.Code.Funs

/-!
# Specifications of `Aegis.MergeTwoLists.merge_two_lists`

LeetCode problem `merge-two-sorted-lists`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MergeTwoLists

  abbrev RList : Type := Aegis.MergeTwoLists.List

  def vals : RList → List Int
    | .Nil => []
    | .Cons v tl => v.val :: vals tl

  def len (l : RList) : Nat := (vals l).length

  def count : RList → Int → Nat
    | .Nil, _ => 0
    | .Cons v tl, x => (if v.val = x then 1 else 0) + count tl x

  def Nondec (L : List Int) : Prop :=
    ∀ (i : Nat) (h : i + 1 < L.length), L.get ⟨i, Nat.lt_of_succ_lt h⟩ ≤ L.get ⟨i + 1, h⟩

  def minPayload (l1 l2 : List Int) : Int :=
    match (l1 ++ l2).head? with
    | none => 0
    | some x => (l1 ++ l2).foldl (fun a b => min a b) x

  def maxPayload (l1 l2 : List Int) : Int :=
    match (l1 ++ l2).head? with
    | none => 0
    | some x => (l1 ++ l2).foldl (fun a b => max a b) x

  /-- The function returns a result r and the following hold: (1) vals(r) is non-decreasing; (2) for every integer x, count(r,x) = count(list1,x) + count(list2,x), where count(L,x) is the number of nodes of L whose payload is x. Consequently len(r)=len(list1)+len(list2) and vals(r) is exactly the non-decreasing sequence of the multiset union of vals(list1) and vals(list2).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence (v0,...,v_{n-1}) of its payloads from head to tail, len(L)=n, and non-decreasing means for every i with 0 <= i and i+1 < n, vals(L)[i] <= vals(L)[i+1]. -/
  theorem spec_1 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∃ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r ∧
        Nondec (vals r) ∧
        (∀ x : Int, count r x = count list1 x + count list2 x) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∃ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r ∧
          Nondec (vals r) ∧
          (∀ x : Int, count r x = count list1 x + count list2 x)) := by
    sorry

  /-- The function returns a result r; in particular, for every input satisfying the preconditions the evaluation does not fail, panic, read out of bounds, or overflow.
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_2 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∃ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∃ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, vals(r) is non-decreasing: for every i with 0 <= i and i+1 < len(r), vals(r)[i] <= vals(r)[i+1].
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_3 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → Nondec (vals r) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → Nondec (vals r)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x, count(r,x) = count(list1,x) + count(list2,x), where count(L,x) is the number of nodes of L whose payload is x.
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_4 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        ∀ x : Int, count r x = count list1 x + count list2 x := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          ∀ x : Int, count r x = count list1 x + count list2 x) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(list1) + len(list2).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_5 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        len r = len list1 + len list2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          len r = len list1 + len list2) := by
    sorry

  /-- If len(list2)=0, then whenever the function returns a result r, vals(r)=vals(list1); equivalently len(r)=len(list1) and vals(r)[i]=vals(list1)[i] for every i with 0 <= i < len(list1).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_6 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      len list2 = 0 →
        ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → vals r = vals list1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), len list2 = 0 →
          ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → vals r = vals list1) := by
    sorry

  /-- If len(list1)=0, then whenever the function returns a result r, vals(r)=vals(list2); equivalently len(r)=len(list2) and vals(r)[i]=vals(list2)[i] for every i with 0 <= i < len(list2).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_7 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      len list1 = 0 →
        ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → vals r = vals list2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), len list1 = 0 →
          ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → vals r = vals list2) := by
    sorry

  /-- Whenever the function returns a result r, if len(list1)+len(list2)>0 then r is nonempty and vals(r)[0] = min({ vals(list1)[i] | 0 <= i < len(list1) } ∪ { vals(list2)[j] | 0 <= j < len(list2) }).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_8 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      0 < len list1 + len list2 →
        ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          (vals r).head? = some (minPayload (vals list1) (vals list2)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), 0 < len list1 + len list2 →
          ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
            (vals r).head? = some (minPayload (vals list1) (vals list2))) := by
    sorry

  /-- Whenever the function returns a result r, if len(list1)+len(list2)>0 then r is nonempty and vals(r)[len(r)-1] = max({ vals(list1)[i] | 0 <= i < len(list1) } ∪ { vals(list2)[j] | 0 <= j < len(list2) }).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_9 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      0 < len list1 + len list2 →
        ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          (vals r).getLast? = some (maxPayload (vals list1) (vals list2)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), 0 < len list1 + len list2 →
          ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
            (vals r).getLast? = some (maxPayload (vals list1) (vals list2))) := by
    sorry

  /-- Whenever the function returns a result r, every payload in r lies in [-100,100]: for every i with 0 <= i < len(r), -100 <= vals(r)[i] <= 100.
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_10 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        ∀ x ∈ vals r, -100 ≤ x ∧ x ≤ 100 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          ∀ x ∈ vals r, -100 ≤ x ∧ x ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r, if every payload of list1 is <= every payload of list2 (that is, for all i,j with 0 <= i < len(list1) and 0 <= j < len(list2), vals(list1)[i] <= vals(list2)[j]), then vals(r) = vals(list1) ++ vals(list2).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_11 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        (∀ (i j : Nat) (hi : i < (vals list1).length) (hj : j < (vals list2).length),
          (vals list1).get ⟨i, hi⟩ ≤ (vals list2).get ⟨j, hj⟩) →
        vals r = vals list1 ++ vals list2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          (∀ (i j : Nat) (hi : i < (vals list1).length) (hj : j < (vals list2).length),
            (vals list1).get ⟨i, hi⟩ ≤ (vals list2).get ⟨j, hj⟩) →
          vals r = vals list1 ++ vals list2) := by
    sorry

  /-- Whenever the function returns a result r, if every payload of list2 is <= every payload of list1 (that is, for all i,j with 0 <= i < len(list2) and 0 <= j < len(list1), vals(list2)[i] <= vals(list1)[j]), then vals(r) = vals(list2) ++ vals(list1).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_12 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        (∀ (i j : Nat) (hi : i < (vals list2).length) (hj : j < (vals list1).length),
          (vals list2).get ⟨i, hi⟩ ≤ (vals list1).get ⟨j, hj⟩) →
        vals r = vals list2 ++ vals list1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          (∀ (i j : Nat) (hi : i < (vals list2).length) (hj : j < (vals list1).length),
            (vals list2).get ⟨i, hi⟩ ≤ (vals list1).get ⟨j, hj⟩) →
          vals r = vals list2 ++ vals list1) := by
    sorry

  /-- Whenever merge_two_lists list1 list2 returns a result r and merge_two_lists list2 list1 returns a result s, vals(r) = vals(s).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_13 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r s, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
        Aegis.MergeTwoLists.merge_two_lists list2 list1 = ok s → vals r = vals s := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r s, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r →
          Aegis.MergeTwoLists.merge_two_lists list2 list1 = ok s → vals r = vals s) := by
    sorry

  /-- Whenever the function returns a result r, if len(r)>0 then either (len(list1)>0 and vals(r)[0]=vals(list1)[0]) or (len(list2)>0 and vals(r)[0]=vals(list2)[0]).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_14 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → 0 < (vals r).length →
        (0 < (vals list1).length ∧ (vals r).head? = (vals list1).head?) ∨
        (0 < (vals list2).length ∧ (vals r).head? = (vals list2).head?) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → 0 < (vals r).length →
          (0 < (vals list1).length ∧ (vals r).head? = (vals list1).head?) ∨
          (0 < (vals list2).length ∧ (vals r).head? = (vals list2).head?)) := by
    sorry

  /-- Whenever the function returns a result r, if len(r)>0 then either (len(list1)>0 and vals(r)[len(r)-1]=vals(list1)[len(list1)-1]) or (len(list2)>0 and vals(r)[len(r)-1]=vals(list2)[len(list2)-1]).
    Preconditions: list1 and list2 are finite linked lists of type List; len(list1) <= 50 and len(list2) <= 50; every payload in either list lies in [-100, 100]; and vals(list1) and vals(list2) are non-decreasing, where for any finite List L, vals(L) is the sequence of its payloads from head to tail and len(L) is its length. -/
  theorem spec_15 (list1 list2 : RList)
      (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
      (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
      (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
      (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)) :
      ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → 0 < (vals r).length →
        (0 < (vals list1).length ∧ (vals r).getLast? = (vals list1).getLast?) ∨
        (0 < (vals list2).length ∧ (vals r).getLast? = (vals list2).getLast?) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (list1 list2 : RList)
        (h1len : len list1 ≤ 50) (h2len : len list2 ≤ 50)
        (h1rng : ∀ x ∈ vals list1, -100 ≤ x ∧ x ≤ 100)
        (h2rng : ∀ x ∈ vals list2, -100 ≤ x ∧ x ≤ 100)
        (h1nd : Nondec (vals list1)) (h2nd : Nondec (vals list2)), ∀ r, Aegis.MergeTwoLists.merge_two_lists list1 list2 = ok r → 0 < (vals r).length →
          (0 < (vals list1).length ∧ (vals r).getLast? = (vals list1).getLast?) ∨
          (0 < (vals list2).length ∧ (vals r).getLast? = (vals list2).getLast?)) := by
    sorry

  end AegisSpec.MergeTwoLists
