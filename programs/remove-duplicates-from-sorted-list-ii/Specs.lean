import Aegis.DeleteDuplicates.Code.Funs

/-!
# Specifications of `Aegis.DeleteDuplicates.delete_duplicates`

LeetCode problem `remove-duplicates-from-sorted-list-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DeleteDuplicates

  def vals (l : Aegis.DeleteDuplicates.List) : List ℤ :=
    match l with
    | .Nil => []
    | .Cons v t => v.val :: vals t

  def len (l : Aegis.DeleteDuplicates.List) : Nat := (vals l).length

  def occ (v : ℤ) (l : Aegis.DeleteDuplicates.List) : Nat :=
    match l with
    | .Nil => 0
    | .Cons x t => (if x.val = v then 1 else 0) + occ v t

  def nonDecreasing (l : Aegis.DeleteDuplicates.List) : Prop :=
    ∀ (i : Nat) (h : i + 1 < (vals l).length),
      (vals l)[i]'(Nat.lt_trans (Nat.lt_succ_self i) h) ≤ (vals l)[i + 1]'h

  def inBounds (l : Aegis.DeleteDuplicates.List) : Prop :=
    ∀ (i : Nat) (h : i < (vals l).length),
      -100 ≤ (vals l)[i]'h ∧ (vals l)[i]'h ≤ 100

  def uniqueVals (l : Aegis.DeleteDuplicates.List) : List ℤ :=
    (List.finRange (vals l).length).filterMap fun i =>
      if occ ((vals l)[i.val]'i.isLt) l = 1 then some ((vals l)[i.val]'i.isLt) else none

  def IsSubsequence (s t : List ℤ) : Prop :=
    ∃ idx : Fin s.length → Fin t.length,
      (∀ k₁ k₂ : Fin s.length, k₁ < k₂ → idx k₁ < idx k₂) ∧
        ∀ k : Fin s.length, s.get k = t.get (idx k)

  /-- The function returns a result r such that vals(r) = [ vals(head)[i] | 0 <= i < len(head) and occ(vals(head)[i], head) = 1 ], where the sequence is taken in increasing order of i. Equivalently, vals(r) is obtained from vals(head) by deleting every occurrence of every value that occurs more than once in head, and keeping the remaining elements in their original relative order.
    Preconditions: head is a linked list whose value sequence vals(head) is non-decreasing: for every i with 0 <= i < len(head)-1, vals(head)[i] <= vals(head)[i+1]; and every value satisfies -100 <= vals(head)[i] <= 100 for 0 <= i < len(head). -/
  theorem spec_1 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ vals r = uniqueVals head := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ vals r = uniqueVals head) := by
    sorry

  /-- The function returns a result r with len(r) <= len(head).
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_2 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ len r ≤ len head := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ len r ≤ len head) := by
    sorry

  /-- For every such head the function returns a result r; it never fails, panics, reads out of bounds, or overflows.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_3 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r) := by
    sorry

  /-- The returned list r is sorted non-decreasing: for every i with 0 <= i < len(r)-1, vals(r)[i] <= vals(r)[i+1].
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_4 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ nonDecreasing r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧ nonDecreasing r) := by
    sorry

  /-- The returned list r contains no repeated value: for every i, j with 0 <= i < j < len(r), vals(r)[i] != vals(r)[j]. (Equivalently, given S4, vals(r) is strictly increasing.)
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_5 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        ∀ (i j : Nat) (hij : i < j) (hj : j < len r),
          (vals r)[i]'(Nat.lt_trans hij hj) ≠ (vals r)[j]'hj := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          ∀ (i j : Nat) (hij : i < j) (hj : j < len r),
            (vals r)[i]'(Nat.lt_trans hij hj) ≠ (vals r)[j]'hj) := by
    sorry

  /-- For every i with 0 <= i < len(r), occ(vals(r)[i], head) = 1: every value that appears in the returned list r occurs exactly once in head.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_6 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        ∀ (i : Nat) (hi : i < len r), occ ((vals r)[i]'hi) head = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          ∀ (i : Nat) (hi : i < len r), occ ((vals r)[i]'hi) head = 1) := by
    sorry

  /-- For every integer v, if occ(v, head) = 1 then occ(v, r) = 1: every value that occurs exactly once in head appears exactly once in the returned list r.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_7 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        ∀ v : ℤ, occ v head = 1 → occ v r = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          ∀ v : ℤ, occ v head = 1 → occ v r = 1) := by
    sorry

  /-- For every integer v, if occ(v, head) >= 2 then occ(v, r) = 0: every value that occurs more than once in head is completely removed from the returned list r.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_8 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        ∀ v : ℤ, 2 ≤ occ v head → occ v r = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          ∀ v : ℤ, 2 ≤ occ v head → occ v r = 0) := by
    sorry

  /-- vals(r) is a subsequence of vals(head): there exist indices 0 <= i_0 < i_1 < ... < i_{len(r)-1} < len(head) such that vals(r)[k] = vals(head)[i_k] for every k with 0 <= k < len(r). (The condition is vacuous when len(r) = 0.)
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_9 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        IsSubsequence (vals r) (vals head) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          IsSubsequence (vals r) (vals head)) := by
    sorry

  /-- len(r) = the number of indices i with 0 <= i < len(head) and occ(vals(head)[i], head) = 1: the length of r equals the number of positions in head whose value occurs exactly once in head.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_10 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        len r = (uniqueVals head).length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          len r = (uniqueVals head).length) := by
    sorry

  /-- If len(head) = 0 then len(r) = 0 (r is Nil).
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_11 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        (len head = 0 → len r = 0 ∧ r = Aegis.DeleteDuplicates.List.Nil) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          (len head = 0 → len r = 0 ∧ r = Aegis.DeleteDuplicates.List.Nil)) := by
    sorry

  /-- If len(head) = 1 then len(r) = 1 and vals(r)[0] = vals(head)[0].
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_12 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        (len head = 1 → len r = 1 ∧ (vals r)[0]! = (vals head)[0]!) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          (len head = 1 → len r = 1 ∧ (vals r)[0]! = (vals head)[0]!)) := by
    sorry

  /-- If every value of head occurs exactly once in head (i.e., for every i with 0 <= i < len(head), occ(vals(head)[i], head) = 1), then vals(r) = vals(head).
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_13 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        ((∀ (i : Nat) (hi : i < len head), occ ((vals head)[i]'hi) head = 1) →
          vals r = vals head) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          ((∀ (i : Nat) (hi : i < len head), occ ((vals head)[i]'hi) head = 1) →
            vals r = vals head)) := by
    sorry

  /-- len(r) = 0 if and only if for every i with 0 <= i < len(head), occ(vals(head)[i], head) >= 2. Equivalently, the returned list is empty exactly when head is empty or every value of head is repeated.
    Preconditions: head is a sorted (non-decreasing) linked list with all values in [-100, 100]. -/
  theorem spec_14 (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
      (hb : inBounds head) :
      ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
        (len r = 0 ↔ ∀ (i : Nat) (hi : i < len head), 2 ≤ occ ((vals head)[i]'hi) head) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (head : Aegis.DeleteDuplicates.List) (hs : nonDecreasing head)
        (hb : inBounds head), ∃ r, Aegis.DeleteDuplicates.delete_duplicates head = ok r ∧
          (len r = 0 ↔ ∀ (i : Nat) (hi : i < len head), 2 ≤ occ ((vals head)[i]'hi) head)) := by
    sorry

  end AegisSpec.DeleteDuplicates
