import Aegis.HighFive.Code.Funs

/-!
# Specifications of `Aegis.HighFive.high_five`

LeetCode problem `high-five`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.HighFive (high_five)

namespace AegisSpec.HighFive

abbrev IVec : Type := alloc.vec.Vec I64

abbrev OVec : Type := alloc.vec.Vec IVec

def idOf (v : IVec) : Option Int := (v.val[0]?).map (fun x => x.val)

def scoreOf (v : IVec) : Option Int := (v.val[1]?).map (fun x => x.val)

def entryLen (l : List IVec) (j : Nat) : Option Nat := (l[j]?).map (fun v => v.val.length)

def entryId (l : List IVec) (j : Nat) : Option Int := (l[j]?).bind idOf

def entryScore (l : List IVec) (j : Nat) : Option Int := (l[j]?).bind scoreOf

def idLt (l : List IVec) (i j : Nat) : Prop :=
  ∃ a b, entryId l i = some a ∧ entryId l j = some b ∧ a < b

def countId (l : List IVec) (d : Int) : Nat := (l.filter (fun v => idOf v = some d)).length

def scores (l : List IVec) (d : Int) : List Int :=
  l.filterMap (fun v => if idOf v = some d then scoreOf v else none)

def top5sum (l : List IVec) (d : Int) : Int :=
  (((scores l d).mergeSort (fun a b => b ≤ a)).take 5).sum

def top5avg (l : List IVec) (d : Int) : Int := top5sum l d / 5

def idsOf (l : List IVec) : List Int :=
  (l.filterMap idOf).eraseDups.mergeSort (fun a b => a ≤ b)

def numDistinctIds (l : List IVec) : Nat := (l.filterMap idOf).eraseDups.length

def scoreSum (l : List IVec) (s : Finset (Fin l.length)) : Int :=
  ∑ i ∈ s, (scoreOf (l.get i)).getD 0

def IsTop5Choice (l : List IVec) (d : Int) (s : Finset (Fin l.length)) : Prop :=
  s.card = 5 ∧ ∀ i ∈ s, idOf (l.get i) = some d

def Pre (items : Slice IVec) : Prop :=
  1 ≤ items.val.length ∧
  items.val.length ≤ 1000 ∧
  (∀ i, i < items.val.length → entryLen items.val i = some 2) ∧
  (∀ i, i < items.val.length → ∀ d, entryId items.val i = some d → 1 ≤ d ∧ d ≤ 1000) ∧
  (∀ i, i < items.val.length → ∀ s, entryScore items.val i = some s → 0 ≤ s ∧ s ≤ 100) ∧
  (∀ d, (∃ i, i < items.val.length ∧ entryId items.val i = some d) → 5 ≤ countId items.val d)

/-- Let scores(items,d) be the list of all items[i][1] such that 0 <= i < len(items) and items[i][0] = d. Let top5sum(items,d) be the sum of the five largest elements of scores(items,d), counting multiplicities; equivalently, the maximum over all choices of five pairwise distinct indices i1,...,i5 with items[ik][0] = d of items[i1][1]+...+items[i5][1]. Let top5avg(items,d) = top5sum(items,d) / 5 using integer division (floor, since top5sum(items,d) >= 0). For every items satisfying the preconditions, whenever high_five(items) returns a result r, let ids be the list of distinct IDs occurring in items sorted in strictly increasing order. Then len(r) = len(ids), and for every j with 0 <= j < len(r), len(r[j]) = 2, r[j][0] = ids[j], and r[j][1] = top5avg(items, ids[j]).
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_1 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    r.val.length = (idsOf items.val).length ∧
      ∀ j, j < r.val.length →
        entryLen r.val j = some 2 ∧
          entryId r.val j = (idsOf items.val)[j]? ∧
            entryScore r.val j = ((idsOf items.val)[j]?).map (top5avg items.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), r.val.length = (idsOf items.val).length ∧
      ∀ j, j < r.val.length →
        entryLen r.val j = some 2 ∧
          entryId r.val j = (idsOf items.val)[j]? ∧
            entryScore r.val j = ((idsOf items.val)[j]?).map (top5avg items.val)) := by
  sorry

/-- For every items satisfying the preconditions, high_five(items) returns a result r (it does not fail).
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_2 (items : Slice IVec) (hpre : Pre items) :
    ∃ r, high_five items = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items), ∃ r, high_five items = ok r) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2.
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_3 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ j, j < r.val.length → entryLen r.val j = some 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ j, j < r.val.length → entryLen r.val j = some 2) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every i and j with 0 <= i < j < len(r), len(r[i]) = 2 and len(r[j]) = 2 and r[i][0] < r[j][0].
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_4 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ i j, i < j → j < r.val.length →
      entryLen r.val i = some 2 ∧ entryLen r.val j = some 2 ∧ idLt r.val i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ i j, i < j → j < r.val.length →
      entryLen r.val i = some 2 ∧ entryLen r.val j = some 2 ∧ idLt r.val i j) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every integer d, (there exists j with 0 <= j < len(r) and len(r[j]) = 2 and r[j][0] = d) if and only if (there exists i with 0 <= i < len(items) and items[i][0] = d).
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_5 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ d : Int,
      (∃ j, j < r.val.length ∧ entryLen r.val j = some 2 ∧ entryId r.val j = some d) ↔
        (∃ i, i < items.val.length ∧ entryId items.val i = some d) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ d : Int,
      (∃ j, j < r.val.length ∧ entryLen r.val j = some 2 ∧ entryId r.val j = some d) ↔
        (∃ i, i < items.val.length ∧ entryId items.val i = some d)) := by
  sorry

/-- Define scores(items,d) as the list of all items[i][1] with 0 <= i < len(items) and items[i][0] = d. Define top5sum(items,d) as the maximum over all choices of five pairwise distinct indices i1,...,i5 with items[ik][0] = d of items[i1][1]+...+items[i5][1]. Define top5avg(items,d) = top5sum(items,d) / 5 using integer division (floor, since top5sum(items,d) >= 0). For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2, there exists i with 0 <= i < len(items) and items[i][0] = r[j][0], and r[j][1] = top5avg(items, r[j][0]).
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_6 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        (∃ i d, i < items.val.length ∧ entryId r.val j = some d ∧
          entryId items.val i = some d) ∧
          (∀ d, entryId r.val j = some d → entryScore r.val j = some (top5avg items.val d)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        (∃ i d, i < items.val.length ∧ entryId r.val j = some d ∧
          entryId items.val i = some d) ∧
          (∀ d, entryId r.val j = some d → entryScore r.val j = some (top5avg items.val d))) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2. Let d = r[j][0] and a = r[j][1]. Then: (a) there exist five pairwise distinct indices i1,...,i5 with 0 <= ik < len(items) and items[ik][0] = d for all k such that 5*a <= items[i1][1]+...+items[i5][1] <= 5*a+4; and (b) for every five pairwise distinct indices i1,...,i5 with 0 <= ik < len(items) and items[ik][0] = d for all k, items[i1][1]+...+items[i5][1] <= 5*a+4.
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_7 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ j, j < r.val.length → ∀ d a, entryId r.val j = some d → entryScore r.val j = some a →
      entryLen r.val j = some 2 ∧
        (∃ s : Finset (Fin items.val.length), IsTop5Choice items.val d s ∧
          5 * a ≤ scoreSum items.val s ∧ scoreSum items.val s ≤ 5 * a + 4) ∧
          (∀ s : Finset (Fin items.val.length), IsTop5Choice items.val d s →
            scoreSum items.val s ≤ 5 * a + 4) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ j, j < r.val.length → ∀ d a, entryId r.val j = some d → entryScore r.val j = some a →
      entryLen r.val j = some 2 ∧
        (∃ s : Finset (Fin items.val.length), IsTop5Choice items.val d s ∧
          5 * a ≤ scoreSum items.val s ∧ scoreSum items.val s ≤ 5 * a + 4) ∧
          (∀ s : Finset (Fin items.val.length), IsTop5Choice items.val d s →
            scoreSum items.val s ≤ 5 * a + 4)) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2 and 0 <= r[j][1] <= 100.
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_8 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        ∃ s : Int, entryScore r.val j = some s ∧ 0 ≤ s ∧ s ≤ 100 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        ∃ s : Int, entryScore r.val j = some s ∧ 0 ≤ s ∧ s ≤ 100) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2 and 1 <= r[j][0] <= 1000.
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_9 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        ∃ d : Int, entryId r.val j = some d ∧ 1 ≤ d ∧ d ≤ 1000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), ∀ j, j < r.val.length →
      entryLen r.val j = some 2 ∧
        ∃ d : Int, entryId r.val j = some d ∧ 1 ≤ d ∧ d ≤ 1000) := by
  sorry

/-- For every items satisfying the preconditions, whenever high_five(items) returns a result r, len(r) equals the number of distinct values among items[0][0], items[1][0], ..., items[len(items)-1][0].
  Preconditions: items is a slice of Vec<I64> with 1 <= len(items) <= 1000. For every i with 0 <= i < len(items), len(items[i]) = 2, 1 <= items[i][0] <= 1000, and 0 <= items[i][1] <= 100. For every distinct ID d that occurs as items[i][0] for some i, the number of indices i with items[i][0] = d is at least 5. -/
theorem spec_10 (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r) :
    r.val.length = numDistinctIds items.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (items : Slice IVec) (hpre : Pre items)
    (r : OVec) (hr : high_five items = ok r), r.val.length = numDistinctIds items.val) := by
  sorry

/-- For every such items and items', whenever high_five(items) returns a result r and high_five(items') returns a result r', we have r = r'.
  Preconditions: Both items and items' satisfy the common preconditions: each is a slice of Vec<I64> with 1 <= len <= 1000; every entry has length 2; IDs are in 1..1000; scores are in 0..100; and every occurring ID has at least five scores. Additionally, items' is a permutation of the entries of items (same length and same multiset of two-element vectors). -/
theorem spec_11 (items items' : Slice IVec) (hpre : Pre items) (hpre' : Pre items')
    (hperm : items.val.Perm items'.val)
    (r r' : OVec) (hr : high_five items = ok r) (hr' : high_five items' = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (items items' : Slice IVec) (hpre : Pre items) (hpre' : Pre items')
    (hperm : items.val.Perm items'.val)
    (r r' : OVec) (hr : high_five items = ok r) (hr' : high_five items' = ok r'), r = r') := by
  sorry

end AegisSpec.HighFive
