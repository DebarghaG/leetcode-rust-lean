import Aegis.GetWinner.Code.Funs

/-!
# Specifications of `Aegis.GetWinner.get_winner`

LeetCode problem `find-the-winner-of-an-array-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GetWinner

namespace AegisSpec.GetWinner

def lget (l : List I64) (i : Nat) : Int := (l.getD i 0#i64).val

def IsListMax (l : List I64) (m : I64) : Prop :=
  m ∈ l ∧ ∀ x, x ∈ l → x.val ≤ m.val

def roundStep (s : List I64 × I64 × Int) : List I64 × I64 × Int :=
  match s.1 with
  | x :: y :: rest =>
      let z : I64 := if y.val ≤ x.val then x else y
      let lo : I64 := if y.val ≤ x.val then y else x
      if z = s.2.1 then (z :: (rest ++ [lo]), s.2.1, s.2.2 + 1)
      else (z :: (rest ++ [lo]), z, 1)
  | _ => s

def procState (l : List I64) (t : Nat) : List I64 × I64 × Int :=
  roundStep^[t] (l, l.getD 0 0#i64, 0)

def IsPrefixMax (l : List I64) (i : Nat) : Prop :=
  i < l.length ∧ ∀ (j : Nat), j < i → lget l j < lget l i

def firstGreater (l : List I64) (i : Nat) : Option Nat :=
  List.find?
    (fun p => decide (i < p) && decide (p < l.length) && decide (lget l i < lget l p))
    (List.range (l.length + 1))

def runLen (l : List I64) (i : Nat) : Option Nat :=
  match firstGreater l i with
  | some p => some (if i = 0 then p - 1 else p - i)
  | none => none

def RunGe (l : List I64) (i : Nat) (k : Int) : Prop :=
  match runLen l i with
  | some m => k ≤ (m : Int)
  | none => True

/-- Whenever the function returns a result r, r is the unique integer declared winner by the following deterministic process. A position consists of a list q of the same integers as arr, a champion c, and a count w. Initially q=arr, c=arr[0], w=0. In each round, let x=q[0] and y=q[1], and let z be the larger of x and y. Replace q by the list whose first element is z, followed by q[2], q[3], ..., q[len(q)-1] (this middle part is empty when len(q)=2), followed by the smaller of x and y. If z=c then set w=w+1; otherwise set c=z and w=1. The first round at which w=k declares its current c to be the winner; r is that c. This process reaches such a declaration under the preconditions.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_1 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (t : Nat) (_ht : 1 ≤ t),
          (procState arr.val t).2.2 = k.val ∧
            (∀ (t' : Nat), t' < t → (procState arr.val t').2.2 ≠ k.val) ∧
              r = (procState arr.val t).2.1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (t : Nat) (_ht : 1 ≤ t),
          (procState arr.val t).2.2 = k.val ∧
            (∀ (t' : Nat), t' < t → (procState arr.val t').2.2 ≠ k.val) ∧
              r = (procState arr.val t).2.1) := by
  sorry

/-- For every arr and k satisfying the preconditions, the function returns a result r and does not fail, panic, perform an out-of-bounds access, or overflow.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_2 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ r : I64, get_winner arr k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∃ r : I64, get_winner arr k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = max(arr[0], arr[1]).
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, 1 <= k <= 1000000000, and k=1. -/
theorem spec_3 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) (hk1 : k.val = 1) :
    ∀ r : I64, get_winner arr k = ok r → r.val = max (arr.val[0]).val (arr.val[1]).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) (hk1 : k.val = 1), ∀ r : I64, get_winner arr k = ok r → r.val = max (arr.val[0]).val (arr.val[1]).val) := by
  sorry

/-- Whenever the function returns a result r, r = arr[0].
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, 1 <= k <= 1000000000, and arr[0] > arr[i] for every i with 0 < i < len(arr). -/
theorem spec_4 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h0max : ∀ (i : Nat) (hi0 : 0 < i) (hi : i < arr.val.length),
      (arr.val[i]).val < (arr.val[0]).val) :
    ∀ r : I64, get_winner arr k = ok r → r.val = (arr.val[0]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h0max : ∀ (i : Nat) (hi0 : 0 < i) (hi : i < arr.val.length),
      (arr.val[i]).val < (arr.val[0]).val), ∀ r : I64, get_winner arr k = ok r → r.val = (arr.val[0]).val) := by
  sorry

/-- Whenever the function returns a result r, r equals the maximum element of arr.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, 1 <= k <= 1000000000, and k >= len(arr) - 1. -/
theorem spec_5 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (hklen : (arr.val.length : Int) - 1 ≤ k.val) :
    ∀ r : I64, get_winner arr k = ok r → IsListMax arr.val r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (hklen : (arr.val.length : Int) - 1 ≤ k.val), ∀ r : I64, get_winner arr k = ok r → IsListMax arr.val r) := by
  sorry

/-- Whenever the function returns a result r, r >= arr[0] and r >= arr[1].
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_6 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r → r.val ≥ (arr.val[0]).val ∧ r.val ≥ (arr.val[1]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r → r.val ≥ (arr.val[0]).val ∧ r.val ≥ (arr.val[1]).val) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(arr) such that arr[i] = r.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_7 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (_hi : i < arr.val.length), (arr.val[i]).val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (_hi : i < arr.val.length), (arr.val[i]).val = r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(arr) such that arr[i] = r and, for every j with 0 <= j < i, arr[j] < r.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_8 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (hi : i < arr.val.length),
          (arr.val[i]).val = r.val ∧
            ∀ (j : Nat) (hj : j < i), (arr.val[j]).val < r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (hi : i < arr.val.length),
          (arr.val[i]).val = r.val ∧
            ∀ (j : Nat) (hj : j < i), (arr.val[j]).val < r.val) := by
  sorry

/-- Whenever the function returns a result r, let i be the unique index with arr[i]=r and let m be the unique index with arr[m] equal to the maximum element of arr. If r is not the maximum element of arr, then i < m.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_9 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        ∀ (m : Nat) (hm : m < arr.val.length),
          IsListMax arr.val arr.val[m] →
            r.val ≠ (arr.val[m]).val →
              ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val = r.val → i < m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        ∀ (m : Nat) (hm : m < arr.val.length),
          IsListMax arr.val arr.val[m] →
            r.val ≠ (arr.val[m]).val →
              ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val = r.val → i < m) := by
  sorry

/-- For every two integers k1 and k2 with 1 <= k1 <= k2 <= 1000000000, if the function returns r1 on (arr, k1) and r2 on (arr, k2), and i1, i2 are the unique indices with arr[i1]=r1 and arr[i2]=r2, then i1 <= i2.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k1 <= k2 <= 1000000000. -/
theorem spec_10 (arr : Slice I64) (k1 k2 : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000) :
    ∀ (r1 r2 : I64),
      get_winner arr k1 = ok r1 →
        get_winner arr k2 = ok r2 →
          ∀ (i1 : Nat) (h1 : i1 < arr.val.length) (i2 : Nat) (h2 : i2 < arr.val.length),
            (arr.val[i1]).val = r1.val → (arr.val[i2]).val = r2.val → i1 ≤ i2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice I64) (k1 k2 : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000), ∀ (r1 r2 : I64),
      get_winner arr k1 = ok r1 →
        get_winner arr k2 = ok r2 →
          ∀ (i1 : Nat) (h1 : i1 < arr.val.length) (i2 : Nat) (h2 : i2 < arr.val.length),
            (arr.val[i1]).val = r1.val → (arr.val[i2]).val = r2.val → i1 ≤ i2) := by
  sorry

/-- Whenever the function returns a result r, r = arr[0] if and only if either (1) arr[i] < arr[0] for every i with 0 < i < len(arr), or (2) there exists an index p with 0 < p < len(arr) such that arr[p] > arr[0], arr[i] < arr[0] for every i with 0 < i < p, and k <= p - 1.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_11 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        (r.val = (arr.val[0]).val ↔
          ((∀ (i : Nat) (hi0 : 0 < i) (hi : i < arr.val.length),
              (arr.val[i]).val < (arr.val[0]).val) ∨
            ∃ (p : Nat) (hp : p < arr.val.length),
              0 < p ∧ (arr.val[0]).val < (arr.val[p]).val ∧
                (∀ (i : Nat) (hi0 : 0 < i) (hi : i < p),
                  (arr.val[i]).val < (arr.val[0]).val) ∧
                  k.val ≤ (p : Int) - 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        (r.val = (arr.val[0]).val ↔
          ((∀ (i : Nat) (hi0 : 0 < i) (hi : i < arr.val.length),
              (arr.val[i]).val < (arr.val[0]).val) ∨
            ∃ (p : Nat) (hp : p < arr.val.length),
              0 < p ∧ (arr.val[0]).val < (arr.val[p]).val ∧
                (∀ (i : Nat) (hi0 : 0 < i) (hi : i < p),
                  (arr.val[i]).val < (arr.val[0]).val) ∧
                  k.val ≤ (p : Int) - 1))) := by
  sorry

/-- Whenever the function returns a result r, r = arr[len(arr)-1].
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, 1 <= k <= 1000000000, k >= 2, and arr[i] < arr[i+1] for every i with 0 <= i < len(arr)-1. -/
theorem spec_12 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) (hk2 : 2 ≤ k.val)
    (hinc : ∀ (i : Nat) (hi : i + 1 < arr.val.length),
      (arr.val[i]).val < (arr.val[i + 1]).val) :
    ∀ r : I64, get_winner arr k = ok r → r.val = (arr.val[arr.val.length - 1]).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) (hk2 : 2 ≤ k.val)
    (hinc : ∀ (i : Nat) (hi : i + 1 < arr.val.length),
      (arr.val[i]).val < (arr.val[i + 1]).val), ∀ r : I64, get_winner arr k = ok r → r.val = (arr.val[arr.val.length - 1]).val) := by
  sorry

/-- For any valid array arr' with len(arr') >= 2, pairwise distinct elements between 1 and 1000000, arr'[0]=arr[0], and arr'[1]=arr[1], if the function returns r on (arr,1) and r' on (arr',1), then r=r'.
  Preconditions: arr and arr' are arrays with 2 <= len(arr) <= 100000 and 2 <= len(arr') <= 100000, every element of each is an integer between 1 and 1000000, the elements of each array are pairwise distinct, arr'[0]=arr[0], arr'[1]=arr[1], and k=1. -/
theorem spec_13 (arr arr' : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hlen2' : 2 ≤ arr'.val.length) (hlen' : arr'.val.length ≤ 100000)
    (hrange' : ∀ (i : Nat) (hi : i < arr'.val.length),
      1 ≤ (arr'.val[i]).val ∧ (arr'.val[i]).val ≤ 1000000)
    (hnodup' : arr'.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h0 : (arr'.val[0]).val = (arr.val[0]).val)
    (h1 : (arr'.val[1]).val = (arr.val[1]).val)
    (hk1 : k.val = 1) :
    ∀ (r r' : I64), get_winner arr k = ok r → get_winner arr' k = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr arr' : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hlen2' : 2 ≤ arr'.val.length) (hlen' : arr'.val.length ≤ 100000)
    (hrange' : ∀ (i : Nat) (hi : i < arr'.val.length),
      1 ≤ (arr'.val[i]).val ∧ (arr'.val[i]).val ≤ 1000000)
    (hnodup' : arr'.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h0 : (arr'.val[0]).val = (arr.val[0]).val)
    (h1 : (arr'.val[1]).val = (arr.val[1]).val)
    (hk1 : k.val = 1), ∀ (r r' : I64), get_winner arr k = ok r → get_winner arr' k = ok r' → r = r') := by
  sorry

/-- Call an index i a prefix maximum if arr[i] > arr[j] for every 0 <= j < i. For such i, define run(i) as follows. Let p be the least index with i < p < len(arr) and arr[p] > arr[i], if it exists. If i=0 and such p exists, run(0)=p-1; if i>0 and such p exists, run(i)=p-i; if no such p exists, then arr[i] is the global maximum and run(i) is unbounded above every allowed k. Whenever the function returns a result r, r = arr[i] for the least prefix-maximum index i with run(i) >= k. This gives an equivalent non-simulating characterization of the answer.
  Preconditions: len(arr) >= 2, len(arr) <= 100000, every element of arr is an integer with 1 <= arr[i] <= 1000000, the elements of arr are pairwise distinct, and 1 <= k <= 1000000000. -/
theorem spec_14 (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (hi : i < arr.val.length),
          IsPrefixMax arr.val i ∧ RunGe arr.val i k.val ∧
            (∀ (j : Nat), j < i → ¬(IsPrefixMax arr.val j ∧ RunGe arr.val j k.val)) ∧
              r = arr.val[i] := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice I64) (k : I64)
    (hlen2 : 2 ≤ arr.val.length) (hlen : arr.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < arr.val.length),
      1 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000)
    (hnodup : arr.val.Nodup)
    (hk : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∀ r : I64,
      get_winner arr k = ok r →
        ∃ (i : Nat) (hi : i < arr.val.length),
          IsPrefixMax arr.val i ∧ RunGe arr.val i k.val ∧
            (∀ (j : Nat), j < i → ¬(IsPrefixMax arr.val j ∧ RunGe arr.val j k.val)) ∧
              r = arr.val[i]) := by
  sorry

end AegisSpec.GetWinner
