import Aegis.PairSum.Code.Funs

/-!
# Specifications of `Aegis.PairSum.pair_sum`

LeetCode problem `maximum-twin-sum-of-a-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PairSum

def vals (head : Aegis.PairSum.List) : List ℤ :=
  match head with
  | .Nil => []
  | .Cons v next => v.val :: vals next

def nthVal (l : List ℤ) (i : Nat) : ℤ := l.getD i 0

def ValuesInRange (l : List ℤ) : Prop :=
  ∀ i, i < l.length → 1 ≤ nthVal l i ∧ nthVal l i ≤ 100000

def frontVals (l : List ℤ) : List ℤ :=
  (List.range (l.length / 2)).map fun i => nthVal l i

def twinVals (l : List ℤ) : List ℤ :=
  (List.range (l.length / 2)).map fun i => nthVal l (l.length - 1 - i)

def twinSums (l : List ℤ) : List ℤ :=
  (List.range (l.length / 2)).map fun i => nthVal l i + nthVal l (l.length - 1 - i)

def maxOf : List ℤ → ℤ
  | [] => 0
  | a :: t => t.foldl (fun acc b => max acc b) a

def minOf : List ℤ → ℤ
  | [] => 0
  | a :: t => t.foldl (fun acc b => min acc b) a

def SortedDesc (l : List ℤ) : Prop := List.Pairwise (fun a b => b ≤ a) l

/-- Whenever pair_sum(head) returns a result r, r equals the maximum, over all integers i with 0 <= i < n/2, of v_i + v_{n-1-i}. Here n/2 is integer division; for each i < n/2, node i and node n-1-i are twins.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_1 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val = maxOf (twinSums (vals head)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val = maxOf (twinSums (vals head))) := by
  sorry

/-- pair_sum(head) returns a result r; it does not fail, panic, or return an error value.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_2 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∃ r, Aegis.PairSum.pair_sum head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∃ r, Aegis.PairSum.pair_sum head = ok r) := by
  sorry

/-- Whenever pair_sum(head) returns a result r, for every integer i with 0 <= i < n/2, we have r >= v_i + v_{n-1-i}.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_3 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∀ i, i < (vals head).length / 2 →
        r.val ≥ nthVal (vals head) i + nthVal (vals head) ((vals head).length - 1 - i) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∀ i, i < (vals head).length / 2 →
        r.val ≥ nthVal (vals head) i + nthVal (vals head) ((vals head).length - 1 - i)) := by
  sorry

/-- Whenever pair_sum(head) returns a result r, there exists an integer k with 0 <= k < n/2 such that r = v_k + v_{n-1-k}.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_4 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∃ k, k < (vals head).length / 2 ∧
        r.val = nthVal (vals head) k + nthVal (vals head) ((vals head).length - 1 - k) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∃ k, k < (vals head).length / 2 ∧
        r.val = nthVal (vals head) k + nthVal (vals head) ((vals head).length - 1 - k)) := by
  sorry

/-- Whenever pair_sum(head) returns a result r, 2*m <= r <= 2*M.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. Let m = min_{0 <= i < n} v_i and M = max_{0 <= i < n} v_i. -/
theorem spec_5 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      2 * minOf (vals head) ≤ r.val ∧ r.val ≤ 2 * maxOf (vals head) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      2 * minOf (vals head) ≤ r.val ∧ r.val ≤ 2 * maxOf (vals head)) := by
  sorry

/-- Whenever pair_sum(head) returns a result r and pair_sum(head') returns a result r', we have r = r'.
  Preconditions: Let head and head' be two linked lists, each with the same length n, where n is even, 2 <= n <= 100000. Let v_i and v'_i be their i-th node values (0-indexed). Assume 1 <= v_i <= 100000 and 1 <= v'_i <= 100000 for every 0 <= i < n. Assume that for every integer i with 0 <= i < n/2, v_i + v_{n-1-i} = v'_i + v'_{n-1-i}. -/
theorem spec_6 (head head' : Aegis.PairSum.List)
    (hLen : (vals head).length = (vals head').length)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head))
    (hRange' : ValuesInRange (vals head'))
    (hSums : ∀ i, i < (vals head).length / 2 →
      nthVal (vals head) i + nthVal (vals head) ((vals head).length - 1 - i) =
        nthVal (vals head') i + nthVal (vals head') ((vals head').length - 1 - i)) :
    ∀ r r', Aegis.PairSum.pair_sum head = ok r →
      Aegis.PairSum.pair_sum head' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head head' : Aegis.PairSum.List)
    (hLen : (vals head).length = (vals head').length)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head))
    (hRange' : ValuesInRange (vals head'))
    (hSums : ∀ i, i < (vals head).length / 2 →
      nthVal (vals head) i + nthVal (vals head) ((vals head).length - 1 - i) =
        nthVal (vals head') i + nthVal (vals head') ((vals head').length - 1 - i)), ∀ r r', Aegis.PairSum.pair_sum head = ok r →
      Aegis.PairSum.pair_sum head' = ok r' → r = r') := by
  sorry

/-- Whenever pair_sum(head) returns a result r, r <= a + b.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. Let a = max_{0 <= i < n/2} v_i and b = max_{0 <= i < n/2} v_{n-1-i}. -/
theorem spec_7 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val ≤ maxOf (frontVals (vals head)) + maxOf (twinVals (vals head)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val ≤ maxOf (frontVals (vals head)) + maxOf (twinVals (vals head))) := by
  sorry

/-- Whenever pair_sum(head) returns a result r, r >= a + b.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. Let a = min_{0 <= i < n/2} v_i and b = min_{0 <= i < n/2} v_{n-1-i}. -/
theorem spec_8 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val ≥ minOf (frontVals (vals head)) + minOf (twinVals (vals head)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      r.val ≥ minOf (frontVals (vals head)) + minOf (twinVals (vals head))) := by
  sorry

/-- Whenever pair_sum(head) returns a result r, r <= w_1 + w_2.
  Preconditions: Let n = len(head), and let v_i be the value in the i-th node of head (0-indexed from the head). Assume n is even, 2 <= n <= 100000, and 1 <= v_i <= 100000 for every i with 0 <= i < n. Let w_1 >= w_2 >= ... >= w_n be the values v_0,...,v_{n-1} sorted in non-increasing order, with multiplicity. -/
theorem spec_9 (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)) :
    ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∀ (ws : List ℤ) (w1 w2 : ℤ) (rest : List ℤ),
        ws = w1 :: w2 :: rest →
          List.Perm (vals head) ws → SortedDesc ws → r.val ≤ w1 + w2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.PairSum.List)
    (hEven : (vals head).length % 2 = 0)
    (hGe : 2 ≤ (vals head).length)
    (hLe : (vals head).length ≤ 100000)
    (hRange : ValuesInRange (vals head)), ∀ r, Aegis.PairSum.pair_sum head = ok r →
      ∀ (ws : List ℤ) (w1 w2 : ℤ) (rest : List ℤ),
        ws = w1 :: w2 :: rest →
          List.Perm (vals head) ws → SortedDesc ws → r.val ≤ w1 + w2) := by
  sorry

end AegisSpec.PairSum
