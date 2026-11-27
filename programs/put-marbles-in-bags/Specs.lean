import Aegis.PutMarbles.Code.Funs

/-!
# Specifications of `Aegis.PutMarbles.put_marbles`

LeetCode problem `put-marbles-in-bags`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PutMarbles

namespace AegisSpec.PutMarbles

def vals (w : Slice Std.I64) : List ℤ := w.val.map (fun x => x.val)

def Bounded (w : Slice Std.I64) : Prop :=
  ∀ v ∈ vals w, 1 ≤ v ∧ v ≤ 1000000000

def ValidInput (w : Slice Std.I64) (k : Std.I64) : Prop :=
  1 ≤ w.val.length ∧ w.val.length ≤ 100000 ∧
    1 ≤ k.val ∧ k.val ≤ (w.val.length : ℤ) ∧ Bounded w

def mOfK (k : Std.I64) : ℕ := (k.val - 1).toNat

def pairSums (l : List ℤ) : List ℤ :=
  (l.zip (l.drop 1)).map (fun p => p.1 + p.2)

def endpointSum (l : List ℤ) : ℤ :=
  l.getD 0 0 + l.getD (l.length - 1) 0

def score (l : List ℤ) (C : Finset ℕ) : ℤ :=
  endpointSum l + C.sum (fun c => l.getD c 0 + l.getD (c + 1) 0)

def scoreSet (w : Slice Std.I64) (m : ℕ) : Finset ℤ :=
  Finset.image (score (vals w))
    (Finset.powersetCard m (Finset.range ((vals w).length - 1)))

def maxScore (w : Slice Std.I64) (k : Std.I64) : ℤ :=
  WithBot.unbotD 0 (scoreSet w (mOfK k)).max

def minScore (w : Slice Std.I64) (k : Std.I64) : ℤ :=
  WithTop.untopD 0 (scoreSet w (mOfK k)).min

def listMax : List ℤ → ℤ
  | [] => 0
  | a :: t => t.foldl (fun x y => max x y) a

def listMin : List ℤ → ℤ
  | [] => 0
  | a :: t => t.foldl (fun x y => min x y) a

def pairMax (l : List ℤ) : ℤ := listMax (pairSums l)

def pairMin (l : List ℤ) : ℤ := listMin (pairSums l)

def sumLargest (l : List ℤ) (m : ℕ) : ℤ :=
  ((l.mergeSort (fun a b => b ≤ a)).take m).sum

def sumSmallest (l : List ℤ) (m : ℕ) : ℤ :=
  ((l.mergeSort (fun a b => a ≤ b)).take m).sum

/-- Let n = len(weights). For any subset C of {0, 1, ..., n-2} with |C| = k-1, define score(C) = weights[0] + weights[n-1] + sum_{c in C} (weights[c] + weights[c+1]). (If n = 1, the set {0, ..., n-2} is empty; the only such C is the empty set, and score(empty) = weights[0] + weights[0].) Let maxScore = max_{C} score(C) and minScore = min_{C} score(C), where C ranges over all subsets of {0, ..., n-2} with |C| = k-1. The function returns a result r and r = maxScore - minScore.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_1 (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k) :
    ∃ r, put_marbles w k = ok r ∧ r.val = maxScore w k - minScore w k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k), ∃ r, put_marbles w k = ok r ∧ r.val = maxScore w k - minScore w k) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_2 (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k) :
    ∀ r, put_marbles w k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k), ∀ r, put_marbles w k = ok r → 0 ≤ r.val) := by
  sorry

/-- Let n = len(weights) and let P be the multiset of adjacent pair sums P = { weights[i] + weights[i+1] : 0 <= i < n-1 }. Define SumLargest(P, m) as the sum of the m largest elements of P (with multiplicity), and 0 if m = 0. Define SumSmallest(P, m) as the sum of the m smallest elements of P (with multiplicity), and 0 if m = 0. The function returns a result r and r = SumLargest(P, k-1) - SumSmallest(P, k-1).
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_3 (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k) :
    ∃ r, put_marbles w k = ok r ∧
      r.val = sumLargest (pairSums (vals w)) (mOfK k) -
        sumSmallest (pairSums (vals w)) (mOfK k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k), ∃ r, put_marbles w k = ok r ∧
      r.val = sumLargest (pairSums (vals w)) (mOfK k) -
        sumSmallest (pairSums (vals w)) (mOfK k)) := by
  sorry

/-- For every weights and k satisfying the preconditions, the function returns a result (it does not fail, panic, or overflow).
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_4 (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k) :
    ∃ r, put_marbles w k = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k), ∃ r, put_marbles w k = ok r) := by
  sorry

/-- If k = 1, the function returns r = 0.
  Preconditions: 1 <= len(weights) <= 100000; k = 1; for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_5 (w : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = 1) (hb : Bounded w) :
    ∃ r, put_marbles w k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = 1) (hb : Bounded w), ∃ r, put_marbles w k = ok r ∧ r.val = 0) := by
  sorry

/-- If k = len(weights), the function returns r = 0.
  Preconditions: 1 <= len(weights) <= 100000; k = len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_6 (w : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = (w.val.length : ℤ)) (hb : Bounded w) :
    ∃ r, put_marbles w k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = (w.val.length : ℤ)) (hb : Bounded w), ∃ r, put_marbles w k = ok r ∧ r.val = 0) := by
  sorry

/-- If k = 2, let M = max{ weights[i] + weights[i+1] : 0 <= i < len(weights)-1 } and m = min{ weights[i] + weights[i+1] : 0 <= i < len(weights)-1 }. Then the function returns r = M - m.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); k = 2; for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_7 (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k)
    (hk : k.val = 2) :
    ∃ r, put_marbles w k = ok r ∧ r.val = pairMax (vals w) - pairMin (vals w) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (h : ValidInput w k)
    (hk : k.val = 2), ∃ r, put_marbles w k = ok r ∧ r.val = pairMax (vals w) - pairMin (vals w)) := by
  sorry

/-- If len(weights) >= 2 and k = len(weights) - 1, let M and m be as in spec_7. Then the function returns r = M - m.
  Preconditions: len(weights) >= 2; len(weights) <= 100000; k = len(weights) - 1; for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_8 (w : Slice Std.I64) (k : Std.I64)
    (hn : 2 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = (w.val.length : ℤ) - 1) (hb : Bounded w) :
    ∃ r, put_marbles w k = ok r ∧ r.val = pairMax (vals w) - pairMin (vals w) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64)
    (hn : 2 ≤ w.val.length) (hn' : w.val.length ≤ 100000)
    (hk : k.val = (w.val.length : ℤ) - 1) (hb : Bounded w), ∃ r, put_marbles w k = ok r ∧ r.val = pairMax (vals w) - pairMin (vals w)) := by
  sorry

/-- If weights[i] = c for every i with 0 <= i < len(weights), then the function returns r = 0.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); there exists c such that weights[i] = c for every i with 0 <= i < len(weights); for every i, 1 <= weights[i] <= 1000000000. -/
theorem spec_9 (w : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hc : ∀ v ∈ vals w, v = c) :
    ∃ r, put_marbles w k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hc : ∀ v ∈ vals w, v = c), ∃ r, put_marbles w k = ok r ∧ r.val = 0) := by
  sorry

/-- For any weights satisfying the preconditions, let weights' be the array defined by weights'[i] = weights[len(weights)-1-i] for 0 <= i < len(weights). Whenever the function returns r for (weights, k) and r' for (weights', k), we have r = r'.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_10 (w w' : Slice Std.I64) (k : Std.I64) (h : ValidInput w k)
    (hw' : vals w' = (vals w).reverse) :
    ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (w w' : Slice Std.I64) (k : Std.I64) (h : ValidInput w k)
    (hw' : vals w' = (vals w).reverse), ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val) := by
  sorry

/-- Let weights'[i] = weights[i] + c for every i. Whenever the function returns r for (weights, k) and r' for (weights', k), we have r = r'.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i, 1 <= weights[i] <= 1000000000; c is an integer such that 1 <= weights[i] + c <= 1000000000 for every i with 0 <= i < len(weights). -/
theorem spec_11 (w w' : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hc : ∀ v ∈ vals w, 1 ≤ v + c ∧ v + c ≤ 1000000000)
    (hw' : vals w' = (vals w).map (fun v => v + c)) :
    ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (w w' : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hc : ∀ v ∈ vals w, 1 ≤ v + c ∧ v + c ≤ 1000000000)
    (hw' : vals w' = (vals w).map (fun v => v + c)), ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val) := by
  sorry

/-- Let weights'[i] = c * weights[i] for every i. Whenever the function returns r for (weights, k) and r' for (weights', k), we have r' = c * r.
  Preconditions: 1 <= len(weights) <= 100000; 1 <= k <= len(weights); for every i, 1 <= weights[i] <= 1000000000; c is a positive integer such that 1 <= c * weights[i] <= 1000000000 for every i with 0 <= i < len(weights). -/
theorem spec_12 (w w' : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hcpos : 0 < c) (hc : ∀ v ∈ vals w, 1 ≤ c * v ∧ c * v ≤ 1000000000)
    (hw' : vals w' = (vals w).map (fun v => c * v)) :
    ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r'.val = c * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (w w' : Slice Std.I64) (k : Std.I64) (c : ℤ) (h : ValidInput w k)
    (hcpos : 0 < c) (hc : ∀ v ∈ vals w, 1 ≤ c * v ∧ c * v ≤ 1000000000)
    (hw' : vals w' = (vals w).map (fun v => c * v)), ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r'.val = c * r.val) := by
  sorry

/-- Let M = max{ weights[i] + weights[i+1] : 0 <= i < len(weights)-1 } and m = min{ weights[i] + weights[i+1] : 0 <= i < len(weights)-1 }. Whenever the function returns a result r, r <= (k-1) * (M - m).
  Preconditions: 1 <= len(weights) <= 100000; len(weights) >= 2; 1 <= k <= len(weights); for every i with 0 <= i < len(weights), 1 <= weights[i] <= 1000000000. -/
theorem spec_13 (w : Slice Std.I64) (k : Std.I64) (hn : 2 ≤ w.val.length)
    (h : ValidInput w k) :
    ∀ r, put_marbles w k = ok r →
      r.val ≤ (k.val - 1) * (pairMax (vals w) - pairMin (vals w)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (w : Slice Std.I64) (k : Std.I64) (hn : 2 ≤ w.val.length)
    (h : ValidInput w k), ∀ r, put_marbles w k = ok r →
      r.val ≤ (k.val - 1) * (pairMax (vals w) - pairMin (vals w))) := by
  sorry

/-- Whenever the function returns r for (weights, k) and r' for (weights', k), we have r = r'.
  Preconditions: weights and weights' are arrays of the same length n with 1 <= n <= 100000 and 1 <= k <= n; for every i with 0 <= i < n, 1 <= weights[i] <= 1000000000 and 1 <= weights'[i] <= 1000000000; and the multisets { weights[i] + weights[i+1] : 0 <= i < n-1 } and { weights'[i] + weights'[i+1] : 0 <= i < n-1 } are equal. -/
theorem spec_14 (w w' : Slice Std.I64) (k : Std.I64)
    (h : ValidInput w k) (h' : ValidInput w' k)
    (hms : (pairSums (vals w) : Multiset ℤ) = (pairSums (vals w') : Multiset ℤ)) :
    ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (w w' : Slice Std.I64) (k : Std.I64)
    (h : ValidInput w k) (h' : ValidInput w' k)
    (hms : (pairSums (vals w) : Multiset ℤ) = (pairSums (vals w') : Multiset ℤ)), ∀ r r', put_marbles w k = ok r → put_marbles w' k = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.PutMarbles
