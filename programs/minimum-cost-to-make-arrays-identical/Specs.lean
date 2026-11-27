import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-make-arrays-identical`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinCost

namespace AegisSpec.MinCost

def BoundedVals (l : List I64) (lo hi : Int) : Prop :=
  ∀ i : Fin l.length, lo ≤ (l.get i).val ∧ (l.get i).val ≤ hi

def SortedVals (l : List I64) : Prop := l.Pairwise (fun x y => x.val ≤ y.val)

def absDiff (x y : I64) : Int := |x.val - y.val|

def absDiffSum : List I64 → List I64 → Int
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys => absDiff x y + absDiffSum xs ys

def D0 (arr brr : Slice I64) : Int := absDiffSum arr.val brr.val

noncomputable def permCostMin (arr brr : List I64) : Int :=
  (arr.permutations.map (fun l => absDiffSum l brr)).foldr min (absDiffSum arr brr)

noncomputable def Dmin (arr brr : Slice I64) : Int := permCostMin arr.val brr.val

def SimulPerm (a b a' b' : List I64) : Prop :=
  a'.length = a.length ∧ b'.length = b.length ∧ (a'.zip b').Perm (a.zip b)

def ValidInput (arr brr : Slice I64) (k : I64) : Prop :=
  arr.val.length = brr.val.length ∧
  1 ≤ arr.val.length ∧
  arr.val.length ≤ 100000 ∧
  0 ≤ k.val ∧
  k.val ≤ 20000000000 ∧
  BoundedVals arr.val (-100000) 100000 ∧
  BoundedVals brr.val (-100000) 100000

inductive Op where

  | rearrange (p q : List (List I64))

  | adjust (l : List I64)

inductive OpStep (k : Int) : List I64 → Op → List I64 → Int → Prop where
  | rearrange (l : List I64) (p q : List (List I64))
      (hjoin : p.flatten = l) (hne : ∀ b ∈ p, b ≠ []) (hperm : q.Perm p) :
      OpStep k l (.rearrange p q) q.flatten k
  | adjust (l l' : List I64) (hlen : l'.length = l.length) :
      OpStep k l (.adjust l') l' (absDiffSum l' l)

inductive Strategy (k : Int) : List I64 → Int → List I64 → Prop where
  | nil (l : List I64) : Strategy k l 0 l
  | step {l l' l'' : List I64} {op : Op} {c c' : Int} :
      OpStep k l op l' c → Strategy k l' c' l'' → Strategy k l (c + c') l''

/-- The function returns a result r such that r = min(D0, k + Dmin), where D0 = sum_{i=0}^{n-1} |arr[i] - brr[i]|, and Dmin = min over all bijections pi from {0,...,n-1} to itself of sum_{i=0}^{n-1} |arr[pi(i)] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_1 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∃ r, min_cost arr brr k = ok r ∧ r.val = min (D0 arr brr) (k.val + Dmin arr brr) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∃ r, min_cost arr brr k = ok r ∧ r.val = min (D0 arr brr) (k.val + Dmin arr brr)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail: no out-of-bounds access, no panic, and no i64 overflow).
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_2 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∃ r, min_cost arr brr k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∃ r, min_cost arr brr k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= Dmin, where Dmin = min over all bijections pi from {0,...,n-1} to itself of sum_{i=0}^{n-1} |arr[pi(i)] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_3 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r, min_cost arr brr k = ok r → Dmin arr brr ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r, min_cost arr brr k = ok r → Dmin arr brr ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= D0, where D0 = sum_{i=0}^{n-1} |arr[i] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_4 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r, min_cost arr brr k = ok r → r.val ≤ D0 arr brr := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r, min_cost arr brr k = ok r → r.val ≤ D0 arr brr) := by
  sorry

/-- Whenever the function returns a result r, r <= k + Dmin, where Dmin = min over all bijections pi from {0,...,n-1} to itself of sum_{i=0}^{n-1} |arr[pi(i)] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_5 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r, min_cost arr brr k = ok r → r.val ≤ k.val + Dmin arr brr := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r, min_cost arr brr k = ok r → r.val ≤ k.val + Dmin arr brr) := by
  sorry

/-- Whenever the function returns a result r, r = Dmin, where Dmin = min over all bijections pi from {0,...,n-1} to itself of sum_{i=0}^{n-1} |arr[pi(i)] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also k = 0. -/
theorem spec_6 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) (hk : k.val = 0) :
    ∀ r, min_cost arr brr k = ok r → r.val = Dmin arr brr := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) (hk : k.val = 0), ∀ r, min_cost arr brr k = ok r → r.val = Dmin arr brr) := by
  sorry

/-- Whenever the function returns a result r, r = D0.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also k >= D0, where D0 = sum_{i=0}^{n-1} |arr[i] - brr[i]|. -/
theorem spec_7 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hk : D0 arr brr ≤ k.val) :
    ∀ r, min_cost arr brr k = ok r → r.val = D0 arr brr := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hk : D0 arr brr ≤ k.val), ∀ r, min_cost arr brr k = ok r → r.val = D0 arr brr) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also arr[i] = brr[i] for every 0 <= i < n. -/
theorem spec_8 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hsame : arr.val = brr.val) :
    ∀ r, min_cost arr brr k = ok r → r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hsame : arr.val = brr.val), ∀ r, min_cost arr brr k = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = min(D0, k), where D0 = sum_{i=0}^{n-1} |arr[i] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also there exists a bijection pi from {0,...,n-1} to itself such that arr[pi(i)] = brr[i] for every 0 <= i < n (equivalently, arr is a permutation of brr). -/
theorem spec_9 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hperm : arr.val.Perm brr.val) :
    ∀ r, min_cost arr brr k = ok r → r.val = min (D0 arr brr) k.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hperm : arr.val.Perm brr.val), ∀ r, min_cost arr brr k = ok r → r.val = min (D0 arr brr) k.val) := by
  sorry

/-- Whenever the function returns a result r, r = D0, where D0 = sum_{i=0}^{n-1} |arr[i] - brr[i]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also arr[0] <= arr[1] <= ... <= arr[n-1] and brr[0] <= brr[1] <= ... <= brr[n-1]. -/
theorem spec_10 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hsa : SortedVals arr.val) (hsb : SortedVals brr.val) :
    ∀ r, min_cost arr brr k = ok r → r.val = D0 arr brr := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hsa : SortedVals arr.val) (hsb : SortedVals brr.val), ∀ r, min_cost arr brr k = ok r → r.val = D0 arr brr) := by
  sorry

/-- Let r1 be the value returned by min_cost(arr, brr, k) and r2 be the value returned by min_cost(brr, arr, k). Whenever both calls return, r1 = r2.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_11 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r1 r2, min_cost arr brr k = ok r1 → min_cost brr arr k = ok r2 → r1 = r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r1 r2, min_cost arr brr k = ok r1 → min_cost brr arr k = ok r2 → r1 = r2) := by
  sorry

/-- Whenever min_cost(arr, brr, k) returns r and min_cost(arr', brr', k) returns r', we have r = r'.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Let sigma be any bijection from {0,...,n-1} to itself. Define arr'[i] = arr[sigma(i)] and brr'[i] = brr[sigma(i)] for 0 <= i < n. -/
theorem spec_12 (arr brr arr' brr' : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hσ : SimulPerm arr.val brr.val arr'.val brr'.val) :
    ∀ r r', min_cost arr brr k = ok r → min_cost arr' brr' k = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr brr arr' brr' : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (hσ : SimulPerm arr.val brr.val arr'.val brr'.val), ∀ r r', min_cost arr brr k = ok r → min_cost arr' brr' k = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, r = |arr[0] - brr[0]|.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. Also n = 1. -/
theorem spec_13 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (x y : I64) (hx : arr.val = [x]) (hy : brr.val = [y]) :
    ∀ r, min_cost arr brr k = ok r → r.val = absDiff x y := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k)
    (x y : I64) (hx : arr.val = [x]) (hy : brr.val = [y]), ∀ r, min_cost arr brr k = ok r → r.val = absDiff x y) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of allowed operations (split the current array into contiguous subarrays and rearrange them at cost k per split; add or subtract a positive integer x from one element at cost x) that transforms arr into brr with total cost exactly r.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_14 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r, min_cost arr brr k = ok r → Strategy k.val arr.val r.val brr.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r, min_cost arr brr k = ok r → Strategy k.val arr.val r.val brr.val) := by
  sorry

/-- Whenever the function returns a result r, every finite sequence of allowed operations (split the current array into contiguous subarrays and rearrange them at cost k per split; add or subtract a positive integer x from one element at cost x) that transforms arr into brr has total cost at least r.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, 0 <= k <= 20000000000, and -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n. -/
theorem spec_15 (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k) :
    ∀ r, min_cost arr brr k = ok r → ∀ c : Int, Strategy k.val arr.val c brr.val → r.val ≤ c := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (arr brr : Slice I64) (k : I64) (h : ValidInput arr brr k), ∀ r, min_cost arr brr k = ok r → ∀ c : Int, Strategy k.val arr.val c brr.val → r.val ≤ c) := by
  sorry

/-- If min_cost(arr, brr, k1) returns r1 and min_cost(arr, brr, k2) returns r2, then r1 <= r2.
  Preconditions: Let n = len(arr). Then len(arr) = len(brr) = n, 1 <= n <= 100000, -100000 <= arr[i], brr[i] <= 100000 for every 0 <= i < n, and 0 <= k1 <= k2 <= 20000000000. -/
theorem spec_16 (arr brr : Slice I64) (k1 k2 : I64) (h1 : ValidInput arr brr k1)
    (h2 : ValidInput arr brr k2) (hk : k1.val ≤ k2.val) :
    ∀ r1 r2, min_cost arr brr k1 = ok r1 → min_cost arr brr k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (arr brr : Slice I64) (k1 k2 : I64) (h1 : ValidInput arr brr k1)
    (h2 : ValidInput arr brr k2) (hk : k1.val ≤ k2.val), ∀ r1 r2, min_cost arr brr k1 = ok r1 → min_cost arr brr k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

end AegisSpec.MinCost
