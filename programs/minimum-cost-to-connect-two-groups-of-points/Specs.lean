import Aegis.ConnectTwoGroups.Code.Funs

/-!
# Specifications of `Aegis.ConnectTwoGroups.connect_two_groups`

LeetCode problem `minimum-cost-to-connect-two-groups-of-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ConnectTwoGroups

namespace AegisSpec.ConnectTwoGroups

noncomputable section

open Classical

def entry (cost : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match cost.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def Rect (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  cost.val.length = m ∧ ∀ row ∈ cost.val, row.val.length = n

def EntriesInRange (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  ∀ i j, i < m → j < n → 0 ≤ entry cost i j ∧ entry cost i j ≤ 100

def IsConnSet (S : Finset (Nat × Nat)) (m n : Nat) : Prop :=
  (∀ p ∈ S, p.1 < m ∧ p.2 < n) ∧
    (∀ i, i < m → ∃ j, j < n ∧ (i, j) ∈ S) ∧
      ∀ j, j < n → ∃ i, i < m ∧ (i, j) ∈ S

def setCost (cost : Slice (alloc.vec.Vec Std.I64)) (S : Finset (Nat × Nat)) : Int :=
  S.sum (fun p => entry cost p.1 p.2)

def minUpTo (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | k + 1 => min (minUpTo f k) (f k)

def assignCost (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (g : Fin m → Fin n) : Int :=
  Finset.univ.sum (fun i : Fin m => entry cost i.val (g i).val) +
    (Finset.range n).sum (fun j =>
      if ∃ i : Fin m, (g i).val = j then 0 else minUpTo (fun i => entry cost i j) m)

def minAssignCost (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  (((Finset.univ : Finset (Fin m → Fin n)).toList).map (fun g => assignCost cost m n g)).min?.getD
    0

/-- The function returns a result r and r is the minimum total cost of a valid connection: there exists a finite set S of pairs (i,j) with 0 <= i < m and 0 <= j < n such that (1) for every i with 0 <= i < m there is some j with (i,j) in S, (2) for every j with 0 <= j < n there is some i with (i,j) in S, (3) r = sum over (i,j) in S of cost[i][j], with each pair counted once, and (4) for every finite set T of pairs (i,j) with 0 <= i < m and 0 <= j < n that satisfies (1) and (2), the sum over (i,j) in T of cost[i][j] is at least r.
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. (The problem statement also promises m >= n; the specification is stated on the weaker rectangular domain and is valid on the promised domain.) -/
theorem spec_1 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∃ r, connect_two_groups cost = ok r ∧
      ∃ S : Finset (Nat × Nat),
        IsConnSet S m n ∧ r.val = setCost cost S ∧
          ∀ T : Finset (Nat × Nat), IsConnSet T m n → r.val ≤ setCost cost T := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∃ r, connect_two_groups cost = ok r ∧
      ∃ S : Finset (Nat × Nat),
        IsConnSet S m n ∧ r.val = setCost cost S ∧
          ∀ T : Finset (Nat × Nat), IsConnSet T m n → r.val ≤ setCost cost T) := by
  sorry

/-- The function returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∃ r, connect_two_groups cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∃ r, connect_two_groups cost = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= (sum for i = 0 to m-1 of cost[i][0]) + (sum for j = 1 to n-1 of cost[0][j]).
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∀ r, connect_two_groups cost = ok r →
      r.val ≤ (Finset.range m).sum (fun i => entry cost i 0) +
        (Finset.range (n - 1)).sum (fun j => entry cost 0 (j + 1)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∀ r, connect_two_groups cost = ok r →
      r.val ≤ (Finset.range m).sum (fun i => entry cost i 0) +
        (Finset.range (n - 1)).sum (fun j => entry cost 0 (j + 1))) := by
  sorry

/-- Whenever the function returns a result r, r >= sum for j = 0 to n-1 of (min over 0 <= i < m of cost[i][j]).
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∀ r, connect_two_groups cost = ok r →
      (Finset.range n).sum (fun j => minUpTo (fun i => entry cost i j) m) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∀ r, connect_two_groups cost = ok r →
      (Finset.range n).sum (fun j => minUpTo (fun i => entry cost i j) m) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= sum for i = 0 to m-1 of (min over 0 <= j < n of cost[i][j]).
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∀ r, connect_two_groups cost = ok r →
      (Finset.range m).sum (fun i => minUpTo (fun j => entry cost i j) n) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∀ r, connect_two_groups cost = ok r →
      (Finset.range m).sum (fun i => minUpTo (fun j => entry cost i j) n) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = (max(m,n)) * c.
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. There exists an integer c with 0 <= c <= 100 such that cost[i][j] = c for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (c : Int) (hc0 : 0 ≤ c) (hc100 : c ≤ 100)
    (hconst : ∀ i j, i < m → j < n → entry cost i j = c) :
    ∀ r, connect_two_groups cost = ok r → r.val = ((max m n : Nat) : Int) * c := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (c : Int) (hc0 : 0 ≤ c) (hc100 : c ≤ 100)
    (hconst : ∀ i j, i < m → j < n → entry cost i j = c), ∀ r, connect_two_groups cost = ok r → r.val = ((max m n : Nat) : Int) * c) := by
  sorry

/-- Whenever the function returns a result r, r = sum for i = 0 to m-1 of cost[i][0].
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. Also n = 1. -/
theorem spec_7 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hn : n = 1) :
    ∀ r, connect_two_groups cost = ok r → r.val = (Finset.range m).sum (fun i => entry cost i 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hn : n = 1), ∀ r, connect_two_groups cost = ok r → r.val = (Finset.range m).sum (fun i => entry cost i 0)) := by
  sorry

/-- If the function returns r for cost and r' for cost', then r = r'.
  Preconditions: Let m = len(cost) and n = len(cost[0]). Both cost and cost' have m rows and n columns; 1 <= m <= 12, 1 <= n <= 12; all entries of both matrices are in [0,100]. There is a permutation pi of {0,...,m-1} such that cost'[i][j] = cost[pi(i)][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (hperm : ∃ π : Equiv.Perm (Fin m),
      ∀ (i : Fin m) (j : Nat), j < n → entry cost' i.val j = entry cost (π i).val j) :
    ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (hperm : ∃ π : Equiv.Perm (Fin m),
      ∀ (i : Fin m) (j : Nat), j < n → entry cost' i.val j = entry cost (π i).val j), ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r.val = r'.val) := by
  sorry

/-- If the function returns r for cost and r' for cost', then r <= r'.
  Preconditions: Let m = len(cost) and n = len(cost[0]). Both cost and cost' have m rows and n columns; 1 <= m <= 12, 1 <= n <= 12; all entries of both matrices are in [0,100]. There are indices i0,j0 with 0 <= i0 < m and 0 <= j0 < n such that cost'[i0][j0] >= cost[i0][j0] and cost'[i][j] = cost[i][j] for every other pair (i,j). -/
theorem spec_9 (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (i0 j0 : Nat) (hi0 : i0 < m) (hj0 : j0 < n)
    (hge : entry cost i0 j0 ≤ entry cost' i0 j0)
    (heq : ∀ i j, i < m → j < n → (i, j) ≠ (i0, j0) → entry cost' i j = entry cost i j) :
    ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (i0 j0 : Nat) (hi0 : i0 < m) (hj0 : j0 < n)
    (hge : entry cost i0 j0 ≤ entry cost' i0 j0)
    (heq : ∀ i j, i < m → j < n → (i, j) ≠ (i0, j0) → entry cost' i j = entry cost i j), ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- If the function returns r for cost and r' for cost', then r' = c * r.
  Preconditions: Let m = len(cost) and n = len(cost[0]). Both cost and cost' have m rows and n columns; 1 <= m <= 12, 1 <= n <= 12; all entries of both matrices are in [0,100]. There is a nonnegative integer c such that cost'[i][j] = c * cost[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (c : Nat)
    (hscale : ∀ i j, i < m → j < n → entry cost' i j = (c : Int) * entry cost i j) :
    ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r'.val = (c : Int) * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cost cost' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmat' : Rect cost' m n) (hbnd' : EntriesInRange cost' m n)
    (c : Nat)
    (hscale : ∀ i j, i < m → j < n → entry cost' i j = (c : Int) * entry cost i j), ∀ r r', connect_two_groups cost = ok r → connect_two_groups cost' = ok r' →
      r'.val = (c : Int) * r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a set S of pairs (i,j) with 0 <= i < m and 0 <= j < n such that (1) for every i with 0 <= i < m there is some j with (i,j) in S, (2) for every j with 0 <= j < n there is some i with (i,j) in S, (3) r = sum over (i,j) in S of cost[i][j], and (4) the number of pairs in S is at most m + n - 1.
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∀ r, connect_two_groups cost = ok r →
      ∃ S : Finset (Nat × Nat),
        IsConnSet S m n ∧ r.val = setCost cost S ∧ S.card ≤ m + n - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∀ r, connect_two_groups cost = ok r →
      ∃ S : Finset (Nat × Nat),
        IsConnSet S m n ∧ r.val = setCost cost S ∧ S.card ≤ m + n - 1) := by
  sorry

/-- Whenever the function returns r, r = min over all functions f : {0,...,m-1} -> {0,...,n-1} of [ sum_{i=0}^{m-1} cost[i][f(i)] + sum_{j=0}^{n-1} (if j is not in the image of f then min_{0<=i<m} cost[i][j] else 0) ].
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n) :
    ∀ r, connect_two_groups cost = ok r → r.val = minAssignCost cost m n := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n), ∀ r, connect_two_groups cost = ok r → r.val = minAssignCost cost m n) := by
  sorry

/-- If the function returns r for cost and rT for costT, then r = rT.
  Preconditions: Let m = len(cost) and n = len(cost[0]). 1 <= m <= 12, 1 <= n <= 12, every row cost[i] for 0 <= i < m has length n, and 0 <= cost[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. Let costT be the n x m matrix defined by costT[j][i] = cost[i][j]. -/
theorem spec_13 (cost costT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmatT : Rect costT n m) (hbndT : EntriesInRange costT n m)
    (htrans : ∀ j i, j < n → i < m → entry costT j i = entry cost i j) :
    ∀ r rT, connect_two_groups cost = ok r → connect_two_groups costT = ok rT →
      r.val = rT.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cost costT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm12 : m ≤ 12) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hmat : Rect cost m n) (hbnd : EntriesInRange cost m n)
    (hmatT : Rect costT n m) (hbndT : EntriesInRange costT n m)
    (htrans : ∀ j i, j < n → i < m → entry costT j i = entry cost i j), ∀ r rT, connect_two_groups cost = ok r → connect_two_groups costT = ok rT →
      r.val = rT.val) := by
  sorry

end

end AegisSpec.ConnectTwoGroups
