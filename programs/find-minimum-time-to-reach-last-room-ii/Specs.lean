import Aegis.MinTimeToReach.Code.Funs

/-!
# Specifications of `Aegis.MinTimeToReach.min_time_to_reach`

LeetCode problem `find-minimum-time-to-reach-last-room-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

noncomputable section

namespace AegisSpec.MinTimeToReach

def Rows (moveTime : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  moveTime.val.map fun row => row.slice.val.map fun x => x.val

def entry (moveTime : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ((Rows moveTime).getD i []).getD j 0

def Admissible (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : Prop :=
  2 ≤ n ∧ n ≤ 750 ∧ 2 ≤ m ∧ m ≤ 750 ∧
    (Rows moveTime).length = n ∧
    (∀ i, i < n → ((Rows moveTime).getD i []).length = m) ∧
    (∀ i, i < n → ∀ j, j < m → 0 ≤ entry moveTime i j ∧ entry moveTime i j ≤ 10 ^ 9)

def stepCost (q : Nat) : Int := if q % 2 = 0 then 1 else 2

def gridRooms (n m : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range m).map fun j => (i, j)

def InGrid (n m : Nat) (p : Nat × Nat) : Prop := p.1 < n ∧ p.2 < m

def ManhattanAdjacent (p q : Nat × Nat) : Prop :=
  Int.natAbs ((p.1 : Int) - (q.1 : Int)) + Int.natAbs ((p.2 : Int) - (q.2 : Int)) = 1

def IsWalk (n m : Nat) (W : List (Nat × Nat)) : Prop :=
  W.head? = some (0, 0) ∧ W.getLast? = some (n - 1, m - 1) ∧
    (∀ p ∈ W, InGrid n m p) ∧
    ∀ q, q + 1 < W.length → ManhattanAdjacent (W.getD q (0, 0)) (W.getD (q + 1) (0, 0))

def OnlyDownRight (W : List (Nat × Nat)) : Prop :=
  ∀ q, q + 1 < W.length →
    ((W.getD (q + 1) (0, 0)).1 = (W.getD q (0, 0)).1 + 1 ∧
        (W.getD (q + 1) (0, 0)).2 = (W.getD q (0, 0)).2) ∨
      ((W.getD (q + 1) (0, 0)).2 = (W.getD q (0, 0)).2 + 1 ∧
        (W.getD (q + 1) (0, 0)).1 = (W.getD q (0, 0)).1)

def numMoves (W : List (Nat × Nat)) : Nat := W.length - 1

def walkTimeFrom (moveTime : Slice (alloc.vec.Vec Std.I64)) : Int → Nat → List (Nat × Nat) → Int
  | t, _, [] => t
  | t, q, p :: rest =>
    walkTimeFrom moveTime (max t (entry moveTime p.1 p.2) + stepCost q) (q + 1) rest

def walkTime (moveTime : Slice (alloc.vec.Vec Std.I64)) (W : List (Nat × Nat)) : Int :=
  match W with
  | [] => 0
  | _ :: rest => walkTimeFrom moveTime 0 0 rest

def allEntries (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : List Int :=
  (gridRooms n m).map fun p => entry moveTime p.1 p.2

def entriesExceptStart (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : List Int :=
  ((gridRooms n m).filter fun p => p ≠ (0, 0)).map fun p => entry moveTime p.1 p.2

def minEntryExceptStart (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : Int :=
  ((entriesExceptStart moveTime n m).min?).getD 0

def maxEntry (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) : Int :=
  ((allEntries moveTime n m).max?).getD 0

def firstStepMin (moveTime : Slice (alloc.vec.Vec Std.I64)) : Int :=
  min (entry moveTime 0 1) (entry moveTime 1 0)

def gridDist (n m : Nat) : Nat := n + m - 2

def floorThreeHalves (d : Nat) : Int := ((3 * d / 2 : Nat) : Int)

def lastStepCost (d : Nat) : Int := if d % 2 = 1 then 1 else 2

/-- Let a walk be a finite sequence W = ((i_0,j_0),...,(i_k,j_k)) of rooms with (i_0,j_0)=(0,0), (i_k,j_k)=(n-1,m-1), and |i_{q+1}-i_q| + |j_{q+1}-j_q| = 1 for every 0 <= q < k. Define T_W(0)=0 and, for q=0,...,k-1, T_W(q+1) = max(T_W(q), moveTime[i_{q+1}][j_{q+1}]) + (1 if q is even, 2 if q is odd). Then the function returns a result r and r = min { T_W(k) | W is a walk from (0,0) to (n-1,m-1) }.
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_1 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      (∀ W, IsWalk n m W → r ≤ walkTime moveTime W) ∧
      ∃ W, IsWalk n m W ∧ walkTime moveTime W = r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      (∀ W, IsWalk n m W → r ≤ walkTime moveTime W) ∧
      ∃ W, IsWalk n m W ∧ walkTime moveTime W = r) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: no arithmetic overflow, no out-of-bounds slice or vector access, and no panic occurs.
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_2 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r) := by
  sorry

/-- Let d = n+m-2 and let T be the minimum of moveTime[i][j] over all rooms (i,j) with (i,j) != (0,0). The result r satisfies r >= T + floor(3*d/2).
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_3 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      minEntryExceptStart moveTime n m + floorThreeHalves (gridDist n m) ≤ r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      minEntryExceptStart moveTime n m + floorThreeHalves (gridDist n m) ≤ r) := by
  sorry

/-- Let d = n+m-2 and let M be the maximum of moveTime[i][j] over all 0 <= i < n and 0 <= j < m. The result r satisfies r <= M + floor(3*d/2).
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_4 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r ≤ maxEntry moveTime n m + floorThreeHalves (gridDist n m) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r ≤ maxEntry moveTime n m + floorThreeHalves (gridDist n m)) := by
  sorry

/-- Let d = n+m-2. The result r satisfies r >= moveTime[n-1][m-1] + c, where c = 1 when d is odd and c = 2 when d is even.
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_5 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      entry moveTime (n - 1) (m - 1) + lastStepCost (gridDist n m) ≤ r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      entry moveTime (n - 1) (m - 1) + lastStepCost (gridDist n m) ≤ r) := by
  sorry

/-- Let d = n+m-2. The result is r = C + floor(3*d/2).
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. Assume additionally that all entries of moveTime are equal to the same integer C. -/
theorem spec_6 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hadm : Admissible moveTime n m)
    (hconst : ∀ i, i < n → ∀ j, j < m → entry moveTime i j = C) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r = C + floorThreeHalves (gridDist n m) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hadm : Admissible moveTime n m)
    (hconst : ∀ i, i < n → ∀ j, j < m → entry moveTime i j = C), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r = C + floorThreeHalves (gridDist n m)) := by
  sorry

/-- Let a = moveTime[0][1], b = moveTime[1][0], and c = moveTime[1][1]. The result is r = max(c, min(a+1, b+1)) + 2.
  Preconditions: Let n = len(moveTime) and m be the common row length. Assume n = 2, m = 2, every row moveTime[i] has length 2, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < 2 and 0 <= j < 2. -/
theorem spec_7 (moveTime : Slice (alloc.vec.Vec Std.I64))
    (hadm : Admissible moveTime 2 2) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r = max (entry moveTime 1 1) (min (entry moveTime 0 1 + 1) (entry moveTime 1 0 + 1)) + 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64))
    (hadm : Admissible moveTime 2 2), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      r = max (entry moveTime 1 1) (min (entry moveTime 0 1 + 1) (entry moveTime 1 0 + 1)) + 2) := by
  sorry

/-- Then min_time_to_reach(A) = min_time_to_reach(B).
  Preconditions: Let A and B be two admissible inputs with the same row count n and common column count m, so 2 <= n <= 750, 2 <= m <= 750, all rows have length m, and all entries are in [0,10^9]. Assume A[i][j] = B[i][j] for every 0 <= i < n and 0 <= j < m except possibly at (i,j)=(0,0). -/
theorem spec_8 (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hA : Admissible A n m) (hB : Admissible B n m)
    (hagree : ∀ i, i < n → ∀ j, j < m → (i, j) ≠ (0, 0) → entry A i j = entry B i j) :
    Aegis.MinTimeToReach.min_time_to_reach A = Aegis.MinTimeToReach.min_time_to_reach B := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hA : Admissible A n m) (hB : Admissible B n m)
    (hagree : ∀ i, i < n → ∀ j, j < m → (i, j) ≠ (0, 0) → entry A i j = entry B i j), Aegis.MinTimeToReach.min_time_to_reach A = Aegis.MinTimeToReach.min_time_to_reach B) := by
  sorry

/-- Let r_A = min_time_to_reach(A) and r_B = min_time_to_reach(B). Then r_A <= r_B.
  Preconditions: Let A and B be two admissible inputs with the same row count n and common column count m, so 2 <= n <= 750, 2 <= m <= 750, all rows have length m, and all entries are in [0,10^9]. Assume A[i][j] <= B[i][j] for every 0 <= i < n and 0 <= j < m. -/
theorem spec_9 (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hA : Admissible A n m) (hB : Admissible B n m)
    (hle : ∀ i, i < n → ∀ j, j < m → entry A i j ≤ entry B i j) :
    ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB → (rA : Int) ≤ (rB : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hA : Admissible A n m) (hB : Admissible B n m)
    (hle : ∀ i, i < n → ∀ j, j < m → entry A i j ≤ entry B i j), ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB → (rA : Int) ≤ (rB : Int)) := by
  sorry

/-- Then min_time_to_reach(B) = min_time_to_reach(A) + C.
  Preconditions: Let A be an admissible input with row count n and common column count m. Let C be an integer with C >= 0 such that B defined by B[i][j] = A[i][j] + C for every 0 <= i < n and 0 <= j < m is also admissible (in particular all B entries are at most 10^9). -/
theorem spec_10 (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hC : 0 ≤ C) (hA : Admissible A n m) (hB : Admissible B n m)
    (hshift : ∀ i, i < n → ∀ j, j < m → entry B i j = entry A i j + C) :
    ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB → rB = rA + C := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hC : 0 ≤ C) (hA : Admissible A n m) (hB : Admissible B n m)
    (hshift : ∀ i, i < n → ∀ j, j < m → entry B i j = entry A i j + C), ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB → rB = rA + C) := by
  sorry

/-- Let r_A = min_time_to_reach(A) and r_B = min_time_to_reach(B). Then r_A <= r_B <= r_A + C.
  Preconditions: Let A be an admissible input with row count n and common column count m. Let C >= 0 be such that B is admissible, B[i][j] = A[i][j] for every room except (n-1,m-1), and B[n-1][m-1] = A[n-1][m-1] + C. -/
theorem spec_11 (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hC : 0 ≤ C) (hA : Admissible A n m) (hB : Admissible B n m)
    (hagree : ∀ i, i < n → ∀ j, j < m → (i, j) ≠ (n - 1, m - 1) → entry B i j = entry A i j)
    (htarget : entry B (n - 1) (m - 1) = entry A (n - 1) (m - 1) + C) :
    ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB →
        (rA : Int) ≤ (rB : Int) ∧ (rB : Int) ≤ (rA : Int) + C := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (n m : Nat) (C : Int)
    (hC : 0 ≤ C) (hA : Admissible A n m) (hB : Admissible B n m)
    (hagree : ∀ i, i < n → ∀ j, j < m → (i, j) ≠ (n - 1, m - 1) → entry B i j = entry A i j)
    (htarget : entry B (n - 1) (m - 1) = entry A (n - 1) (m - 1) + C), ∀ rA rB, Aegis.MinTimeToReach.min_time_to_reach A = ok rA →
      Aegis.MinTimeToReach.min_time_to_reach B = ok rB →
        (rA : Int) ≤ (rB : Int) ∧ (rB : Int) ≤ (rA : Int) + C) := by
  sorry

/-- Let r be the result. There exists a walk W from (0,0) to (n-1,m-1), under the movement and waiting rules of the problem, whose arrival time is exactly r and in which no room occurs twice. Consequently, this optimal walk has at most n*m-1 moves.
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_12 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      ∃ W, IsWalk n m W ∧ W.Nodup ∧ walkTime moveTime W = r ∧ numMoves W ≤ n * m - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      ∃ W, IsWalk n m W ∧ W.Nodup ∧ walkTime moveTime W = r ∧ numMoves W ≤ n * m - 1) := by
  sorry

/-- There exists an optimal walk W from (0,0) to (n-1,m-1) that only moves down (increasing i by 1) or right (increasing j by 1); consequently, this optimal walk has exactly d = n+m-2 moves.
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_13 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      ∃ W, IsWalk n m W ∧ OnlyDownRight W ∧ walkTime moveTime W = r ∧
        numMoves W = gridDist n m := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∃ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r ∧
      ∃ W, IsWalk n m W ∧ OnlyDownRight W ∧ walkTime moveTime W = r ∧
        numMoves W = gridDist n m) := by
  sorry

/-- Let d = n+m-2 and let t = min(moveTime[0][1], moveTime[1][0]). The result r satisfies r >= t + floor(3*d/2).
  Preconditions: Let n = len(moveTime); let m be the common row length. Assume 2 <= n <= 750, 2 <= m <= 750, every row moveTime[i] has length m, and 0 <= moveTime[i][j] <= 10^9 for every 0 <= i < n and 0 <= j < m. -/
theorem spec_14 (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m) :
    ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      firstStepMin moveTime + floorThreeHalves (gridDist n m) ≤ r := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (moveTime : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hadm : Admissible moveTime n m), ∀ r, Aegis.MinTimeToReach.min_time_to_reach moveTime = ok r →
      firstStepMin moveTime + floorThreeHalves (gridDist n m) ≤ r) := by
  sorry

end AegisSpec.MinTimeToReach

end
