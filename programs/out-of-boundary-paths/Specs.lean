import Aegis.FindPaths.Code.Funs

/-!
# Specifications of `Aegis.FindPaths.find_paths`

LeetCode problem `out-of-boundary-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.FindPaths

def isMove (d : Int × Int) : Prop :=
  d = (-1, 0) ∨ d = (1, 0) ∨ d = (0, -1) ∨ d = (0, 1)

def moveList : List (Int × Int) := [(-1, 0), (1, 0), (0, -1), (0, 1)]

def shift : Int × Int → List (Int × Int) → Int × Int
  | p, [] => p
  | p, d :: ds => shift (p.1 + d.1, p.2 + d.2) ds

def posAfter (sr sc : Int) (path : List (Int × Int)) (t : Nat) : Int × Int :=
  shift (sr, sc) (path.take t)

def inside (m n : Int) (p : Int × Int) : Prop :=
  0 ≤ p.1 ∧ p.1 < m ∧ 0 ≤ p.2 ∧ p.2 < n

def isEscapingPath (m n sr sc : Int) (path : List (Int × Int)) : Prop :=
  (∀ d ∈ path, isMove d) ∧
    (∀ t, t < path.length → inside m n (posAfter sr sc path t)) ∧
      ¬ inside m n (posAfter sr sc path path.length)

def moveSeqsOfLength : Nat → List (List (Int × Int))
  | 0 => [[]]
  | k + 1 => (moveSeqsOfLength k).flatMap (fun p => moveList.map (fun d => p ++ [d]))

noncomputable def escapingPaths (m n sr sc : Int) (k : Nat) : List (List (Int × Int)) := by
  classical
  exact (moveSeqsOfLength k).filter (fun p => decide (isEscapingPath m n sr sc p))

noncomputable def numEscapingPaths (m n sr sc : Int) (maxMove : Int) : Nat :=
  ((List.range maxMove.toNat).map (fun k => (escapingPaths m n sr sc (k + 1)).length)).sum

def mkI64 (x : Int) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 x⟩

def edgeDist (m n sr sc : Int) : Int :=
  min (min (sr + 1) (m - sr)) (min (sc + 1) (n - sc))

/-- Let M = 1000000007. For an integer k with 1 <= k <= maxMove, consider a sequence of k moves, each one of (-1,0), (1,0), (0,-1), (0,1), starting from p_0 = (startRow, startColumn) and setting p_t = p_{t-1} + move_t for 1 <= t <= k. Call this sequence an escaping path if every p_t with 0 <= t < k has row in [0, m-1] and column in [0, n-1], while p_k has row outside [0, m-1] or column outside [0, n-1]. Let N be the number of escaping paths over all k with 1 <= k <= maxMove. The function returns a result r such that 0 <= r < M and r is congruent to N modulo M; equivalently, r is the least nonnegative residue of N modulo M.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_1 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val
            (Int.ofNat
              (numEscapingPaths m.val n.val startRow.val startColumn.val maxMove.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val
            (Int.ofNat
              (numEscapingPaths m.val n.val startRow.val startColumn.val maxMove.val))) := by
  sorry

/-- The call find_paths(m, n, maxMove, startRow, startColumn) returns a result r; it does not fail, panic, go out of bounds, or overflow the i64 range.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_2 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r) := by
  sorry

/-- The function returns a result r with 0 <= r <= 1000000006.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_3 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- The function returns 0.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, maxMove = 0, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_4 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : maxMove.val = 0)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : maxMove.val = 0)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r with r = (1 if startRow = 0 else 0) + (1 if startRow = m-1 else 0) + (1 if startColumn = 0 else 0) + (1 if startColumn = n-1 else 0).
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, maxMove = 1, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_5 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : maxMove.val = 1)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        r.val = (if startRow.val = 0 then (1 : Int) else 0) +
          (if startRow.val = m.val - 1 then (1 : Int) else 0) +
          (if startColumn.val = 0 then (1 : Int) else 0) +
          (if startColumn.val = n.val - 1 then (1 : Int) else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : maxMove.val = 1)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧
        r.val = (if startRow.val = 0 then (1 : Int) else 0) +
          (if startRow.val = m.val - 1 then (1 : Int) else 0) +
          (if startColumn.val = 0 then (1 : Int) else 0) +
          (if startColumn.val = n.val - 1 then (1 : Int) else 0)) := by
  sorry

/-- The function returns a result r with r = 4.
  Preconditions: The I64 parameters satisfy m = 1, n = 1, 1 <= maxMove <= 50, startRow = 0, and startColumn = 0. -/
theorem spec_6 (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : m.val = 1) (hn : n.val = 1)
    (hmaxMove : 1 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : startRow.val = 0)
    (hstartColumn : startColumn.val = 0) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧ r.val = 4 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n maxMove startRow startColumn : Aeneas.Std.I64)
    (hm : m.val = 1) (hn : n.val = 1)
    (hmaxMove : 1 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : startRow.val = 0)
    (hstartColumn : startColumn.val = 0), ∃ r : Aeneas.Std.I64,
      Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r ∧ r.val = 4) := by
  sorry

/-- Whenever find_paths(m, n, maxMove, startRow, startColumn) returns r and find_paths(n, m, maxMove, startColumn, startRow) returns r', we have r = r'.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_7 (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths n m maxMove startColumn startRow = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths n m maxMove startColumn startRow = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever find_paths(m, n, maxMove, startRow, startColumn) returns r and find_paths(m, n, maxMove, startRow, n-1-startColumn) returns r', we have r = r'.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_8 (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove startRow
      (mkI64 (n.val - 1 - startColumn.val)) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove startRow
      (mkI64 (n.val - 1 - startColumn.val)) = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever find_paths(m, n, maxMove, startRow, startColumn) returns r and find_paths(m, n, maxMove, m-1-startRow, startColumn) returns r', we have r = r'.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_9 (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove
      (mkI64 (m.val - 1 - startRow.val)) startColumn = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove
      (mkI64 (m.val - 1 - startRow.val)) startColumn = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever find_paths(m, n, maxMove, startRow, startColumn) returns r and find_paths(m, n, maxMove, m-1-startRow, n-1-startColumn) returns r', we have r = r'.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_10 (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove
      (mkI64 (m.val - 1 - startRow.val)) (mkI64 (n.val - 1 - startColumn.val)) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (m n maxMove startRow startColumn r r' : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hres' : Aegis.FindPaths.find_paths m n maxMove
      (mkI64 (m.val - 1 - startRow.val)) (mkI64 (n.val - 1 - startColumn.val)) = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever find_paths(m, n, maxMove, startRow, startColumn) returns r with r != 0, there exists an integer k with 1 <= k <= maxMove and a sequence of k moves, each one of (-1,0), (1,0), (0,-1), (0,1), such that starting from (startRow, startColumn), the starting position and all positions after the first k-1 moves are inside the grid (row in [0, m-1] and column in [0, n-1]), and the position after the kth move is outside the grid.
  Preconditions: The I64 parameters satisfy 1 <= m <= 50, 1 <= n <= 50, 0 <= maxMove <= 50, 0 <= startRow < m, and 0 <= startColumn < n. -/
theorem spec_11 (m n maxMove startRow startColumn r : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hr : r.val ≠ 0) :
    ∃ k : Nat,
      1 ≤ k ∧ k ≤ maxMove.val.toNat ∧
        ∃ path : List (Int × Int),
          path.length = k ∧ isEscapingPath m.val n.val startRow.val startColumn.val path := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (m n maxMove startRow startColumn r : Aeneas.Std.I64)
    (hm : 1 ≤ m.val ∧ m.val ≤ 50) (hn : 1 ≤ n.val ∧ n.val ≤ 50)
    (hmaxMove : 0 ≤ maxMove.val ∧ maxMove.val ≤ 50)
    (hstartRow : 0 ≤ startRow.val ∧ startRow.val < m.val)
    (hstartColumn : 0 ≤ startColumn.val ∧ startColumn.val < n.val)
    (hres : Aegis.FindPaths.find_paths m n maxMove startRow startColumn = ok r)
    (hr : r.val ≠ 0), ∃ k : Nat,
      1 ≤ k ∧ k ≤ maxMove.val.toNat ∧
        ∃ path : List (Int × Int),
          path.length = k ∧ isEscapingPath m.val n.val startRow.val startColumn.val path) := by
  sorry

end AegisSpec.FindPaths
