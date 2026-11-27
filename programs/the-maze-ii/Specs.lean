import Aegis.ShortestDistance.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistance.shortest_distance`

LeetCode problem `the-maze-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestDistance

abbrev Cell := ℤ × ℤ

def IsDirection (d : Cell) : Prop :=
  d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

def numRows (maze : Slice (alloc.vec.Vec I64)) : Nat := maze.val.length

def numCols (maze : Slice (alloc.vec.Vec I64)) : Nat :=
  ((maze.val[0]?).map (fun row => row.val.length)).getD 0

def coord (a : Slice I64) (i : Nat) : ℤ := ((a.val[i]?).map (fun x : I64 => x.val)).getD 0

def cellOf (a : Slice I64) : Cell := (coord a 0, coord a 1)

def cellAt (maze : Slice (alloc.vec.Vec I64)) (r c : ℤ) : Option ℤ :=
  if 0 ≤ r ∧ 0 ≤ c then
    ((maze.val[r.toNat]?).bind (fun row => row.val[c.toNat]?)).map (fun x : I64 => x.val)
  else none

def IsEmptyCell (maze : Slice (alloc.vec.Vec I64)) (p : Cell) : Prop :=
  cellAt maze p.1 p.2 = some 0

def IsBlockedCell (maze : Slice (alloc.vec.Vec I64)) (p : Cell) : Prop :=
  ¬ IsEmptyCell maze p

def absInt (x : ℤ) : ℤ := if 0 ≤ x then x else -x

def LegalRoll (maze : Slice (alloc.vec.Vec I64)) (p q : Cell) (k : ℤ) : Prop :=
  ∃ d : Cell,
    IsDirection d ∧
      1 ≤ k ∧
      q = (p.1 + k * d.1, p.2 + k * d.2) ∧
      (∀ i : ℤ, 0 ≤ i → i ≤ k → IsEmptyCell maze (p.1 + i * d.1, p.2 + i * d.2)) ∧
      IsBlockedCell maze (p.1 + (k + 1) * d.1, p.2 + (k + 1) * d.2)

def IsPath
    (maze : Slice (alloc.vec.Vec I64)) (s t : Cell) (cells : List Cell) (costs : List ℤ) : Prop :=
  2 ≤ cells.length ∧
    costs.length + 1 = cells.length ∧
    cells[0]? = some s ∧
    cells.getLast? = some t ∧
    (∀ i : Nat,
      i < costs.length →
        ∃ p q k, cells[i]? = some p ∧ cells[i + 1]? = some q ∧ costs[i]? = some k ∧
          LegalRoll maze p q k)

def PathCost (maze : Slice (alloc.vec.Vec I64)) (s t : Cell) (k : ℤ) : Prop :=
  ∃ cells costs, IsPath maze s t cells costs ∧ costs.sum = k

def SimplePathCost (maze : Slice (alloc.vec.Vec I64)) (s t : Cell) (k : ℤ) : Prop :=
  ∃ cells costs, IsPath maze s t cells costs ∧ cells.Nodup ∧ costs.sum = k

def ValidInput (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64) : Prop :=
  1 ≤ numRows maze ∧
    numRows maze ≤ 100 ∧
    1 ≤ numCols maze ∧
    numCols maze ≤ 100 ∧
    (∀ row ∈ maze.val, row.val.length = numCols maze) ∧
    (∀ row ∈ maze.val, ∀ x ∈ row.val, x.val = 0 ∨ x.val = 1) ∧
    start.val.length = 2 ∧
    destination.val.length = 2 ∧
    0 ≤ coord start 0 ∧
    coord start 0 < (numRows maze : ℤ) ∧
    0 ≤ coord start 1 ∧
    coord start 1 < (numCols maze : ℤ) ∧
    0 ≤ coord destination 0 ∧
    coord destination 0 < (numRows maze : ℤ) ∧
    0 ≤ coord destination 1 ∧
    coord destination 1 < (numCols maze : ℤ) ∧
    IsEmptyCell maze (cellOf start) ∧
    IsEmptyCell maze (cellOf destination) ∧
    cellOf start ≠ cellOf destination

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. A path from start to destination is a sequence of cells p0, p1, ..., pt with t >= 1, p0 = (start[0], start[1]), pt = (destination[0], destination[1]), such that for each 0 <= i < t there exists an integer k_i >= 1 with a legal roll from p_i to p_{i+1} of cost k_i; the total cost of the path is the sum of k_i for 0 <= i < t. Whenever the function returns a result r, the following holds: if there exists at least one path from start to destination (as defined above), then r is the minimum total cost over all such paths; if no such path exists, then r = -1.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_1
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        ((∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k) →
            (PathCost maze (cellOf start) (cellOf destination) r.val ∧
              ∀ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k → r.val ≤ k)) ∧
          (¬ (∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        ((∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k) →
            (PathCost maze (cellOf start) (cellOf destination) r.val ∧
              ∀ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k → r.val ≤ k)) ∧
          (¬ (∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k) → r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_2
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∃ r : I64, Aegis.ShortestDistance.shortest_distance maze start destination = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∃ r : I64, Aegis.ShortestDistance.shortest_distance maze start destination = ok r) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= m * n * (max(m,n) - 1), where m = len(maze) and n = len(maze[0]).
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_3
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          r.val ≤
            (numRows maze : ℤ) * (numCols maze : ℤ) *
              ((max (numRows maze) (numCols maze) : ℤ) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          r.val ≤
            (numRows maze : ℤ) * (numCols maze : ℤ) *
              ((max (numRows maze) (numCols maze) : ℤ) - 1)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r >= |start[0] - destination[0]| + |start[1] - destination[1]|.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_4
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          r.val ≥
            absInt (coord start 0 - coord destination 0) +
              absInt (coord start 1 - coord destination 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          r.val ≥
            absInt (coord start 0 - coord destination 0) +
              absInt (coord start 1 - coord destination 1)) := by
  sorry

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. A path from start to destination is a sequence of cells p0, p1, ..., pt with t >= 1, p0 = (start[0], start[1]), pt = (destination[0], destination[1]), such that for each 0 <= i < t there exists an integer k_i >= 1 with a legal roll from p_i to p_{i+1} of cost k_i; the total cost of the path is the sum of k_i for 0 <= i < t. Whenever the function returns a result r with r != -1, for every path from start to destination (as defined above), the total cost of that path is at least r.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_5
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          ∀ (cells : List Cell) (costs : List ℤ),
            IsPath maze (cellOf start) (cellOf destination) cells costs → r.val ≤ costs.sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          ∀ (cells : List Cell) (costs : List ℤ),
            IsPath maze (cellOf start) (cellOf destination) cells costs → r.val ≤ costs.sum) := by
  sorry

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. A path from start to destination is a sequence of cells p0, p1, ..., pt with t >= 1, p0 = (start[0], start[1]), pt = (destination[0], destination[1]), such that for each 0 <= i < t there exists an integer k_i >= 1 with a legal roll from p_i to p_{i+1} of cost k_i; the total cost of the path is the sum of k_i for 0 <= i < t. Whenever the function returns a result r, r = -1 if and only if there does not exist any path from start to destination (as defined above).
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_6
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        (r.val = -1 ↔ ¬ ∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        (r.val = -1 ↔ ¬ ∃ k : ℤ, PathCost maze (cellOf start) (cellOf destination) k)) := by
  sorry

/-- Call a cell (r,c) non-empty if it is out-of-bounds (r < 0 or r >= m or c < 0 or c >= n) or maze[r][c] = 1. If for every direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} the cell (start[0] + dr, start[1] + dc) is non-empty, then whenever the function returns a result r, r = -1.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_7
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination)
    (hblocked :
      ∀ d : Cell, IsDirection d → IsBlockedCell maze (coord start 0 + d.1, coord start 1 + d.2)) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination)
    (hblocked :
      ∀ d : Cell, IsDirection d → IsBlockedCell maze (coord start 0 + d.1, coord start 1 + d.2)), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = -1) := by
  sorry

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. If there exists a legal roll from start to destination with cost k (as defined above), then whenever the function returns a result r, r = k.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_8
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) (k : ℤ)
    (hroll : LegalRoll maze (cellOf start) (cellOf destination) k) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) (k : ℤ)
    (hroll : LegalRoll maze (cellOf start) (cellOf destination) k), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = k) := by
  sorry

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. If there is no cell p and direction d such that a legal roll from p in direction d lands exactly at destination (i.e., destination is not the endpoint of any legal roll), then whenever the function returns a result r, r = -1.
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_9
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination)
    (hno :
      ∀ (p : Cell) (k : ℤ), ¬ LegalRoll maze p (cellOf destination) k) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination)
    (hno :
      ∀ (p : Cell) (k : ℤ), ¬ LegalRoll maze p (cellOf destination) k), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r → r.val = -1) := by
  sorry

/-- Call a cell (r,c) empty if 0 <= r < m, 0 <= c < n, and maze[r][c] = 0; otherwise (including out-of-bounds) call it non-empty. A legal roll from cell p = (pr,pc) to cell q = (qr,qc) with cost k is defined to hold if there exists a direction d = (dr,dc) in {(1,0),(-1,0),(0,1),(0,-1)} and an integer k >= 1 such that q = (pr + k*dr, pc + k*dc), every cell (pr + i*dr, pc + i*dc) for 0 <= i <= k is empty, and the cell (pr + (k+1)*dr, pc + (k+1)*dc) is non-empty. A path from start to destination is a sequence of cells p0, p1, ..., pt with t >= 1, p0 = (start[0], start[1]), pt = (destination[0], destination[1]), such that for each 0 <= i < t there exists an integer k_i >= 1 with a legal roll from p_i to p_{i+1} of cost k_i; the total cost of the path is the sum of k_i for 0 <= i < t. Whenever the function returns a result r with r != -1, there exists a path from start to destination of total cost r that visits each cell at most once (i.e., the cells p0, p1, ..., pt are pairwise distinct).
  Preconditions: Let m = len(maze) and n = len(maze[0]). The slice maze is non-empty and every row has length n (i.e., len(maze[i]) = n for 0 <= i < m), with 1 <= m, n <= 100. Every maze[i][j] for 0 <= i < m and 0 <= j < n is 0 or 1. len(start) = 2 and len(destination) = 2. 0 <= start[0], destination[0] < m and 0 <= start[1], destination[1] < n. maze[start[0]][start[1]] = 0 and maze[destination[0]][destination[1]] = 0. (start[0], start[1]) != (destination[0], destination[1]). The maze contains at least 2 empty cells (implied by the previous conditions). -/
theorem spec_10
    (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination) :
    ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          SimplePathCost maze (cellOf start) (cellOf destination) r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (start destination : Slice I64)
    (h : ValidInput maze start destination), ∀ r : I64,
      Aegis.ShortestDistance.shortest_distance maze start destination = ok r →
        r.val ≠ -1 →
          SimplePathCost maze (cellOf start) (cellOf destination) r.val) := by
  sorry

end AegisSpec.ShortestDistance
