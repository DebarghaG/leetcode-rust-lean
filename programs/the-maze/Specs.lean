import Aegis.HasPath.Code.Funs

/-!
# Specifications of `Aegis.HasPath.has_path`

LeetCode problem `the-maze`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasPath

  open Aegis.HasPath

  abbrev Position : Type := Int × Int

  def shift (p v : Position) (k : Int) : Position := (p.1 + k * v.1, p.2 + k * v.2)

  def cell (maze : Slice (alloc.vec.Vec I64)) (r c : Nat) : Option Int :=
    match maze.val[r]? with
    | none => none
    | some row => (row.val[c]?).map (fun v => v.val)

  def CellEmpty (maze : Slice (alloc.vec.Vec I64)) (p : Position) : Prop :=
    cell maze p.1.toNat p.2.toNat = some 0

  def CellWall (maze : Slice (alloc.vec.Vec I64)) (p : Position) : Prop :=
    cell maze p.1.toNat p.2.toNat = some 1

  def InBounds (m n : Nat) (p : Position) : Prop :=
    0 ≤ p.1 ∧ p.1 < (m : Int) ∧ 0 ≤ p.2 ∧ p.2 < (n : Int)

  inductive Dir where
    | up
    | down
    | left
    | right
    deriving DecidableEq, Repr

  def Dir.vec : Dir → Position
    | .up => (-1, 0)
    | .down => (1, 0)
    | .left => (0, -1)
    | .right => (0, 1)

  def IsGrid (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    1 ≤ m ∧ m ≤ 100 ∧ 1 ≤ n ∧ n ≤ 100 ∧
    maze.val.length = m ∧
    (∀ row ∈ maze.val, row.val.length = n) ∧
    (∀ r c : Nat, r < m → c < n → cell maze r c = some 0 ∨ cell maze r c = some 1)

  def emptyCount (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) : Nat :=
    (List.range m).foldl
      (fun acc r => acc + ((List.range n).filter (fun c => cell maze r c == some 0)).length) 0

  def RollsIn (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) (p : Position) (d : Dir)
      (q : Position) : Prop :=
    InBounds m n (shift p (Dir.vec d) 1) ∧
    CellEmpty maze (shift p (Dir.vec d) 1) ∧
    ∃ k : Nat,
      1 ≤ k ∧
      q = shift p (Dir.vec d) (k : Int) ∧
      (∀ i : Nat, i ≤ k →
        InBounds m n (shift p (Dir.vec d) (i : Int)) ∧
        CellEmpty maze (shift p (Dir.vec d) (i : Int))) ∧
      (¬ InBounds m n (shift p (Dir.vec d) ((k : Int) + 1)) ∨
        CellWall maze (shift p (Dir.vec d) ((k : Int) + 1)))

  def Rolls (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) (p q : Position) : Prop :=
    ∃ d : Dir, RollsIn maze m n p d q

  def IsRollSeq (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) (t : Nat)
      (ps : Nat → Position) : Prop :=
    1 ≤ t ∧ ∀ i : Nat, i < t → Rolls maze m n (ps i) (ps (i + 1))

  def RollReach (maze : Slice (alloc.vec.Vec I64)) (m n : Nat) (p q : Position) : Prop :=
    ∃ t : Nat, ∃ ps : Nat → Position, IsRollSeq maze m n t ps ∧ ps 0 = p ∧ ps t = q

  def IsReflectH (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    maze'.val.length = m ∧
    (∀ row ∈ maze'.val, row.val.length = n) ∧
    (∀ i j : Nat, i < m → j < n → cell maze' i j = cell maze i (n - 1 - j))

  def IsReflectV (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    maze'.val.length = m ∧
    (∀ row ∈ maze'.val, row.val.length = n) ∧
    (∀ i j : Nat, i < m → j < n → cell maze' i j = cell maze (m - 1 - i) j)

  def IsTranspose (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    maze'.val.length = n ∧
    (∀ row ∈ maze'.val, row.val.length = m) ∧
    (∀ i j : Nat, i < n → j < m → cell maze' i j = cell maze j i)

  /-- Let a position be a pair (r,c) with 0 <= r < m and 0 <= c < n. A cell is empty if maze[r][c] = 0. For a position p and a direction d ∈ {(-1,0),(1,0),(0,-1),(0,1)}, we say that q is obtained by rolling from p in direction d if: (1) p + d is within bounds and maze[p + d] = 0; (2) there exists an integer k >= 1 such that q = p + k*d, for all i with 0 <= i <= k, p + i*d is within bounds and maze[p + i*d] = 0, and either p + (k+1)*d is out of bounds or maze[p + (k+1)*d] = 1. The function returns true if and only if there exists a finite sequence of positions p0, p1, ..., pt (t >= 1) such that p0 = start, pt = destination, and for each i from 0 to t-1, p_{i+1} is obtained by rolling from p_i in some direction d. Otherwise, it returns false.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_1 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      (has_path maze start destination = ok true ↔ RollReach maze m n (sr, sc) (dr, dc)) ∧
      (has_path maze start destination = ok false ↔ ¬ RollReach maze m n (sr, sc) (dr, dc)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), (has_path maze start destination = ok true ↔ RollReach maze m n (sr, sc) (dr, dc)) ∧
        (has_path maze start destination = ok false ↔ ¬ RollReach maze m n (sr, sc) (dr, dc))) := by
    sorry

  /-- For all inputs satisfying the preconditions, the function returns a result (either true or false) and does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_2 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      ∃ r : Bool, has_path maze start destination = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), ∃ r : Bool, has_path maze start destination = ok r) := by
    sorry

  /-- If the function returns true, then there exists a finite sequence of positions p0, p1, ..., pk (k >= 1) such that p0 = start, pk = destination, each pi (0 <= i <= k) is within the maze bounds and maze[pi] = 0, and for each i from 0 to k-1, p_{i+1} is obtained by rolling from p_i in one of the four directions (as defined in spec_1).
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_3 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      has_path maze start destination = ok true →
        ∃ t : Nat, ∃ ps : Nat → Position,
          IsRollSeq maze m n t ps ∧
          ps 0 = (sr, sc) ∧
          ps t = (dr, dc) ∧
          (∀ i : Nat, i ≤ t → InBounds m n (ps i) ∧ CellEmpty maze (ps i)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), has_path maze start destination = ok true →
          ∃ t : Nat, ∃ ps : Nat → Position,
            IsRollSeq maze m n t ps ∧
            ps 0 = (sr, sc) ∧
            ps t = (dr, dc) ∧
            (∀ i : Nat, i ≤ t → InBounds m n (ps i) ∧ CellEmpty maze (ps i))) := by
    sorry

  /-- If there is no direction d ∈ {(-1,0),(1,0),(0,-1),(0,1)} such that the cell destination + d is either out of bounds or maze[destination + d] = 1, and the cell destination - d is within bounds and maze[destination - d] = 0, then the function returns false.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_4 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (hstop : ∀ d : Dir,
        ¬ ((¬ InBounds m n (shift (dr, dc) (Dir.vec d) 1) ∨
              CellWall maze (shift (dr, dc) (Dir.vec d) 1)) ∧
            InBounds m n (shift (dr, dc) (Dir.vec d) (-1)) ∧
            CellEmpty maze (shift (dr, dc) (Dir.vec d) (-1)))) :
      has_path maze start destination = ok false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (hstop : ∀ d : Dir,
          ¬ ((¬ InBounds m n (shift (dr, dc) (Dir.vec d) 1) ∨
                CellWall maze (shift (dr, dc) (Dir.vec d) 1)) ∧
              InBounds m n (shift (dr, dc) (Dir.vec d) (-1)) ∧
              CellEmpty maze (shift (dr, dc) (Dir.vec d) (-1)))), has_path maze start destination = ok false) := by
    sorry

  /-- If for every direction d ∈ {(-1,0),(1,0),(0,-1),(0,1)}, the cell start + d is either out of bounds or maze[start + d] = 1, then the function returns false.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_5 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (hblocked : ∀ d : Dir,
        ¬ InBounds m n (shift (sr, sc) (Dir.vec d) 1) ∨
        CellWall maze (shift (sr, sc) (Dir.vec d) 1)) :
      has_path maze start destination = ok false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (hblocked : ∀ d : Dir,
          ¬ InBounds m n (shift (sr, sc) (Dir.vec d) 1) ∨
          CellWall maze (shift (sr, sc) (Dir.vec d) 1)), has_path maze start destination = ok false) := by
    sorry

  /-- If there is no finite sequence of rolls from start to destination (as defined in spec_1), then the function returns false.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_6 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (hnopath : ¬ RollReach maze m n (sr, sc) (dr, dc)) :
      has_path maze start destination = ok false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (hnopath : ¬ RollReach maze m n (sr, sc) (dr, dc)), has_path maze start destination = ok false) := by
    sorry

  /-- If the function returns true, then there exists a finite sequence of positions p0, p1, ..., pk (k >= 1) as in spec_3 such that all positions p0, p1, ..., pk are distinct.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_7 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      has_path maze start destination = ok true →
        ∃ t : Nat, ∃ ps : Nat → Position,
          IsRollSeq maze m n t ps ∧
          ps 0 = (sr, sc) ∧
          ps t = (dr, dc) ∧
          (∀ i : Nat, i ≤ t → InBounds m n (ps i) ∧ CellEmpty maze (ps i)) ∧
          (∀ i j : Nat, i ≤ t → j ≤ t → ps i = ps j → i = j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), has_path maze start destination = ok true →
          ∃ t : Nat, ∃ ps : Nat → Position,
            IsRollSeq maze m n t ps ∧
            ps 0 = (sr, sc) ∧
            ps t = (dr, dc) ∧
            (∀ i : Nat, i ≤ t → InBounds m n (ps i) ∧ CellEmpty maze (ps i)) ∧
            (∀ i j : Nat, i ≤ t → j ≤ t → ps i = ps j → i = j)) := by
    sorry

  /-- If the function returns true, then there exists a finite sequence of rolls from start to destination of length at most E, where E = |{(r,c) | 0 <= r < m, 0 <= c < n, maze[r][c] = 0}| (the number of empty cells in the maze).
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_8 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      has_path maze start destination = ok true →
        ∃ t : Nat, ∃ ps : Nat → Position,
          IsRollSeq maze m n t ps ∧
          ps 0 = (sr, sc) ∧
          ps t = (dr, dc) ∧
          t ≤ emptyCount maze m n := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), has_path maze start destination = ok true →
          ∃ t : Nat, ∃ ps : Nat → Position,
            IsRollSeq maze m n t ps ∧
            ps 0 = (sr, sc) ∧
            ps t = (dr, dc) ∧
            t ≤ emptyCount maze m n) := by
    sorry

  /-- Let maze' be the maze obtained by reflecting maze horizontally: for all 0 <= i < m, 0 <= j < n, maze'[i][j] = maze[i][n-1-j]. Let start' = (start[0], n-1-start[1]) and destination' = (destination[0], n-1-destination[1]). Then has_path(maze, start, destination) = has_path(maze', start', destination').
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_9 (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (hrefl : IsReflectH maze maze' m n)
      (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
      (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
      (hstart' : sr' = sr ∧ sc' = (n : Int) - 1 - sc)
      (hdest' : dr' = dr ∧ dc' = (n : Int) - 1 - dc) :
      has_path maze start destination = has_path maze' start' destination' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (hrefl : IsReflectH maze maze' m n)
        (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
        (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
        (hstart' : sr' = sr ∧ sc' = (n : Int) - 1 - sc)
        (hdest' : dr' = dr ∧ dc' = (n : Int) - 1 - dc), has_path maze start destination = has_path maze' start' destination') := by
    sorry

  /-- Let maze' be the maze obtained by reflecting maze vertically: for all 0 <= i < m, 0 <= j < n, maze'[i][j] = maze[m-1-i][j]. Let start' = (m-1-start[0], start[1]) and destination' = (m-1-destination[0], destination[1]). Then has_path(maze, start, destination) = has_path(maze', start', destination').
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_10 (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (hrefl : IsReflectV maze maze' m n)
      (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
      (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
      (hstart' : sr' = (m : Int) - 1 - sr ∧ sc' = sc)
      (hdest' : dr' = (m : Int) - 1 - dr ∧ dc' = dc) :
      has_path maze start destination = has_path maze' start' destination' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (hrefl : IsReflectV maze maze' m n)
        (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
        (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
        (hstart' : sr' = (m : Int) - 1 - sr ∧ sc' = sc)
        (hdest' : dr' = (m : Int) - 1 - dr ∧ dc' = dc), has_path maze start destination = has_path maze' start' destination') := by
    sorry

  /-- Let maze' be the transpose of maze: it has dimensions n × m, and for all 0 <= i < n, 0 <= j < m, maze'[i][j] = maze[j][i]. Let start' = (start[1], start[0]) and destination' = (destination[1], destination[0]). Then has_path(maze, start, destination) = has_path(maze', start', destination').
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_11 (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (htrans : IsTranspose maze maze' m n)
      (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
      (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
      (hstart' : sr' = sc ∧ sc' = sr)
      (hdest' : dr' = dc ∧ dc' = dr) :
      has_path maze start destination = has_path maze' start' destination' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (maze maze' : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination start' destination' : Slice I64) (sr sc dr dc sr' sc' dr' dc' : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (htrans : IsTranspose maze maze' m n)
        (hs' : start'.val.map (fun v => v.val) = [sr', sc'])
        (hd' : destination'.val.map (fun v => v.val) = [dr', dc'])
        (hstart' : sr' = sc ∧ sc' = sr)
        (hdest' : dr' = dc ∧ dc' = dr), has_path maze start destination = has_path maze' start' destination') := by
    sorry

  /-- Let S be any set of positions (pairs (r,c) with 0 <= r < m, 0 <= c < n) such that start is in S and S is closed under rolling: for every p in S, every direction d in {(-1,0),(1,0),(0,-1),(0,1)} and every q obtained by rolling from p in direction d (as defined in spec_1), q is in S. Then if destination is not in S the function returns false; equivalently, every position reachable from start by a finite roll sequence (as in spec_1) belongs to every such S (the reachable set is the least fixed point).
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_12 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n)
      (S : Set Position)
      (hSstart : (sr, sc) ∈ S)
      (hSclosed : ∀ p ∈ S, ∀ d : Dir, ∀ q : Position, RollsIn maze m n p d q → q ∈ S) :
      ((dr, dc) ∉ S → has_path maze start destination = ok false) ∧
      (∀ q : Position, RollReach maze m n (sr, sc) q → q ∈ S) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n)
        (S : Set Position)
        (hSstart : (sr, sc) ∈ S)
        (hSclosed : ∀ p ∈ S, ∀ d : Dir, ∀ q : Position, RollsIn maze m n p d q → q ∈ S), ((dr, dc) ∉ S → has_path maze start destination = ok false) ∧
        (∀ q : Position, RollReach maze m n (sr, sc) q → q ∈ S)) := by
    sorry

  /-- Let E = |{(r,c) | 0 <= r < m, 0 <= c < n, maze[r][c] = 0}|. For every position q that is the endpoint of a finite roll sequence starting at start (as defined in spec_1), q is the endpoint of such a sequence with at most E-1 rolls; consequently at most E positions are reachable by rolling from start. In particular, if the function returns true then there is a roll sequence from start to destination of length at most E-1.
    Preconditions: maze is an m x n rectangular grid of 0/1 with 1 <= m,n <= 100. start and destination are [row,col] with 0 <= row < m, 0 <= col < n. maze[start] = 0, maze[destination] = 0, start != destination. There are at least 2 empty cells. -/
  theorem spec_13 (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (start destination : Slice I64) (sr sc dr dc : Int)
      (hg : IsGrid maze m n)
      (hs : start.val.map (fun v => v.val) = [sr, sc])
      (hd : destination.val.map (fun v => v.val) = [dr, dc])
      (hsb : InBounds m n (sr, sc))
      (hdb : InBounds m n (dr, dc))
      (hse : CellEmpty maze (sr, sc))
      (hde : CellEmpty maze (dr, dc))
      (hne : (sr, sc) ≠ (dr, dc))
      (h2 : 2 ≤ emptyCount maze m n) :
      (∀ q : Position, RollReach maze m n (sr, sc) q →
        ∃ t : Nat, ∃ ps : Nat → Position,
          IsRollSeq maze m n t ps ∧ ps 0 = (sr, sc) ∧ ps t = q ∧
          t ≤ emptyCount maze m n - 1) ∧
      (∃ L : List Position,
        L.length ≤ emptyCount maze m n ∧
        ∀ q : Position, RollReach maze m n (sr, sc) q → q ∈ L) ∧
      (has_path maze start destination = ok true →
        ∃ t : Nat, ∃ ps : Nat → Position,
          IsRollSeq maze m n t ps ∧ ps 0 = (sr, sc) ∧ ps t = (dr, dc) ∧
          t ≤ emptyCount maze m n - 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (maze : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (start destination : Slice I64) (sr sc dr dc : Int)
        (hg : IsGrid maze m n)
        (hs : start.val.map (fun v => v.val) = [sr, sc])
        (hd : destination.val.map (fun v => v.val) = [dr, dc])
        (hsb : InBounds m n (sr, sc))
        (hdb : InBounds m n (dr, dc))
        (hse : CellEmpty maze (sr, sc))
        (hde : CellEmpty maze (dr, dc))
        (hne : (sr, sc) ≠ (dr, dc))
        (h2 : 2 ≤ emptyCount maze m n), (∀ q : Position, RollReach maze m n (sr, sc) q →
          ∃ t : Nat, ∃ ps : Nat → Position,
            IsRollSeq maze m n t ps ∧ ps 0 = (sr, sc) ∧ ps t = q ∧
            t ≤ emptyCount maze m n - 1) ∧
        (∃ L : List Position,
          L.length ≤ emptyCount maze m n ∧
          ∀ q : Position, RollReach maze m n (sr, sc) q → q ∈ L) ∧
        (has_path maze start destination = ok true →
          ∃ t : Nat, ∃ ps : Nat → Position,
            IsRollSeq maze m n t ps ∧ ps 0 = (sr, sc) ∧ ps t = (dr, dc) ∧
            t ≤ emptyCount maze m n - 1)) := by
    sorry

  end AegisSpec.HasPath
