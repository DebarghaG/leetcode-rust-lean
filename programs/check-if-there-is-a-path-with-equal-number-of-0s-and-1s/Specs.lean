import Aegis.IsThereAPath.Code.Funs

/-!
# Specifications of `Aegis.IsThereAPath.is_there_a_path`

LeetCode problem `check-if-there-is-a-path-with-equal-number-of-0s-and-1s`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsThereAPath

  abbrev Grid := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  def content (grid : Grid) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def cellOf (M : List (List Int)) (i j : Nat) : Int := (M.getD i []).getD j 0

  def cell (grid : Grid) (i j : Nat) : Int := cellOf (content grid) i j

  def IsBinaryMatrix (grid : Grid) (m n : Nat) : Prop :=
    (content grid).length = m ∧
      2 ≤ m ∧ m ≤ 100 ∧ 2 ≤ n ∧ n ≤ 100 ∧
        (∀ row ∈ content grid, row.length = n) ∧
          (∀ row ∈ content grid, ∀ x ∈ row, x = 0 ∨ x = 1)

  def IsMonotonePath (m n : Nat) (P : List (Nat × Nat)) : Prop :=
    P.head? = some (0, 0) ∧
      P.getLast? = some (m - 1, n - 1) ∧
        (∀ (k : Nat) (a b : Nat × Nat),
          P[k]? = some a → P[k + 1]? = some b →
            b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1))

  def pathOnes (grid : Grid) (P : List (Nat × Nat)) : Nat :=
    (P.filter (fun c => cell grid c.1 c.2 = 1)).length

  def pathZeros (grid : Grid) (P : List (Nat × Nat)) : Nat :=
    (P.filter (fun c => cell grid c.1 c.2 = 0)).length

  def sumRange (f : Nat → Int) (lo hi : Nat) : Int :=
    ((List.range (hi - lo)).map (fun k => f (lo + k))).sum

  def complementRows (M : List (List Int)) : List (List Int) :=
    M.map (fun row => row.map (fun x => 1 - x))

  def transposeRows (m n : Nat) (M : List (List Int)) : List (List Int) :=
    (List.range n).map (fun j => (List.range m).map (fun i => cellOf M i j))

  def flipRows (m n : Nat) (M : List (List Int)) : List (List Int) :=
    (List.range m).map
      (fun i => (List.range n).map (fun j => cellOf M (m - 1 - i) (n - 1 - j)))

  def rotateTransposeRows (m n : Nat) (M : List (List Int)) : List (List Int) :=
    (List.range n).map
      (fun r => (List.range m).map (fun c => cellOf M (m - 1 - c) (n - 1 - r)))

  /-- Whenever is_there_a_path(grid) returns a result r, we have r = true if and only if there exists a monotone path P from (0,0) to (m-1,n-1) such that ones(P) = zeros(P). Here a monotone path is a sequence of cells starting at (0,0), ending at (m-1,n-1), where each consecutive step is either (row+1,col) or (row,col+1); ones(P) is the number of visited cells with value 1, and zeros(P) is the number of visited cells with value 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_1 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n) :
      ∀ r : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          (r = true ↔
            ∃ P : List (Nat × Nat),
              IsMonotonePath m n P ∧ pathOnes grid P = pathZeros grid P) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n), ∀ r : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            (r = true ↔
              ∃ P : List (Nat × Nat),
                IsMonotonePath m n P ∧ pathOnes grid P = pathZeros grid P)) := by
    sorry

  /-- For every grid satisfying the preconditions, the call is_there_a_path(grid) returns a result r; it does not fail.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_2 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n) :
      ∃ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n), ∃ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r) := by
    sorry

  /-- If m+n is even, then whenever is_there_a_path(grid) returns a result r, r = false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_3 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hparity : Even (m + n)) :
      ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hparity : Even (m + n)), ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = false) := by
    sorry

  /-- Let comp be the m by n matrix defined by comp[i][j] = 1 - grid[i][j]. Whenever is_there_a_path(grid) returns r and is_there_a_path(comp) returns s, we have r = s.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_4 (grid comp : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hcomp : IsBinaryMatrix comp m n)
      (hdef : content comp = complementRows (content grid)) :
      ∀ r s : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          Aegis.IsThereAPath.is_there_a_path comp = ok s → r = s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid comp : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hcomp : IsBinaryMatrix comp m n)
        (hdef : content comp = complementRows (content grid)), ∀ r s : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            Aegis.IsThereAPath.is_there_a_path comp = ok s → r = s) := by
    sorry

  /-- Let T be the n by m matrix defined by T[j][i] = grid[i][j] for all 0 ≤ i < m and 0 ≤ j < n. Whenever is_there_a_path(grid) returns r and is_there_a_path(T) returns s, we have r = s.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_5 (grid T : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hT : IsBinaryMatrix T n m) (hdef : content T = transposeRows m n (content grid)) :
      ∀ r s : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          Aegis.IsThereAPath.is_there_a_path T = ok s → r = s := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid T : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hT : IsBinaryMatrix T n m) (hdef : content T = transposeRows m n (content grid)), ∀ r s : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            Aegis.IsThereAPath.is_there_a_path T = ok s → r = s) := by
    sorry

  /-- Let R be the m by n matrix defined by R[i][j] = grid[m-1-i][n-1-j] for all 0 ≤ i < m and 0 ≤ j < n. Whenever is_there_a_path(grid) returns r and is_there_a_path(R) returns s, we have r = s.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_6 (grid R : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hR : IsBinaryMatrix R m n) (hdef : content R = flipRows m n (content grid)) :
      ∀ r s : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          Aegis.IsThereAPath.is_there_a_path R = ok s → r = s := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid R : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hR : IsBinaryMatrix R m n) (hdef : content R = flipRows m n (content grid)), ∀ r s : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            Aegis.IsThereAPath.is_there_a_path R = ok s → r = s) := by
    sorry

  /-- Whenever is_there_a_path(grid) returns a result r, r = true if and only if n is odd and there exists an integer c with 0 ≤ c < n such that 2 * (sum_{j=0}^{c} grid[0][j] + sum_{j=c}^{n-1} grid[1][j]) = n+1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. Also assume m = 2. -/
  theorem spec_7 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n) (hm : m = 2) :
      ∀ r : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          (r = true ↔
            Odd n ∧
              ∃ c : Nat,
                0 ≤ c ∧ c < n ∧
                  2 * (sumRange (fun j => cell grid 0 j) 0 (c + 1) +
                        sumRange (fun j => cell grid 1 j) c n) = (n : Int) + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n) (hm : m = 2), ∀ r : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            (r = true ↔
              Odd n ∧
                ∃ c : Nat,
                  0 ≤ c ∧ c < n ∧
                    2 * (sumRange (fun j => cell grid 0 j) 0 (c + 1) +
                          sumRange (fun j => cell grid 1 j) c n) = (n : Int) + 1)) := by
    sorry

  /-- For a monotone path P define ones(P) as the number of visited cells with value 1 and zeros(P) as the number with value 0. If there exist monotone paths P and Q from (0,0) to (m-1,n-1) such that ones(P) < zeros(P) and ones(Q) > zeros(Q), then whenever is_there_a_path(grid) returns a result r, r = true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. Also assume m+n is odd. -/
  theorem spec_8 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hparity : Odd (m + n))
      (hP : ∃ P : List (Nat × Nat), IsMonotonePath m n P ∧ pathOnes grid P < pathZeros grid P)
      (hQ : ∃ Q : List (Nat × Nat), IsMonotonePath m n Q ∧ pathOnes grid Q > pathZeros grid Q) :
      ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hparity : Odd (m + n))
        (hP : ∃ P : List (Nat × Nat), IsMonotonePath m n P ∧ pathOnes grid P < pathZeros grid P)
        (hQ : ∃ Q : List (Nat × Nat), IsMonotonePath m n Q ∧ pathOnes grid Q > pathZeros grid Q), ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = true) := by
    sorry

  /-- For a monotone path P define ones(P) as the number of visited cells with value 1 and zeros(P) as the number with value 0. If either every monotone path P from (0,0) to (m-1,n-1) satisfies ones(P) > zeros(P), or every such P satisfies zeros(P) > ones(P), then whenever is_there_a_path(grid) returns a result r, r = false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_9 (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hall : (∀ P : List (Nat × Nat), IsMonotonePath m n P → pathOnes grid P > pathZeros grid P) ∨
        (∀ P : List (Nat × Nat), IsMonotonePath m n P → pathZeros grid P > pathOnes grid P)) :
      ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hall : (∀ P : List (Nat × Nat), IsMonotonePath m n P → pathOnes grid P > pathZeros grid P) ∨
          (∀ P : List (Nat × Nat), IsMonotonePath m n P → pathZeros grid P > pathOnes grid P)), ∀ r : Bool, Aegis.IsThereAPath.is_there_a_path grid = ok r → r = false) := by
    sorry

  /-- Let U be the n by m matrix defined by U[r][c] = grid[m-1-c][n-1-r] for all 0 ≤ r < n and 0 ≤ c < m. Whenever is_there_a_path(grid) returns r and is_there_a_path(U) returns s, we have r = s.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is an m by n binary matrix as in the constraints: all rows have length n, 2 ≤ m,n ≤ 100, and every entry grid[i][j] is 0 or 1. -/
  theorem spec_10 (grid U : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
      (hU : IsBinaryMatrix U n m) (hdef : content U = rotateTransposeRows m n (content grid)) :
      ∀ r s : Bool,
        Aegis.IsThereAPath.is_there_a_path grid = ok r →
          Aegis.IsThereAPath.is_there_a_path U = ok s → r = s := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid U : Grid) (m n : Nat) (hgrid : IsBinaryMatrix grid m n)
        (hU : IsBinaryMatrix U n m) (hdef : content U = rotateTransposeRows m n (content grid)), ∀ r s : Bool,
          Aegis.IsThereAPath.is_there_a_path grid = ok r →
            Aegis.IsThereAPath.is_there_a_path U = ok s → r = s) := by
    sorry

  end AegisSpec.IsThereAPath
