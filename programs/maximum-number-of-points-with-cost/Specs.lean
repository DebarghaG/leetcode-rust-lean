import Aegis.MaxPoints.Code.Funs

/-!
# Specifications of `Aegis.MaxPoints.max_points`

LeetCode problem `maximum-number-of-points-with-cost`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxPoints

  def entries (points : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    points.val.map (fun v => v.slice.val.map (fun x => x.val))

  def numRows (points : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    (entries points).length

  def numCols (points : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((entries points).headD []).length

  def row (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    (entries points).getD i []

  def cell (points : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (row points i).getD j 0

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr min x

  def absDiff (a b : Nat) : Int :=
    (((a : Int) - (b : Int)).natAbs : Int)

  def rowMax (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    listMax (row points i)

  def rowMin (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    listMin (row points i)

  def colSum (points : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
    ((List.range (numRows points)).map (fun i => cell points i j)).sum

  def rowMaxSum (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
    ((List.range (numRows points)).map (fun i => rowMax points i)).sum

  def colMaxSum (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
    listMax ((List.range (numCols points)).map (fun j => colSum points j))

  def rowMinSum (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
    ((List.range (numRows points)).map (fun i => rowMin points i)).sum

  def IsColChoice (points : Slice (alloc.vec.Vec Std.I64)) (c : List Nat) : Prop :=
    c.length = numRows points ∧
      ∀ i : Nat, i < numRows points → c.getD i 0 < numCols points

  def score (points : Slice (alloc.vec.Vec Std.I64)) (c : List Nat) : Int :=
    ((List.range (numRows points)).map (fun i => cell points i (c.getD i 0))).sum -
      ((List.range (numRows points - 1)).map
        (fun i => absDiff (c.getD i 0) (c.getD (i + 1) 0))).sum

  def ValidInput (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ numRows points ∧
      1 ≤ numCols points ∧
      (∀ i : Nat, i < numRows points → (row points i).length = numCols points) ∧
      numRows points ≤ 100000 ∧
      numCols points ≤ 100000 ∧
      numRows points * numCols points ≤ 100000 ∧
      (∀ i j : Nat,
        i < numRows points → j < numCols points →
          0 ≤ cell points i j ∧ cell points i j ≤ 100000)

  /-- The function returns a result r (max_points points = ok r), and r is the maximum possible score. For a column choice c = (c_0,...,c_{m-1}) with 0 <= c_i < n for every i, define score(c) = (sum_{i=0}^{m-1} points[i][c_i]) - (sum_{i=0}^{m-2} abs(c_i - c_{i+1})). Then for every such c, score(c) <= r, and there exists at least one such c with score(c) = r.
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_1
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64,
        Aegis.MaxPoints.max_points points = ok r ∧
          (∀ c : List Nat, IsColChoice points c → score points c ≤ r.val) ∧
          (∃ c : List Nat, IsColChoice points c ∧ score points c = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64,
          Aegis.MaxPoints.max_points points = ok r ∧
            (∀ c : List Nat, IsColChoice points c → score points c ≤ r.val) ∧
            (∃ c : List Nat, IsColChoice points c ∧ score points c = r.val)) := by
    sorry

  /-- For every points satisfying the preconditions, max_points points returns a result r; that is, the call does not fail, panic, or overflow. No other property is claimed in this specification.
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_2
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64, Aegis.MaxPoints.max_points points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64, Aegis.MaxPoints.max_points points = ok r) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{m-1} (max_{0 <= j < n} points[i][j]).
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_3
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64,
        Aegis.MaxPoints.max_points points = ok r ∧ r.val ≤ rowMaxSum points := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64,
          Aegis.MaxPoints.max_points points = ok r ∧ r.val ≤ rowMaxSum points) := by
    sorry

  /-- The function returns a result r and r >= max_{0 <= j < n} (sum_{i=0}^{m-1} points[i][j]).
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_4
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64,
        Aegis.MaxPoints.max_points points = ok r ∧ colMaxSum points ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64,
          Aegis.MaxPoints.max_points points = ok r ∧ colMaxSum points ≤ r.val) := by
    sorry

  /-- The function returns a result r and r >= (sum_{i=0}^{m-1} (min_{0 <= j < n} points[i][j])) - (m-1)*(n-1).
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_5
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64,
        Aegis.MaxPoints.max_points points = ok r ∧
          rowMinSum points - ((numRows points : Int) - 1) * ((numCols points : Int) - 1) ≤
            r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64,
          Aegis.MaxPoints.max_points points = ok r ∧
            rowMinSum points - ((numRows points : Int) - 1) * ((numCols points : Int) - 1) ≤
              r.val) := by
    sorry

  /-- The function returns a result r. Let M = sum_{i=0}^{m-1} (max_{0 <= j < n} points[i][j]). Then r = M if and only if there exists a column j with 0 <= j < n such that for every i with 0 <= i < m, points[i][j] = max_{0 <= k < n} points[i][k].
    Preconditions: points is a nonempty slice of nonempty Vec<i64>. Let m = len(points) and n = len(points[0]). Every row of points has length n. The dimensions satisfy 1 <= m,n <= 10^5 and m*n <= 10^5. For every i,j with 0 <= i < m and 0 <= j < n, 0 <= points[i][j] <= 10^5. -/
  theorem spec_6
      (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points) :
      ∃ r : Std.I64,
        Aegis.MaxPoints.max_points points = ok r ∧
          (r.val = rowMaxSum points ↔
            ∃ j : Nat,
              j < numCols points ∧
                ∀ i : Nat, i < numRows points → cell points i j = rowMax points i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (hpoints : ValidInput points), ∃ r : Std.I64,
          Aegis.MaxPoints.max_points points = ok r ∧
            (r.val = rowMaxSum points ↔
              ∃ j : Nat,
                j < numCols points ∧
                  ∀ i : Nat, i < numRows points → cell points i j = rowMax points i)) := by
    sorry

  /-- Let rp be the result of max_points points and rq be the result of max_points q; both calls return results. Then rq >= rp.
    Preconditions: points and q are matrices satisfying the same preconditions, with common dimensions m = len(points) = len(q) and n = len(points[0]) = len(q[0]). There are indices a,b with 0 <= a < m and 0 <= b < n and an integer d >= 0 such that q[a][b] = points[a][b] + d and q[i][j] = points[i][j] for all other (i,j). -/
  theorem spec_7
      (points q : Slice (alloc.vec.Vec Std.I64))
      (hpoints : ValidInput points) (hq : ValidInput q)
      (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
      (a b : Nat) (d : Int)
      (ha : a < numRows points) (hb : b < numCols points) (hd : 0 ≤ d)
      (hinc : cell q a b = cell points a b + d)
      (hsame : ∀ i j : Nat,
        i < numRows points → j < numCols points → ¬ (i = a ∧ j = b) →
          cell q i j = cell points i j) :
      ∃ rp rq : Std.I64,
        Aegis.MaxPoints.max_points points = ok rp ∧
          Aegis.MaxPoints.max_points q = ok rq ∧ rp.val ≤ rq.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points q : Slice (alloc.vec.Vec Std.I64))
        (hpoints : ValidInput points) (hq : ValidInput q)
        (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
        (a b : Nat) (d : Int)
        (ha : a < numRows points) (hb : b < numCols points) (hd : 0 ≤ d)
        (hinc : cell q a b = cell points a b + d)
        (hsame : ∀ i j : Nat,
          i < numRows points → j < numCols points → ¬ (i = a ∧ j = b) →
            cell q i j = cell points i j), ∃ rp rq : Std.I64,
          Aegis.MaxPoints.max_points points = ok rp ∧
            Aegis.MaxPoints.max_points q = ok rq ∧ rp.val ≤ rq.val) := by
    sorry

  /-- Let rp be the result of max_points points and rq be the result of max_points q; both calls return results. Then rq <= rp + d.
    Preconditions: points and q are matrices satisfying the same preconditions, with common dimensions m = len(points) = len(q) and n = len(points[0]) = len(q[0]). There are indices a,b with 0 <= a < m and 0 <= b < n and an integer d >= 0 such that q[a][b] = points[a][b] + d and q[i][j] = points[i][j] for all other (i,j). -/
  theorem spec_8
      (points q : Slice (alloc.vec.Vec Std.I64))
      (hpoints : ValidInput points) (hq : ValidInput q)
      (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
      (a b : Nat) (d : Int)
      (ha : a < numRows points) (hb : b < numCols points) (hd : 0 ≤ d)
      (hinc : cell q a b = cell points a b + d)
      (hsame : ∀ i j : Nat,
        i < numRows points → j < numCols points → ¬ (i = a ∧ j = b) →
          cell q i j = cell points i j) :
      ∃ rp rq : Std.I64,
        Aegis.MaxPoints.max_points points = ok rp ∧
          Aegis.MaxPoints.max_points q = ok rq ∧ rq.val ≤ rp.val + d := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points q : Slice (alloc.vec.Vec Std.I64))
        (hpoints : ValidInput points) (hq : ValidInput q)
        (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
        (a b : Nat) (d : Int)
        (ha : a < numRows points) (hb : b < numCols points) (hd : 0 ≤ d)
        (hinc : cell q a b = cell points a b + d)
        (hsame : ∀ i j : Nat,
          i < numRows points → j < numCols points → ¬ (i = a ∧ j = b) →
            cell q i j = cell points i j), ∃ rp rq : Std.I64,
          Aegis.MaxPoints.max_points points = ok rp ∧
            Aegis.MaxPoints.max_points q = ok rq ∧ rq.val ≤ rp.val + d) := by
    sorry

  /-- Let rp be the result of max_points points and rq be the result of max_points q; both calls return results. Then rq = rp + k.
    Preconditions: points and q are matrices satisfying the same preconditions, with common dimensions m = len(points) = len(q) and n = len(points[0]) = len(q[0]). There is a row index a with 0 <= a < m and an integer k such that q[a][j] = points[a][j] + k for every j with 0 <= j < n, and q[i][j] = points[i][j] for all i with 0 <= i < m and i not equal to a. -/
  theorem spec_9
      (points q : Slice (alloc.vec.Vec Std.I64))
      (hpoints : ValidInput points) (hq : ValidInput q)
      (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
      (a : Nat) (k : Int)
      (ha : a < numRows points)
      (hrow : ∀ j : Nat, j < numCols points → cell q a j = cell points a j + k)
      (hsame : ∀ i j : Nat,
        i < numRows points → i ≠ a → j < numCols points →
          cell q i j = cell points i j) :
      ∃ rp rq : Std.I64,
        Aegis.MaxPoints.max_points points = ok rp ∧
          Aegis.MaxPoints.max_points q = ok rq ∧ rq.val = rp.val + k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points q : Slice (alloc.vec.Vec Std.I64))
        (hpoints : ValidInput points) (hq : ValidInput q)
        (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
        (a : Nat) (k : Int)
        (ha : a < numRows points)
        (hrow : ∀ j : Nat, j < numCols points → cell q a j = cell points a j + k)
        (hsame : ∀ i j : Nat,
          i < numRows points → i ≠ a → j < numCols points →
            cell q i j = cell points i j), ∃ rp rq : Std.I64,
          Aegis.MaxPoints.max_points points = ok rp ∧
            Aegis.MaxPoints.max_points q = ok rq ∧ rq.val = rp.val + k) := by
    sorry

  /-- Let rp be the result of max_points points and rq be the result of max_points q; both calls return results. Then rq = rp.
    Preconditions: points and q are matrices satisfying the same preconditions, with common dimensions m = len(points) = len(q) and n = len(points[0]) = len(q[0]). For every i,j with 0 <= i < m and 0 <= j < n, q[i][j] = points[i][n-1-j]. -/
  theorem spec_10
      (points q : Slice (alloc.vec.Vec Std.I64))
      (hpoints : ValidInput points) (hq : ValidInput q)
      (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
      (hrev : ∀ i j : Nat,
        i < numRows points → j < numCols points →
          cell q i j = cell points i (numCols points - 1 - j)) :
      ∃ rp rq : Std.I64,
        Aegis.MaxPoints.max_points points = ok rp ∧
          Aegis.MaxPoints.max_points q = ok rq ∧ rq.val = rp.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points q : Slice (alloc.vec.Vec Std.I64))
        (hpoints : ValidInput points) (hq : ValidInput q)
        (hrows : numRows points = numRows q) (hcols : numCols points = numCols q)
        (hrev : ∀ i j : Nat,
          i < numRows points → j < numCols points →
            cell q i j = cell points i (numCols points - 1 - j)), ∃ rp rq : Std.I64,
          Aegis.MaxPoints.max_points points = ok rp ∧
            Aegis.MaxPoints.max_points q = ok rq ∧ rq.val = rp.val) := by
    sorry

  end AegisSpec.MaxPoints
