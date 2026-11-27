import Aegis.UniquePathsWithObstacles.Code.Funs

/-!
# Specifications of `Aegis.UniquePathsWithObstacles.unique_paths_with_obstacles`

LeetCode problem `unique-paths-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.UniquePathsWithObstacles (unique_paths_with_obstacles)

  namespace AegisSpec.UniquePathsWithObstacles

  def cells (m n : Nat) : List (Nat × Nat) :=
    (List.range m).flatMap fun i => (List.range n).map fun j => (i, j)

  def seqsOfLen {α : Type} (l : List α) : Nat → List (List α)
    | 0 => [[]]
    | k + 1 => (seqsOfLen l k).flatMap fun s => l.map fun a => a :: s

  def IsFreePath (m n : Nat) (g : Nat → Nat → Int) (p : List (Nat × Nat)) : Prop :=
    p.length = (m + n - 2) + 1 ∧
      p.head? = some (0, 0) ∧
      p.getLast? = some (m - 1, n - 1) ∧
      (∀ q ∈ p, q.1 < m ∧ q.2 < n ∧ g q.1 q.2 = 0) ∧
      (∀ t ∈ List.range (m + n - 2), ∀ a b : Nat × Nat,
        p[t]? = some a → p[t + 1]? = some b →
          b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1))

  def isFreePathB (m n : Nat) (g : Nat → Nat → Int) (p : List (Nat × Nat)) : Bool :=
    (p.length == (m + n - 2) + 1) &&
      (p.head? == some (0, 0)) &&
      (p.getLast? == some (m - 1, n - 1)) &&
      (p.all fun q => decide (q.1 < m) && decide (q.2 < n) && decide (g q.1 q.2 = 0)) &&
      ((p.zip p.tail).all fun ab =>
        decide (ab.2 = (ab.1.1 + 1, ab.1.2) ∨ ab.2 = (ab.1.1, ab.1.2 + 1)))

  def numFreePaths (m n : Nat) (g : Nat → Nat → Int) : Nat :=
    ((seqsOfLen (cells m n) ((m + n - 2) + 1)).filter (isFreePathB m n g)).length

  def gridRow (grid : List (alloc.vec.Vec I64)) (i : Nat) : List Int :=
    match grid[i]? with
    | some row => row.val.map fun x => x.val
    | none => []

  def entry (grid : List (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    match (gridRow grid i)[j]? with
    | some x => x
    | none => 0

  /-- The function returns a result r and r = P, where P is the number of sequences of positions (i_0,j_0),...,(i_k,j_k) such that k = m+n-2, (i_0,j_0) = (0,0), (i_k,j_k) = (m-1,n-1), for every t with 0 <= t <= k we have 0 <= i_t < m, 0 <= j_t < n, and obstacleGrid[i_t][j_t] = 0, and for every t with 0 <= t < k either (i_{t+1},j_{t+1}) = (i_t+1,j_t) or (i_{t+1},j_{t+1}) = (i_t,j_t+1).
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, and the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9. -/
  theorem spec_1
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9) :
      ∃ r : I64, unique_paths_with_obstacles obstacleGrid = ok r ∧
        r.val = (numFreePaths m n (entry obstacleGrid.val) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9), ∃ r : I64, unique_paths_with_obstacles obstacleGrid = ok r ∧
          r.val = (numFreePaths m n (entry obstacleGrid.val) : Int)) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(obstacleGrid) returns a result r, 0 <= r <= 2*10^9.
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, and the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9. -/
  theorem spec_2
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9) :
      ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
        0 ≤ r.val ∧ r.val ≤ (2 * 10 ^ 9 : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9), ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
          0 ≤ r.val ∧ r.val ≤ (2 * 10 ^ 9 : Int)) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(obstacleGrid) returns a result r, r <= binom(m+n-2, m-1), where binom(a,b) denotes the mathematical binomial coefficient counting all down/right paths from (0,0) to (m-1,n-1) when no cell is blocked.
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, and the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9. -/
  theorem spec_3
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9) :
      ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
        r.val ≤ (Nat.choose (m + n - 2) (m - 1) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9), ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
          r.val ≤ (Nat.choose (m + n - 2) (m - 1) : Int)) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(obstacleGrid) returns a result r, r = binom(m+n-2, m-1), where binom(a,b) is the mathematical binomial coefficient.
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9, and obstacleGrid[i][j] = 0 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9)
      (hfree : ∀ i j, i < m → j < n → entry obstacleGrid.val i j = 0) :
      ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
        r.val = (Nat.choose (m + n - 2) (m - 1) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9)
        (hfree : ∀ i j, i < m → j < n → entry obstacleGrid.val i j = 0), ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
          r.val = (Nat.choose (m + n - 2) (m - 1) : Int)) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(obstacleGrid) returns a result r, r = binom(m+n-2, m-1) - binom(i+j, i) * binom(m+n-2-i-j, m-1-i).
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9, and there is exactly one pair (i,j) with 0 <= i < m and 0 <= j < n such that obstacleGrid[i][j] = 1; denote this pair by (i,j). -/
  theorem spec_5
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9) :
      ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
        ∀ i j : Nat, i < m → j < n → entry obstacleGrid.val i j = 1 →
          (∀ i' j', i' < m → j' < n → entry obstacleGrid.val i' j' = 1 →
            i' = i ∧ j' = j) →
          r.val = (Nat.choose (m + n - 2) (m - 1) : Int) -
            (Nat.choose (i + j) i : Int) *
              (Nat.choose (m + n - 2 - i - j) (m - 1 - i) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9), ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
          ∀ i j : Nat, i < m → j < n → entry obstacleGrid.val i j = 1 →
            (∀ i' j', i' < m → j' < n → entry obstacleGrid.val i' j' = 1 →
              i' = i ∧ j' = j) →
            r.val = (Nat.choose (m + n - 2) (m - 1) : Int) -
              (Nat.choose (i + j) i : Int) *
                (Nat.choose (m + n - 2 - i - j) (m - 1 - i) : Int)) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(G) returns r_G and unique_paths_with_obstacles(H) returns r_H, r_G = r_H.
    Preconditions: Let m and n be integers with 1 <= m <= 100 and 1 <= n <= 100. Let G be an m x n grid (array of m rows, each of length n) with every entry either 0 or 1, and assume the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) in G is at most 2*10^9. Let H be the n x m grid defined by H[j][i] = G[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6
      (G H : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hmG : m = G.val.length)
      (hnG : ∀ row ∈ G.val, row.val.length = n)
      (hmH : n = H.val.length)
      (hnH : ∀ row ∈ H.val, row.val.length = m)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hentriesG : ∀ i j, i < m → j < n →
        entry G.val i j = 0 ∨ entry G.val i j = 1)
      (hboundG : numFreePaths m n (entry G.val) ≤ 2 * 10 ^ 9)
      (htranspose : ∀ i j, i < m → j < n → entry H.val j i = entry G.val i j) :
      ∀ rG rH : I64, unique_paths_with_obstacles G = ok rG →
        unique_paths_with_obstacles H = ok rH → rG = rH := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (G H : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hmG : m = G.val.length)
        (hnG : ∀ row ∈ G.val, row.val.length = n)
        (hmH : n = H.val.length)
        (hnH : ∀ row ∈ H.val, row.val.length = m)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hentriesG : ∀ i j, i < m → j < n →
          entry G.val i j = 0 ∨ entry G.val i j = 1)
        (hboundG : numFreePaths m n (entry G.val) ≤ 2 * 10 ^ 9)
        (htranspose : ∀ i j, i < m → j < n → entry H.val j i = entry G.val i j), ∀ rG rH : I64, unique_paths_with_obstacles G = ok rG →
          unique_paths_with_obstacles H = ok rH → rG = rH) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(A) returns r_A and unique_paths_with_obstacles(B) returns r_B, r_B <= r_A.
    Preconditions: Let m and n be integers with 1 <= m <= 100 and 1 <= n <= 100. Let A and B be m x n grids (arrays of m rows, each of length n) with every entry either 0 or 1, and assume the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9 in A and in B. Suppose A[i][j] <= B[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7
      (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hmA : m = A.val.length)
      (hnA : ∀ row ∈ A.val, row.val.length = n)
      (hmB : m = B.val.length)
      (hnB : ∀ row ∈ B.val, row.val.length = n)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hentriesA : ∀ i j, i < m → j < n →
        entry A.val i j = 0 ∨ entry A.val i j = 1)
      (hentriesB : ∀ i j, i < m → j < n →
        entry B.val i j = 0 ∨ entry B.val i j = 1)
      (hboundA : numFreePaths m n (entry A.val) ≤ 2 * 10 ^ 9)
      (hboundB : numFreePaths m n (entry B.val) ≤ 2 * 10 ^ 9)
      (hmono : ∀ i j, i < m → j < n → entry A.val i j ≤ entry B.val i j) :
      ∀ rA rB : I64, unique_paths_with_obstacles A = ok rA →
        unique_paths_with_obstacles B = ok rB → rB ≤ rA := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hmA : m = A.val.length)
        (hnA : ∀ row ∈ A.val, row.val.length = n)
        (hmB : m = B.val.length)
        (hnB : ∀ row ∈ B.val, row.val.length = n)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hentriesA : ∀ i j, i < m → j < n →
          entry A.val i j = 0 ∨ entry A.val i j = 1)
        (hentriesB : ∀ i j, i < m → j < n →
          entry B.val i j = 0 ∨ entry B.val i j = 1)
        (hboundA : numFreePaths m n (entry A.val) ≤ 2 * 10 ^ 9)
        (hboundB : numFreePaths m n (entry B.val) ≤ 2 * 10 ^ 9)
        (hmono : ∀ i j, i < m → j < n → entry A.val i j ≤ entry B.val i j), ∀ rA rB : I64, unique_paths_with_obstacles A = ok rA →
          unique_paths_with_obstacles B = ok rB → rB ≤ rA) := by
    sorry

  /-- Whenever unique_paths_with_obstacles(obstacleGrid) returns a result r, r > 0 if and only if there exists at least one down/right path from (0,0) to (m-1,n-1) that stays in the grid and uses only cells with obstacleGrid[i][j] = 0.
    Preconditions: Let m = len(obstacleGrid) and n = len(obstacleGrid[0]). Assume m >= 1, n >= 1, m <= 100, n <= 100, every row obstacleGrid[i] has length n, every entry obstacleGrid[i][j] is either 0 or 1, and the number of down/right obstacle-free paths from (0,0) to (m-1,n-1) is at most 2*10^9. -/
  theorem spec_8
      (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = obstacleGrid.val.length)
      (hn : n = (obstacleGrid.val.headD default).val.length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
      (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
      (hentries : ∀ i j, i < m → j < n →
        entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
      (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9) :
      ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
        (0 < r.val ↔ ∃ p : List (Nat × Nat), IsFreePath m n (entry obstacleGrid.val) p) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (obstacleGrid : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = obstacleGrid.val.length)
        (hn : n = (obstacleGrid.val.headD default).val.length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hm100 : m ≤ 100) (hn100 : n ≤ 100)
        (hrows : ∀ row ∈ obstacleGrid.val, row.val.length = n)
        (hentries : ∀ i j, i < m → j < n →
          entry obstacleGrid.val i j = 0 ∨ entry obstacleGrid.val i j = 1)
        (hbound : numFreePaths m n (entry obstacleGrid.val) ≤ 2 * 10 ^ 9), ∀ r : I64, unique_paths_with_obstacles obstacleGrid = ok r →
          (0 < r.val ↔ ∃ p : List (Nat × Nat), IsFreePath m n (entry obstacleGrid.val) p)) := by
    sorry

  end AegisSpec.UniquePathsWithObstacles
