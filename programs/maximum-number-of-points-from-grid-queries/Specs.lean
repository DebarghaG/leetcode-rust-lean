import Aegis.MaxPoints.Code.Funs

/-!
# Specifications of `Aegis.MaxPoints.max_points`

LeetCode problem `maximum-number-of-points-from-grid-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPoints

abbrev Grid := Slice (alloc.vec.Vec I64)

abbrev AnswerVec := alloc.vec.Vec I64

def numRows (grid : Grid) : ℕ := grid.length

def numQueries (queries : Slice I64) : ℕ := queries.length

def rowsOf (grid : Grid) : List (alloc.vec.Vec I64) := grid.val

def rowLen (grid : Grid) (r : ℕ) : ℕ := ((rowsOf grid).getD r default).length

def numCols (grid : Grid) : ℕ := rowLen grid 0

def cellVal (grid : Grid) (r c : ℕ) : ℤ := (((rowsOf grid).getD r default).val.getD c default).val

def queryVal (queries : Slice I64) (i : ℕ) : ℤ := (queries.val.getD i default).val

def answerList (ans : AnswerVec) : List ℤ := ans.val.map (fun x => x.val)

def answerVal (ans : AnswerVec) (i : ℕ) : ℤ := (ans.val.getD i default).val

@[simp] theorem numRows_eq_length (grid : Grid) : numRows grid = grid.val.length := rfl

@[simp] theorem rowLen_eq_length (grid : Grid) (r : ℕ) (h : r < numRows grid) :
    rowLen grid r = (rowsOf grid)[r].length := by
  simp only [rowLen, rowsOf, List.getD, List.getElem?_eq_getElem h, Option.getD_some]
  rfl

@[simp] theorem queryVal_eq_getElem (queries : Slice I64) (i : ℕ) (h : i < numQueries queries) :
    queryVal queries i = queries.val[i].val := by
  simp [queryVal, List.getElem?_eq_getElem h]

@[simp] theorem answerList_length (ans : AnswerVec) : (answerList ans).length = ans.length := by
  simp [answerList]

noncomputable def countCells (m n : ℕ) (P : ℕ → ℕ → Prop) : ℕ := by
  classical
  exact ((List.range m).product (List.range n)).countP (fun p => decide (P p.1 p.2))

def Adjacent (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

def AdjacentChain : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Adjacent p q ∧ AdjacentChain (q :: rest)

def IsLowWalk (grid : Grid) (m n : ℕ) (qv : ℤ) (path : List (ℕ × ℕ)) : Prop :=
  path ≠ [] ∧
    path.head? = some (0, 0) ∧
    AdjacentChain path ∧
    ∀ p ∈ path, p.1 < m ∧ p.2 < n ∧ cellVal grid p.1 p.2 < qv

def LowReach (grid : Grid) (m n : ℕ) (qv : ℤ) (r c : ℕ) : Prop :=
  r < m ∧ c < n ∧ ∃ path : List (ℕ × ℕ), IsLowWalk grid m n qv path ∧ path.getLast? = some (r, c)

/-- Whenever max_points returns a result ans, len(ans) = k and for every i with 0 <= i < k, ans[i] is equal to the number of pairs (r,c) such that 0 <= r < m, 0 <= c < n, and there exists a finite sequence of cells (r_0,c_0), ..., (r_t,c_t) with t >= 0, (r_0,c_0) = (0,0), (r_t,c_t) = (r,c), each consecutive pair differing by exactly 1 in one coordinate and 0 in the other, and grid[r_s][c_s] < queries[i] for every s with 0 <= s <= t.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_1 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      (answerList ans).length = numQueries queries ∧
        ∀ i, i < numQueries queries →
          answerVal ans i =
            ((countCells (numRows grid) n
              (fun r c => LowReach grid (numRows grid) n (queryVal queries i) r c) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      (answerList ans).length = numQueries queries ∧
        ∀ i, i < numQueries queries →
          answerVal ans i =
            ((countCells (numRows grid) n
              (fun r c => LowReach grid (numRows grid) n (queryVal queries i) r c) : ℕ) : ℤ)) := by
  sorry

/-- Under the preconditions, max_points returns a result ans; it does not panic, fail an overflow check, or access grid, a row of grid, or queries out of bounds.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_2 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∃ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∃ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans) := by
  sorry

/-- Whenever max_points returns a result ans, len(ans) = len(queries) = k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_3 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      (answerList ans).length = numQueries queries := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      (answerList ans).length = numQueries queries) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, 0 <= ans[i] <= m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_4 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        0 ≤ answerVal ans i ∧ answerVal ans i ≤ ((numRows grid * n : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        0 ≤ answerVal ans i ∧ answerVal ans i ≤ ((numRows grid * n : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, ans[i] <= N_i, where N_i is the number of pairs (r,c) with 0 <= r < m, 0 <= c < n, and grid[r][c] < queries[i].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_5 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        answerVal ans i ≤
          ((countCells (numRows grid) n (fun r c => cellVal grid r c < queryVal queries i) : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        answerVal ans i ≤
          ((countCells (numRows grid) n (fun r c => cellVal grid r c < queryVal queries i) : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, ans[i] = 0 if and only if queries[i] <= grid[0][0].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_6 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → (answerVal ans i = 0 ↔ queryVal queries i ≤ cellVal grid 0 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → (answerVal ans i = 0 ↔ queryVal queries i ≤ cellVal grid 0 0)) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, if queries[i] > grid[r][c] for all r,c with 0 <= r < m and 0 <= c < n, then ans[i] = m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_7 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        (∀ r c, r < numRows grid → c < n → cellVal grid r c < queryVal queries i) →
        answerVal ans i = ((numRows grid * n : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        (∀ r c, r < numRows grid → c < n → cellVal grid r c < queryVal queries i) →
        answerVal ans i = ((numRows grid * n : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_points returns a result ans, for all i,j with 0 <= i < k and 0 <= j < k, if queries[i] <= queries[j], then ans[i] <= ans[j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_8 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i j, i < numQueries queries → j < numQueries queries →
        queryVal queries i ≤ queryVal queries j → answerVal ans i ≤ answerVal ans j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i j, i < numQueries queries → j < numQueries queries →
        queryVal queries i ≤ queryVal queries j → answerVal ans i ≤ answerVal ans j) := by
  sorry

/-- Whenever max_points returns a result ans, for all i,j with 0 <= i < k and 0 <= j < k, if for every r,c with 0 <= r < m and 0 <= c < n the condition grid[r][c] < queries[i] holds exactly when grid[r][c] < queries[j] holds, then ans[i] = ans[j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_9 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i j, i < numQueries queries → j < numQueries queries →
        (∀ r c, r < numRows grid → c < n →
          (cellVal grid r c < queryVal queries i ↔ cellVal grid r c < queryVal queries j)) →
        answerVal ans i = answerVal ans j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i j, i < numQueries queries → j < numQueries queries →
        (∀ r c, r < numRows grid → c < n →
          (cellVal grid r c < queryVal queries i ↔ cellVal grid r c < queryVal queries j)) →
        answerVal ans i = answerVal ans j) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k and ans[i] > 0, there exists a finite sequence of cells (r_0,c_0), ..., (r_t,c_t) such that (r_0,c_0) = (0,0), consecutive cells are adjacent in one of the four directions, grid[r_s][c_s] < queries[i] for every s with 0 <= s <= t, and the number of distinct cells among (r_0,c_0), ..., (r_t,c_t) is exactly ans[i].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_10 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → 0 < answerVal ans i →
        ∃ path : List (ℕ × ℕ),
          IsLowWalk grid (numRows grid) n (queryVal queries i) path ∧
            answerVal ans i = ((path.dedup.length : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → 0 < answerVal ans i →
        ∃ path : List (ℕ × ℕ),
          IsLowWalk grid (numRows grid) n (queryVal queries i) path ∧
            answerVal ans i = ((path.dedup.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k and every finite sequence of cells (r_0,c_0), ..., (r_t,c_t) with (r_0,c_0) = (0,0), consecutive cells adjacent in one of the four directions, and grid[r_s][c_s] < queries[i] for every s with 0 <= s <= t, the number of distinct cells among the sequence is at most ans[i].
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_11 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → ∀ path : List (ℕ × ℕ),
        IsLowWalk grid (numRows grid) n (queryVal queries i) path →
          ((path.dedup.length : ℕ) : ℤ) ≤ answerVal ans i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries → ∀ path : List (ℕ × ℕ),
        IsLowWalk grid (numRows grid) n (queryVal queries i) path →
          ((path.dedup.length : ℕ) : ℤ) ≤ answerVal ans i) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, if queries[i] > grid[0][0] and grid[r][c] >= queries[i] for every cell (r,c) other than (0,0), then ans[i] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. -/
theorem spec_12 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        cellVal grid 0 0 < queryVal queries i →
        (∀ r c, r < numRows grid → c < n → (r, c) ≠ (0, 0) →
          queryVal queries i ≤ cellVal grid r c) →
        answerVal ans i = 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        cellVal grid 0 0 < queryVal queries i →
        (∀ r c, r < numRows grid → c < n → (r, c) ≠ (0, 0) →
          queryVal queries i ≤ cellVal grid r c) →
        answerVal ans i = 1) := by
  sorry

/-- Whenever max_points returns a result ans, for every i with 0 <= i < k, ans[i] = 0 if queries[i] <= v, and ans[i] = m*n if queries[i] > v.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume m >= 1; n >= 1; every row grid[r] with 0 <= r < m has length exactly n; m*n <= 100000; for every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000; and k = len(queries) satisfies 1 <= k <= 10000. The entries of queries may be arbitrary 64-bit integers. All indices are 0-based. Additionally there is an integer v with 1 <= v <= 1000000 such that grid[r][c] = v for every r,c with 0 <= r < m and 0 <= c < n. -/
theorem spec_13 (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000)
    (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000)
    (hconst : ∀ r c, r < numRows grid → c < n → cellVal grid r c = v) :
    ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        (queryVal queries i ≤ v → answerVal ans i = 0) ∧
          (v < queryVal queries i → answerVal ans i = ((numRows grid * n : ℕ) : ℤ)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (queries : Slice I64) (n : ℕ)
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ n)
    (hrows : ∀ r, r < numRows grid → rowLen grid r = n)
    (hsize : numRows grid * n ≤ 100000)
    (hbound : ∀ r c, r < numRows grid → c < n →
      1 ≤ cellVal grid r c ∧ cellVal grid r c ≤ 1000000)
    (hk1 : 1 ≤ numQueries queries) (hk2 : numQueries queries ≤ 10000)
    (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000)
    (hconst : ∀ r c, r < numRows grid → c < n → cellVal grid r c = v), ∀ ans : AnswerVec, Aegis.MaxPoints.max_points grid queries = ok ans →
      ∀ i, i < numQueries queries →
        (queryVal queries i ≤ v → answerVal ans i = 0) ∧
          (v < queryVal queries i → answerVal ans i = ((numRows grid * n : ℕ) : ℤ))) := by
  sorry

end AegisSpec.MaxPoints
