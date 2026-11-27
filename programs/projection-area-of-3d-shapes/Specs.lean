import Aegis.ProjectionArea.Code.Funs

/-!
# Specifications of `Aegis.ProjectionArea.projection_area`

LeetCode problem `projection-area-of-3d-shapes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.ProjectionArea

def nrows (g : Slice (alloc.vec.Vec I64)) : ℕ := g.val.length

def rowOf (g : Slice (alloc.vec.Vec I64)) (i : ℕ) : List I64 :=
  ((g.val[i]?).map (fun r => r.val)).getD []

def rowLen (g : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℕ := (rowOf g i).length

def ent (g : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
  (((rowOf g i)[j]?).map (fun v => v.val)).getD 0

def rowEnts (g : Slice (alloc.vec.Vec I64)) (i : ℕ) : List ℤ :=
  (List.range (nrows g)).map (fun j => ent g i j)

def colEnts (g : Slice (alloc.vec.Vec I64)) (j : ℕ) : List ℤ :=
  (List.range (nrows g)).map (fun i => ent g i j)

def entries (g : Slice (alloc.vec.Vec I64)) : List ℤ :=
  (List.range (nrows g)).flatMap (fun i => rowEnts g i)

def listMax (l : List ℤ) : ℤ := l.foldr max 0

def rowMax (g : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ := listMax (rowEnts g i)

def colMax (g : Slice (alloc.vec.Vec I64)) (j : ℕ) : ℤ := listMax (colEnts g j)

def maxEntry (g : Slice (alloc.vec.Vec I64)) : ℤ := listMax (entries g)

def posCount (g : Slice (alloc.vec.Vec I64)) : ℕ :=
  (entries g).countP (fun x => decide (0 < x))

def posRows (g : Slice (alloc.vec.Vec I64)) : ℕ :=
  (List.range (nrows g)).countP (fun i => (rowEnts g i).any (fun x => decide (0 < x)))

def posCols (g : Slice (alloc.vec.Vec I64)) : ℕ :=
  (List.range (nrows g)).countP (fun j => (colEnts g j).any (fun x => decide (0 < x)))

def Valid (g : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ nrows g ∧ nrows g ≤ 50 ∧
    (∀ i, i < nrows g → rowLen g i = nrows g) ∧
    (∀ i j, i < nrows g → j < nrows g → 0 ≤ ent g i j ∧ ent g i j ≤ 50)

/-- The function returns a result r (it does not fail), and r = |{(i,j) | 0 <= i < n and 0 <= j < n and grid[i][j] > 0}| + (sum_{i=0}^{n-1} max_{0 <= j < n} grid[i][j]) + (sum_{j=0}^{n-1} max_{0 <= i < n} grid[i][j]).
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        r.val = (posCount grid : ℤ)
          + (∑ i ∈ Finset.range (nrows grid), rowMax grid i)
          + (∑ j ∈ Finset.range (nrows grid), colMax grid j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        r.val = (posCount grid : ℤ)
          + (∑ i ∈ Finset.range (nrows grid), rowMax grid i)
          + (∑ j ∈ Finset.range (nrows grid), colMax grid j)) := by
  sorry

/-- Let M = max{grid[i][j] | 0 <= i < n and 0 <= j < n}, which exists because n >= 1. The function returns a result r and r >= 2*M + (if M > 0 then 1 else 0).
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        2 * maxEntry grid + (if 0 < maxEntry grid then 1 else 0) ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        2 * maxEntry grid + (if 0 < maxEntry grid then 1 else 0) ≤ r.val) := by
  sorry

/-- Let M = max{grid[i][j] | 0 <= i < n and 0 <= j < n}, and let z = |{(i,j) | 0 <= i < n and 0 <= j < n and grid[i][j] > 0}|. The function returns a result r and r <= z + 2*n*M.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        r.val ≤ (posCount grid : ℤ) + 2 * (nrows grid : ℤ) * maxEntry grid := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        r.val ≤ (posCount grid : ℤ) + 2 * (nrows grid : ℤ) * maxEntry grid) := by
  sorry

/-- Let z = |{(i,j) | 0 <= i < n and 0 <= j < n and grid[i][j] > 0}|. Let R = |{i | 0 <= i < n and there exists j with 0 <= j < n and grid[i][j] > 0}|. Let C = |{j | 0 <= j < n and there exists i with 0 <= i < n and grid[i][j] > 0}|. The function returns a result r and r >= z + R + C.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        (posCount grid : ℤ) + (posRows grid : ℤ) + (posCols grid : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        (posCount grid : ℤ) + (posRows grid : ℤ) + (posCols grid : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if for every i,j with 0 <= i < n and 0 <= j < n we have grid[i][j] = 0.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        (r.val = 0 ↔ ∀ i j, i < nrows grid → j < nrows grid → ent grid i j = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64,
      Aegis.ProjectionArea.projection_area grid = ok r ∧
        (r.val = 0 ↔ ∀ i j, i < nrows grid → j < nrows grid → ent grid i j = 0)) := by
  sorry

/-- Whenever the function returns r1 on grid1 and r2 on grid2, we have r1 <= r2.
  Preconditions: Let n = len(grid1) = len(grid2). Both grid1 and grid2 satisfy 1 <= n <= 50, every row has length n, and all entries are in {0,1,...,50}. Also, for every i,j with 0 <= i < n and 0 <= j < n we have grid1[i][j] <= grid2[i][j]. -/
theorem spec_6 (grid1 grid2 : Slice (alloc.vec.Vec I64))
    (hg1 : Valid grid1) (hg2 : Valid grid2) (hn : nrows grid1 = nrows grid2)
    (hle : ∀ i j, i < nrows grid1 → j < nrows grid1 → ent grid1 i j ≤ ent grid2 i j) :
    ∀ r1 r2 : I64,
      Aegis.ProjectionArea.projection_area grid1 = ok r1 →
        Aegis.ProjectionArea.projection_area grid2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid1 grid2 : Slice (alloc.vec.Vec I64))
    (hg1 : Valid grid1) (hg2 : Valid grid2) (hn : nrows grid1 = nrows grid2)
    (hle : ∀ i j, i < nrows grid1 → j < nrows grid1 → ent grid1 i j ≤ ent grid2 i j), ∀ r1 r2 : I64,
      Aegis.ProjectionArea.projection_area grid1 = ok r1 →
        Aegis.ProjectionArea.projection_area grid2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns r on grid and rt on gt, we have r = rt.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. Let gt be the n x n grid defined by gt[i][j] = grid[j][i] for all i,j with 0 <= i < n and 0 <= j < n. -/
theorem spec_7 (grid gt : Slice (alloc.vec.Vec I64))
    (hg : Valid grid) (hgt : Valid gt) (hn : nrows gt = nrows grid)
    (htrans : ∀ i j, i < nrows grid → j < nrows grid → ent gt i j = ent grid j i) :
    ∀ r rt : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area gt = ok rt → r.val = rt.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid gt : Slice (alloc.vec.Vec I64))
    (hg : Valid grid) (hgt : Valid gt) (hn : nrows gt = nrows grid)
    (htrans : ∀ i j, i < nrows grid → j < nrows grid → ent gt i j = ent grid j i), ∀ r rt : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area gt = ok rt → r.val = rt.val) := by
  sorry

/-- Whenever the function returns r on grid and r' on grid', we have r = r'.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. Let pi be a permutation of {0,1,...,n-1}. Define grid'[i][j] = grid[pi(i)][j] for all i,j with 0 <= i < n and 0 <= j < n. -/
theorem spec_8 (grid g' : Slice (alloc.vec.Vec I64)) (pi : ℕ → ℕ)
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hpi : ∀ i, i < nrows grid → pi i < nrows grid)
    (hinj : ∀ i i', i < nrows grid → i' < nrows grid → pi i = pi i' → i = i')
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = ent grid (pi i) j) :
    ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid g' : Slice (alloc.vec.Vec I64)) (pi : ℕ → ℕ)
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hpi : ∀ i, i < nrows grid → pi i < nrows grid)
    (hinj : ∀ i i', i < nrows grid → i' < nrows grid → pi i = pi i' → i = i')
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = ent grid (pi i) j), ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' → r.val = r'.val) := by
  sorry

/-- Let z = |{(i,j) | 0 <= i < n and 0 <= j < n and grid[i][j] > 0}|. Whenever the function returns r on grid and r' on grid', we have r' = z + k*(r - z).
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. Let k be an integer with k >= 1 such that k*grid[i][j] <= 50 for every i,j with 0 <= i < n and 0 <= j < n. Define grid'[i][j] = k*grid[i][j] for all i,j. -/
theorem spec_9 (grid g' : Slice (alloc.vec.Vec I64)) (k : ℤ)
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hk : 1 ≤ k)
    (hkmul : ∀ i j, i < nrows grid → j < nrows grid → k * ent grid i j ≤ 50)
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = k * ent grid i j) :
    ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' →
          r'.val = (posCount grid : ℤ) + k * (r.val - (posCount grid : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid g' : Slice (alloc.vec.Vec I64)) (k : ℤ)
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hk : 1 ≤ k)
    (hkmul : ∀ i j, i < nrows grid → j < nrows grid → k * ent grid i j ≤ 50)
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = k * ent grid i j), ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' →
          r'.val = (posCount grid : ℤ) + k * (r.val - (posCount grid : ℤ))) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 50. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid) :
    ∃ r : I64, Aegis.ProjectionArea.projection_area grid = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hg : Valid grid), ∃ r : I64, Aegis.ProjectionArea.projection_area grid = ok r) := by
  sorry

/-- Let z = |{(i,j) | 0 <= i < n and 0 <= j < n and grid[i][j] > 0}|. Whenever the function returns r on grid and r' on grid', we have r' = r - z + n*n + 2*n.
  Preconditions: Let n = len(grid). The input satisfies 1 <= n <= 50, for every i with 0 <= i < n we have len(grid[i]) = n, and for every i,j with 0 <= i < n and 0 <= j < n we have 0 <= grid[i][j] <= 49. Define grid'[i][j] = grid[i][j] + 1 for all i,j. -/
theorem spec_11 (grid g' : Slice (alloc.vec.Vec I64))
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hle49 : ∀ i j, i < nrows grid → j < nrows grid → ent grid i j ≤ 49)
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = ent grid i j + 1) :
    ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' →
          r'.val =
            r.val - (posCount grid : ℤ) + (nrows grid : ℤ) * (nrows grid : ℤ)
              + 2 * (nrows grid : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid g' : Slice (alloc.vec.Vec I64))
    (hg : Valid grid) (hg' : Valid g') (hn : nrows g' = nrows grid)
    (hle49 : ∀ i j, i < nrows grid → j < nrows grid → ent grid i j ≤ 49)
    (hgrid' : ∀ i j, i < nrows grid → j < nrows grid → ent g' i j = ent grid i j + 1), ∀ r r' : I64,
      Aegis.ProjectionArea.projection_area grid = ok r →
        Aegis.ProjectionArea.projection_area g' = ok r' →
          r'.val =
            r.val - (posCount grid : ℤ) + (nrows grid : ℤ) * (nrows grid : ℤ)
              + 2 * (nrows grid : ℤ)) := by
  sorry

end AegisSpec.ProjectionArea
