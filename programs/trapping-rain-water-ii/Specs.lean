import Aegis.TrapRainWater.Code.Funs

/-!
# Specifications of `Aegis.TrapRainWater.trap_rain_water`

LeetCode problem `trapping-rain-water-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TrapRainWater

def row (heightMap : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
  match heightMap.val[i]? with
  | some r => r.val.map (fun x => x.val)
  | none => []

def cell (heightMap : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  (row heightMap i).getD j 0

def InGrid (m n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < m ∧ p.2 < n

def OnBoundary (m n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 = 0 ∨ p.1 = m - 1 ∨ p.2 = 0 ∨ p.2 = n - 1

def IsCorner (m n : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 = n - 1) ∨
  (p.1 = m - 1 ∧ p.2 = 0) ∨ (p.1 = m - 1 ∧ p.2 = n - 1)

def IsInterior (m n : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.1 < m - 1 ∧ 0 < p.2 ∧ p.2 < n - 1

instance instDecidableInGrid (m n : ℕ) (p : ℕ × ℕ) : Decidable (InGrid m n p) := by
  unfold InGrid; infer_instance

instance instDecidableOnBoundary (m n : ℕ) (p : ℕ × ℕ) : Decidable (OnBoundary m n p) := by
  unfold OnBoundary; infer_instance

instance instDecidableIsCorner (m n : ℕ) (p : ℕ × ℕ) : Decidable (IsCorner m n p) := by
  unfold IsCorner; infer_instance

instance instDecidableIsInterior (m n : ℕ) (p : ℕ × ℕ) : Decidable (IsInterior m n p) := by
  unfold IsInterior; infer_instance

def cells (m n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range m ×ˢ Finset.range n

def interiorCells (m n : ℕ) : Finset (ℕ × ℕ) :=
  (cells m n).filter (fun p => IsInterior m n p)

def nonCornerBoundaryCells (m n : ℕ) : Finset (ℕ × ℕ) :=
  (cells m n).filter (fun p => OnBoundary m n p ∧ ¬ IsCorner m n p)

def Adjacent (p q : ℕ × ℕ) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
  (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨ (p.1 = q.1 ∧ q.2 + 1 = p.2)

def IsPath (m n : ℕ) (p : ℕ × ℕ) (path : List (ℕ × ℕ)) : Prop :=
  path.head? = some p ∧
  (∀ q ∈ path, InGrid m n q) ∧
  (∀ (k : ℕ) (a b : ℕ × ℕ), path[k]? = some a → path[k + 1]? = some b → Adjacent a b) ∧
  ∃ last, path.getLast? = some last ∧ OnBoundary m n last

def pathMax (h : ℕ → ℕ → ℤ) (path : List (ℕ × ℕ)) : ℤ :=
  match path with
  | [] => 0
  | q :: qs => qs.foldl (fun acc r => max acc (h r.1 r.2)) (h q.1 q.2)

def IsSpill (m n : ℕ) (h : ℕ → ℕ → ℤ) (p : ℕ × ℕ) (v : ℤ) : Prop :=
  (∃ path, IsPath m n p path ∧ pathMax h path = v) ∧
  ∀ w : ℤ, (∃ path, IsPath m n p path ∧ pathMax h path = w) → v ≤ w

noncomputable def spill (m n : ℕ) (h : ℕ → ℕ → ℤ) (p : ℕ × ℕ) : ℤ :=
  by classical
     exact if hex : ∃ v : ℤ, IsSpill m n h p v then hex.choose else 0

noncomputable def water (m n : ℕ) (h : ℕ → ℕ → ℤ) (p : ℕ × ℕ) : ℤ :=
  spill m n h p - h p.1 p.2

noncomputable def trappedWater (m n : ℕ) (h : ℕ → ℕ → ℤ) : ℤ :=
  ∑ p ∈ cells m n, water m n h p

noncomputable def gridMax (m n : ℕ) (h : ℕ → ℕ → ℤ) : ℤ :=
  by classical
     exact if hne : (cells m n).Nonempty then (cells m n).sup' hne (fun p => h p.1 p.2) else 0

noncomputable def boundaryMin (m n : ℕ) (h : ℕ → ℕ → ℤ) : ℤ :=
  by classical
     exact if hne : (nonCornerBoundaryCells m n).Nonempty then
       (nonCornerBoundaryCells m n).inf' hne (fun p => h p.1 p.2)
     else 0

def HeightMapPre (heightMap : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
  m = heightMap.val.length ∧
  1 ≤ m ∧ m ≤ 200 ∧
  n = (row heightMap 0).length ∧
  1 ≤ n ∧ n ≤ 200 ∧
  (∀ i, i < m → (row heightMap i).length = n) ∧
  (∀ i j, i < m → j < n → 0 ≤ cell heightMap i j ∧ cell heightMap i j ≤ 20000)

variable {heightMap : Slice (alloc.vec.Vec Std.I64)} {m n : ℕ}

/-- The function returns a result r and r = T, where T is defined as follows. For a cell (i,j) with 0 <= i < m and 0 <= j < n, a path from (i,j) to the boundary is a sequence of cells p_0, p_1, ..., p_k such that p_0 = (i,j), p_k is a boundary cell (i.e., p_k[0] = 0 or p_k[0] = m-1 or p_k[1] = 0 or p_k[1] = n-1), and for each 0 <= t < k, p_{t+1} is obtained from p_t by changing exactly one coordinate by +1 or -1 (so the cells are horizontally or vertically adjacent). The maximum height along such a path is max_{0 <= t <= k} heightMap[p_t[0]][p_t[1]]. Let spill(i,j) be the minimum over all paths from (i,j) to the boundary of the maximum height along the path. Let water(i,j) = spill(i,j) - heightMap[i][j]. Then T = sum_{0 <= i < m, 0 <= j < n} water(i,j).
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      r.val = trappedWater m n (cell heightMap) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      r.val = trappedWater m n (cell heightMap)) := by
  sorry

/-- The function returns a result r (it does not fail due to overflow, out-of-bounds access, or panic).
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= I * M, where I = max(0, m-2) * max(0, n-2) and M = max_{0 <= i < m, 0 <= j < n} heightMap[i][j].
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      r.val ≤ ((max 0 (m - 2) : ℕ) : ℤ) * ((max 0 (n - 2) : ℕ) : ℤ) *
        gridMax m n (cell heightMap) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      r.val ≤ ((max 0 (m - 2) : ℕ) : ℤ) * ((max 0 (n - 2) : ℕ) : ℤ) *
        gridMax m n (cell heightMap)) := by
  sorry

/-- If m <= 2 or n <= 2, then the function returns a result r and r = 0.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (hpre : HeightMapPre heightMap m n) (hthin : m ≤ 2 ∨ n ≤ 2) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n) (hthin : m ≤ 2 ∨ n ≤ 2), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ r.val = 0) := by
  sorry

/-- If there exists an integer h such that heightMap[i][j] = h for all 0 <= i < m and 0 <= j < n, then the function returns a result r and r = 0.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (hpre : HeightMapPre heightMap m n)
    (hconst : ∃ h : ℤ, ∀ i j, i < m → j < n → cell heightMap i j = h) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n)
    (hconst : ∃ h : ℤ, ∀ i j, i < m → j < n → cell heightMap i j = h), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧ r.val = 0) := by
  sorry

/-- If trap_rain_water(heightMap) returns r and trap_rain_water(heightMap') returns r', then r' = r.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. Let c be an integer and define heightMap' by heightMap'[i][j] = heightMap[i][j] + c for all i,j. Assume heightMap' also satisfies the problem's preconditions (i.e., it is a non-empty rectangular matrix with 0 <= heightMap'[i][j] <= 20000 for all i,j). -/
theorem spec_7 {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (c : ℤ) (hshift : ∀ i j, i < m → j < n → cell heightMap' i j = cell heightMap i j + c) :
    ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r'.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (c : ℤ) (hshift : ∀ i j, i < m → j < n → cell heightMap' i j = cell heightMap i j + c), ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r'.val = r.val) := by
  sorry

/-- If trap_rain_water(heightMap) returns r and trap_rain_water(heightMap') returns r', then r' = c * r.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. Let c be a positive integer such that c * heightMap[i][j] <= 20000 for all i,j. Define heightMap' by heightMap'[i][j] = c * heightMap[i][j] for all i,j. Assume heightMap' satisfies the problem's preconditions (it does under the bound). -/
theorem spec_8 {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (c : ℕ) (hc : 0 < c)
    (hscale : ∀ i j, i < m → j < n → cell heightMap' i j = (c : ℤ) * cell heightMap i j)
    (hbound : ∀ i j, i < m → j < n → (c : ℤ) * cell heightMap i j ≤ 20000) :
    ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r'.val = (c : ℤ) * r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (c : ℕ) (hc : 0 < c)
    (hscale : ∀ i j, i < m → j < n → cell heightMap' i j = (c : ℤ) * cell heightMap i j)
    (hbound : ∀ i j, i < m → j < n → (c : ℤ) * cell heightMap i j ≤ 20000), ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r'.val = (c : ℤ) * r.val) := by
  sorry

/-- The function returns a result r and, if I is empty, r = 0; otherwise r = sum_{(i,j) in I} (B - heightMap[i][j]).
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. Assume that for every boundary cell b and every interior cell c, heightMap[b] >= heightMap[c]. Let I = { (i,j) | 0 < i < m-1 and 0 < j < n-1 } be the set of interior cells. If I is nonempty, let B be the minimum of heightMap[i][j] over all boundary cells (i,j) that are not one of the four corners (0,0), (0,n-1), (m-1,0), (m-1,n-1). -/
theorem spec_9 (hpre : HeightMapPre heightMap m n)
    (hdom : ∀ b, InGrid m n b → OnBoundary m n b → ∀ c, IsInterior m n c →
      cell heightMap c.1 c.2 ≤ cell heightMap b.1 b.2) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      ((interiorCells m n).Nonempty →
        r.val = ∑ p ∈ interiorCells m n,
          (boundaryMin m n (cell heightMap) - cell heightMap p.1 p.2)) ∧
      (interiorCells m n = ∅ → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n)
    (hdom : ∀ b, InGrid m n b → OnBoundary m n b → ∀ c, IsInterior m n c →
      cell heightMap c.1 c.2 ≤ cell heightMap b.1 b.2), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      ((interiorCells m n).Nonempty →
        r.val = ∑ p ∈ interiorCells m n,
          (boundaryMin m n (cell heightMap) - cell heightMap p.1 p.2)) ∧
      (interiorCells m n = ∅ → r.val = 0)) := by
  sorry

/-- If trap_rain_water(heightMap) returns r and trap_rain_water(heightMap') returns r', then r' >= r.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. Let heightMap' be another m x n matrix satisfying the problem's preconditions. Assume that for every interior cell (i,j), heightMap'[i][j] = heightMap[i][j], and for every boundary cell (i,j), heightMap'[i][j] >= heightMap[i][j]. -/
theorem spec_10 {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (hint : ∀ p, IsInterior m n p → cell heightMap' p.1 p.2 = cell heightMap p.1 p.2)
    (hbdy : ∀ p, InGrid m n p → OnBoundary m n p →
      cell heightMap p.1 p.2 ≤ cell heightMap' p.1 p.2) :
    ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ {heightMap' : Slice (alloc.vec.Vec Std.I64)}
    (hpre : HeightMapPre heightMap m n) (hpre' : HeightMapPre heightMap' m n)
    (hint : ∀ p, IsInterior m n p → cell heightMap' p.1 p.2 = cell heightMap p.1 p.2)
    (hbdy : ∀ p, InGrid m n p → OnBoundary m n p →
      cell heightMap p.1 p.2 ≤ cell heightMap' p.1 p.2), ∀ r r' : Std.I64,
      Aegis.TrapRainWater.trap_rain_water heightMap = ok r →
      Aegis.TrapRainWater.trap_rain_water heightMap' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and r > 0 if and only if there exists a cell (i,j) with 0 <= i < m and 0 <= j < n such that water(i,j) > 0, where for any cell (i,j), spill(i,j) is the minimum over all paths from (i,j) to a boundary cell of the maximum height along the path, and water(i,j) = spill(i,j) - heightMap[i][j].
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      (0 < r.val ↔ ∃ i j, i < m ∧ j < n ∧ 0 < water m n (cell heightMap) (i, j)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      (0 < r.val ↔ ∃ i j, i < m ∧ j < n ∧ 0 < water m n (cell heightMap) (i, j))) := by
  sorry

/-- The function returns a result r and for every cell (i,j) with 0 <= i < m and 0 <= j < n, water(i,j) <= r, where water(i,j) = spill(i,j) - heightMap[i][j] and spill(i,j) is the minimum over all paths from (i,j) to a boundary cell of the maximum height along the path.
  Preconditions: heightMap is a non-empty slice of non-empty Vec<I64>. Let m = len(heightMap) and n = len(heightMap[0]). Assume all rows of heightMap have length n, 1 <= m <= 200, 1 <= n <= 200, and 0 <= heightMap[i][j] <= 20000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (hpre : HeightMapPre heightMap m n) :
    ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      ∀ i j, i < m → j < n → water m n (cell heightMap) (i, j) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hpre : HeightMapPre heightMap m n), ∃ r : Std.I64, Aegis.TrapRainWater.trap_rain_water heightMap = ok r ∧
      ∀ i j, i < m → j < n → water m n (cell heightMap) (i, j) ≤ r.val) := by
  sorry

end AegisSpec.TrapRainWater
