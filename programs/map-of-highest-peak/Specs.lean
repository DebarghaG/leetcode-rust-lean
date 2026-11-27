import Aegis.HighestPeak.Code.Funs

/-!
# Specifications of `Aegis.HighestPeak.highest_peak`

LeetCode problem `map-of-highest-peak`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.HighestPeak

namespace AegisSpec.HighestPeak

def numRows (isWater : Slice (alloc.vec.Vec I64)) : Nat :=
  isWater.val.length

def numCols (isWater : Slice (alloc.vec.Vec I64)) : Nat :=
  match isWater.val with
  | [] => 0
  | row :: _ => row.val.length

def cell? (M : List (alloc.vec.Vec I64)) (i j : Nat) : Option Int :=
  (M[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

def cell (M : List (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  (cell? M i j).getD 0

def icell? (M : List (List Int)) (i j : Nat) : Option Int :=
  (M[i]?).bind (fun row => row[j]?)

def icell (M : List (List Int)) (i j : Nat) : Int :=
  (icell? M i j).getD 0

def maxInt (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl max x

def minNat (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def maxNat (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl Nat.max x

def toIntMat (M : List (alloc.vec.Vec I64)) : List (List Int) :=
  M.map (fun row => row.val.map (fun x => x.val))

def maxEntry (M : List (alloc.vec.Vec I64)) : Int :=
  maxInt (toIntMat M).flatten

def maxEntryI (M : List (List Int)) : Int :=
  maxInt M.flatten

def l1 (i j a b : Nat) : Nat :=
  Int.natAbs ((i : Int) - (a : Int)) + Int.natAbs ((j : Int) - (b : Int))

def IsWater (isWater : Slice (alloc.vec.Vec I64)) (a b : Nat) : Prop :=
  cell? isWater.val a b = some 1

def waterDists (isWater : Slice (alloc.vec.Vec I64)) (i j : Nat) : List Nat :=
  (List.range (numRows isWater)).flatMap (fun a =>
    (List.range (numCols isWater)).filterMap (fun b =>
      if cell? isWater.val a b = some 1 then some (l1 i j a b) else none))

def distToWater (isWater : Slice (alloc.vec.Vec I64)) (i j : Nat) : Nat :=
  minNat (waterDists isWater i j)

def maxDistToWater (isWater : Slice (alloc.vec.Vec I64)) : Nat :=
  maxNat ((List.range (numRows isWater)).flatMap (fun a =>
    (List.range (numCols isWater)).map (fun b => distToWater isWater a b)))

def Pre (isWater : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ numRows isWater ∧ numRows isWater ≤ 1000 ∧
  1 ≤ numCols isWater ∧ numCols isWater ≤ 1000 ∧
  (∀ row ∈ isWater.val, row.val.length = numCols isWater) ∧
  (∀ i j, i < numRows isWater → j < numCols isWater →
    cell? isWater.val i j = some 0 ∨ cell? isWater.val i j = some 1) ∧
  (∃ i j, i < numRows isWater ∧ j < numCols isWater ∧ IsWater isWater i j)

def HasLand (isWater : Slice (alloc.vec.Vec I64)) : Prop :=
  ∃ i j, i < numRows isWater ∧ j < numCols isWater ∧ cell? isWater.val i j = some 0

/-- Let W = {(a,b) | 0 <= a < m, 0 <= b < n, isWater[a][b] = 1}. For every cell (i,j), define d(i,j) = min over (a,b) in W of (|i-a| + |j-b|), and define D = max over 0 <= i < m and 0 <= j < n of d(i,j). The function returns a result height such that: len(height) = m; every row height[i] has length n; every entry height[i][j] is non-negative; height[i][j] = 0 whenever isWater[i][j] = 1; for every i,j with i+1 < m, |height[i+1][j] - height[i][j]| <= 1; for every i,j with j+1 < n, |height[i][j+1] - height[i][j]| <= 1; and the maximum entry of height is exactly D.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell, i.e. some i,j has isWater[i][j] = 1. -/
theorem spec_1 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater) :
    ∃ height : alloc.vec.Vec (alloc.vec.Vec I64),
      highest_peak isWater = ok height ∧
      height.val.length = numRows isWater ∧
      (∀ row ∈ height.val, row.val.length = numCols isWater) ∧
      (∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ cell height.val i j) ∧
      (∀ i j, i < numRows isWater → j < numCols isWater →
        IsWater isWater i j → cell height.val i j = 0) ∧
      (∀ i j, i + 1 < numRows isWater → j < numCols isWater →
        |cell height.val (i + 1) j - cell height.val i j| ≤ 1) ∧
      (∀ i j, i < numRows isWater → j + 1 < numCols isWater →
        |cell height.val i (j + 1) - cell height.val i j| ≤ 1) ∧
      maxEntry height.val = (maxDistToWater isWater : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater), ∃ height : alloc.vec.Vec (alloc.vec.Vec I64),
      highest_peak isWater = ok height ∧
      height.val.length = numRows isWater ∧
      (∀ row ∈ height.val, row.val.length = numCols isWater) ∧
      (∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ cell height.val i j) ∧
      (∀ i j, i < numRows isWater → j < numCols isWater →
        IsWater isWater i j → cell height.val i j = 0) ∧
      (∀ i j, i + 1 < numRows isWater → j < numCols isWater →
        |cell height.val (i + 1) j - cell height.val i j| ≤ 1) ∧
      (∀ i j, i < numRows isWater → j + 1 < numCols isWater →
        |cell height.val i (j + 1) - cell height.val i j| ≤ 1) ∧
      maxEntry height.val = (maxDistToWater isWater : Int)) := by
  sorry

/-- Whenever the function returns a result height, len(height) = m and for every i with 0 <= i < m, len(height[i]) = n.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_2 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    height.val.length = numRows isWater ∧
      (∀ row ∈ height.val, row.val.length = numCols isWater) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), height.val.length = numRows isWater ∧
      (∀ row ∈ height.val, row.val.length = numCols isWater)) := by
  sorry

/-- Whenever the function returns a result height, for every i,j with 0 <= i < m and 0 <= j < n, if isWater[i][j] = 1 then height[i][j] = 0.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_3 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i < numRows isWater → j < numCols isWater →
      IsWater isWater i j → cell height.val i j = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i < numRows isWater → j < numCols isWater →
      IsWater isWater i j → cell height.val i j = 0) := by
  sorry

/-- Whenever the function returns a result height, for every i,j with 0 <= i < m and 0 <= j < n, height[i][j] >= 0.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_4 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ cell height.val i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ cell height.val i j) := by
  sorry

/-- Whenever the function returns a result height, for every i,j with 0 <= i < m, 0 <= j < n, and i+1 < m, |height[i+1][j] - height[i][j]| <= 1.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_5 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i + 1 < numRows isWater → j < numCols isWater →
      |cell height.val (i + 1) j - cell height.val i j| ≤ 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i + 1 < numRows isWater → j < numCols isWater →
      |cell height.val (i + 1) j - cell height.val i j| ≤ 1) := by
  sorry

/-- Whenever the function returns a result height, for every i,j with 0 <= i < m, 0 <= j < n, and j+1 < n, |height[i][j+1] - height[i][j]| <= 1.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_6 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i < numRows isWater → j + 1 < numCols isWater →
      |cell height.val i (j + 1) - cell height.val i j| ≤ 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i < numRows isWater → j + 1 < numCols isWater →
      |cell height.val i (j + 1) - cell height.val i j| ≤ 1) := by
  sorry

/-- Let W = {(a,b) | 0 <= a < m, 0 <= b < n, isWater[a][b] = 1}. For each cell (i,j), define d(i,j) = min over (a,b) in W of (|i-a| + |j-b|). Whenever the function returns a result height, for every i,j with 0 <= i < m and 0 <= j < n, height[i][j] <= d(i,j).
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_7 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i < numRows isWater → j < numCols isWater →
      cell height.val i j ≤ (distToWater isWater i j : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i < numRows isWater → j < numCols isWater →
      cell height.val i j ≤ (distToWater isWater i j : Int)) := by
  sorry

/-- Whenever the function returns a result height, for every integer matrix H with m rows, each row of length n, if H has non-negative entries, H[a][b] = 0 at every water cell isWater[a][b] = 1, every vertically adjacent pair of entries of H differs by at most 1, and every horizontally adjacent pair of entries of H differs by at most 1, then max over all entries of H is at most max over all entries of height.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_8 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height)
    (H : List (List Int))
    (hHrows : H.length = numRows isWater)
    (hHcols : ∀ row ∈ H, row.length = numCols isWater)
    (hHnonneg : ∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ icell H i j)
    (hHwater : ∀ a b, a < numRows isWater → b < numCols isWater →
      IsWater isWater a b → icell H a b = 0)
    (hHvert : ∀ a b, a + 1 < numRows isWater → b < numCols isWater →
      |icell H (a + 1) b - icell H a b| ≤ 1)
    (hHhoriz : ∀ a b, a < numRows isWater → b + 1 < numCols isWater →
      |icell H a (b + 1) - icell H a b| ≤ 1) :
    maxEntryI H ≤ maxEntry height.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height)
    (H : List (List Int))
    (hHrows : H.length = numRows isWater)
    (hHcols : ∀ row ∈ H, row.length = numCols isWater)
    (hHnonneg : ∀ i j, i < numRows isWater → j < numCols isWater → 0 ≤ icell H i j)
    (hHwater : ∀ a b, a < numRows isWater → b < numCols isWater →
      IsWater isWater a b → icell H a b = 0)
    (hHvert : ∀ a b, a + 1 < numRows isWater → b < numCols isWater →
      |icell H (a + 1) b - icell H a b| ≤ 1)
    (hHhoriz : ∀ a b, a < numRows isWater → b + 1 < numCols isWater →
      |icell H a (b + 1) - icell H a b| ≤ 1), maxEntryI H ≤ maxEntry height.val) := by
  sorry

/-- Let W = {(a,b) | 0 <= a < m, 0 <= b < n, isWater[a][b] = 1}. For each cell (i,j), define d(i,j) = min over (a,b) in W of (|i-a| + |j-b|), and D = max over 0 <= i < m and 0 <= j < n of d(i,j). Whenever the function returns a result height, there exist i,j with 0 <= i < m and 0 <= j < n such that height[i][j] = D.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_9 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∃ i j, i < numRows isWater ∧ j < numCols isWater ∧
      cell height.val i j = (maxDistToWater isWater : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∃ i j, i < numRows isWater ∧ j < numCols isWater ∧
      cell height.val i j = (maxDistToWater isWater : Int)) := by
  sorry

/-- Whenever the function returns a result height, the maximum entry of height is at least 1.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; there exists at least one water cell; and there exists at least one land cell, i.e. some i,j has isWater[i][j] = 0. -/
theorem spec_10 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (hland : HasLand isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    1 ≤ maxEntry height.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (hland : HasLand isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), 1 ≤ maxEntry height.val) := by
  sorry

/-- The function returns a result height; it does not fail, overflow, or panic on any input satisfying the preconditions.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_11 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater) :
    ∃ height : alloc.vec.Vec (alloc.vec.Vec I64), highest_peak isWater = ok height := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater), ∃ height : alloc.vec.Vec (alloc.vec.Vec I64), highest_peak isWater = ok height) := by
  sorry

/-- Let W = {(a,b) | 0 <= a < m, 0 <= b < n, isWater[a][b] = 1}. For each cell (i,j), define d(i,j) = min over (a,b) in W of (|i-a| + |j-b|), and D = max over 0 <= i < m and 0 <= j < n of d(i,j). Whenever the function returns a result height, for every i,j with 0 <= i < m and 0 <= j < n, if height[i][j] = D then d(i,j) = D.
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_12 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ i j, i < numRows isWater → j < numCols isWater →
      cell height.val i j = (maxDistToWater isWater : Int) →
      distToWater isWater i j = maxDistToWater isWater := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ i j, i < numRows isWater → j < numCols isWater →
      cell height.val i j = (maxDistToWater isWater : Int) →
      distToWater isWater i j = maxDistToWater isWater) := by
  sorry

/-- Whenever the function returns a result height, let Mheight = max over all entries of height. For every cell (a,b) with height[a][b] = Mheight and every cell (i,j) with 0 <= i < m and 0 <= j < n, height[i][j] >= Mheight - (|i-a| + |j-b|).
  Preconditions: Let m = len(isWater) and n = len(isWater[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000; every row of isWater has length n; for every i,j with 0 <= i < m and 0 <= j < n, isWater[i][j] is either 0 or 1; and there exists at least one water cell. -/
theorem spec_13 (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height) :
    ∀ a b, a < numRows isWater → b < numCols isWater →
      cell height.val a b = maxEntry height.val →
      ∀ i j, i < numRows isWater → j < numCols isWater →
        maxEntry height.val - (l1 i j a b : Int) ≤ cell height.val i j := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (isWater : Slice (alloc.vec.Vec I64)) (hpre : Pre isWater)
    (height : alloc.vec.Vec (alloc.vec.Vec I64))
    (hres : highest_peak isWater = ok height), ∀ a b, a < numRows isWater → b < numCols isWater →
      cell height.val a b = maxEntry height.val →
      ∀ i j, i < numRows isWater → j < numCols isWater →
        maxEntry height.val - (l1 i j a b : Int) ≤ cell height.val i j) := by
  sorry

end AegisSpec.HighestPeak
