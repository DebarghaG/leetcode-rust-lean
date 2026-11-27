import Aegis.HighestRankedKItems.Code.Funs

/-!
# Specifications of `Aegis.HighestRankedKItems.highest_ranked_k_items`

LeetCode problem `k-highest-ranked-items-within-a-price-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HighestRankedKItems

open Aegis.HighestRankedKItems (RankedItems highest_ranked_k_items)

def gridRows (grid : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  grid.val.map (fun r => r.val.map (fun x => x.val))

def gridRow (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int :=
  (gridRows grid).getD i []

def cellValue (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  (gridRow grid i).getD j 0

def sliceVal (s : Slice I64) (t : Nat) : Int :=
  ((s.val[t]?).map (fun x => x.val)).getD 0

def outRow (r : RankedItems) (t : Nat) : List Int :=
  ((r.val[t]?).map (fun v => v.val.map (fun x => x.val))).getD []

def outRow0 (r : RankedItems) (t : Nat) : Int :=
  (outRow r t).getD 0 0

def outRow1 (r : RankedItems) (t : Nat) : Int :=
  (outRow r t).getD 1 0

def outPair (r : RankedItems) (t : Nat) : Int × Int :=
  (outRow0 r t, outRow1 r t)

def NonnegCell (r : RankedItems) (t : Nat) : Prop :=
  0 ≤ outRow0 r t ∧ 0 ≤ outRow1 r t

structure Cell where
  row : Nat
  col : Nat

def outCell (r : RankedItems) (t : Nat) : Cell :=
  { row := (outRow0 r t).toNat, col := (outRow1 r t).toNat }

def entryEq (r : RankedItems) (t : Nat) (c : Cell) : Prop :=
  outRow0 r t = (c.row : Int) ∧ outRow1 r t = (c.col : Int)

def ValidCell (m n : Nat) (c : Cell) : Prop :=
  c.row < m ∧ c.col < n

def Passable (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (c : Cell) : Prop :=
  ValidCell m n c ∧ 0 < cellValue grid c.row c.col

def Adjacent (a b : Cell) : Prop :=
  (a.row = b.row ∧ (a.col + 1 = b.col ∨ b.col + 1 = a.col)) ∨
    (a.col = b.col ∧ (a.row + 1 = b.row ∨ b.row + 1 = a.row))

inductive Path (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (s : Cell) :
    Cell → Nat → Prop where
  | nil (h : Passable m n grid s) : Path m n grid s s 0
  | step {c x : Cell} {l : Nat} (hp : Path m n grid s c l) (ha : Adjacent c x)
      (hx : Passable m n grid x) : Path m n grid s x (l + 1)

def Reachable (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (s x : Cell) : Prop :=
  ∃ l, Path m n grid s x l

def ShortestDist (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (s x : Cell)
    (l : Nat) : Prop :=
  Path m n grid s x l ∧ ∀ l', Path m n grid s x l' → l ≤ l'

def InS (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (low high : Int) (s c : Cell) :
    Prop :=
  ValidCell m n c ∧ low ≤ cellValue grid c.row c.col ∧
    cellValue grid c.row c.col ≤ high ∧ Reachable m n grid s c

noncomputable def cardS (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (low high : Int)
    (s : Cell) : Nat := by
  classical
  exact (((List.range m).product (List.range n)).filter
    (fun p => decide (InS m n grid low high s { row := p.1, col := p.2 }))).length

def rankBetter (m n : Nat) (grid : Slice (alloc.vec.Vec I64)) (s a b : Cell) : Prop :=
  ∃ da db : Nat,
    ShortestDist m n grid s a da ∧ ShortestDist m n grid s b db ∧
      (da < db ∨
        (da = db ∧ cellValue grid a.row a.col < cellValue grid b.row b.col) ∨
          (da = db ∧ cellValue grid a.row a.col = cellValue grid b.row b.col ∧
            (a.row < b.row ∨ (a.row = b.row ∧ a.col < b.col))))

/-- Define S to be the set of cells (i,j) with 0 <= i < m, 0 <= j < n, low <= grid[i][j] <= high, that are reachable from (sr,sc) by a path of adjacent cells all having grid > 0. For (i,j) in S let d(i,j) be the length (number of steps) of a shortest such path. For distinct a=(r1,c1) and b=(r2,c2) in S, write rank_better(a,b) iff the tuple (d(a), grid[r1][c1], r1, c1) is lexicographically smaller than the tuple (d(b), grid[r2][c2], r2, c2). The function returns a result r such that: (1) len(r) = min(k, |S|); (2) for every t with 0 <= t < len(r), r[t] is a vector of length 2 and cell(r[t]) = (r[t][0], r[t][1]) belongs to S; (3) the cells cell(r[0]), ..., cell(r[len(r)-1]) are pairwise distinct; (4) for every t with 0 <= t < len(r)-1, rank_better(cell(r[t]), cell(r[t+1])); (5) for every cell x in S that is not equal to any cell(r[t]) with 0 <= t < len(r), and for every t with 0 <= t < len(r), rank_better(cell(r[t]), x).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        r.val.length = min k.val.toNat (cardS m n grid low high ⟨sr, sc⟩) ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ t u, t < u → u < r.val.length → outPair r t ≠ outPair r u) ∧
        (∀ t, t + 1 < r.val.length →
          rankBetter m n grid ⟨sr, sc⟩ (outCell r t) (outCell r (t + 1))) ∧
        (∀ x, InS m n grid low high ⟨sr, sc⟩ x →
          (∀ t, t < r.val.length → ¬ entryEq r t x) →
            ∀ t, t < r.val.length → rankBetter m n grid ⟨sr, sc⟩ (outCell r t) x) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        r.val.length = min k.val.toNat (cardS m n grid low high ⟨sr, sc⟩) ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ t u, t < u → u < r.val.length → outPair r t ≠ outPair r u) ∧
        (∀ t, t + 1 < r.val.length →
          rankBetter m n grid ⟨sr, sc⟩ (outCell r t) (outCell r (t + 1))) ∧
        (∀ x, InS m n grid low high ⟨sr, sc⟩ x →
          (∀ t, t < r.val.length → ¬ entryEq r t x) →
            ∀ t, t < r.val.length → rankBetter m n grid ⟨sr, sc⟩ (outCell r t) x)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic) on any input satisfying the preconditions.
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems, highest_ranked_k_items grid pricing start k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems, highest_ranked_k_items grid pricing start k = ok r) := by
  sorry

/-- The function returns a result r and for every t with 0 <= t < len(r), len(r[t]) = 2.
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length → (outRow r t).length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length → (outRow r t).length = 2) := by
  sorry

/-- The function returns a result r and for every t with 0 <= t < len(r), 0 <= r[t][0] < m and 0 <= r[t][1] < n.
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          0 ≤ outRow0 r t ∧ outRow0 r t < (m : Int) ∧
            0 ≤ outRow1 r t ∧ outRow1 r t < (n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          0 ≤ outRow0 r t ∧ outRow0 r t < (m : Int) ∧
            0 ≤ outRow1 r t ∧ outRow1 r t < (n : Int)) := by
  sorry

/-- Let low = pricing[0] and high = pricing[1]. The function returns a result r and for every t with 0 <= t < len(r), the cell (r[t][0], r[t][1]) is valid (0 <= r[t][0] < m and 0 <= r[t][1] < n) and low <= grid[r[t][0]][r[t][1]] <= high.
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          0 ≤ outRow0 r t ∧ outRow0 r t < (m : Int) ∧
            0 ≤ outRow1 r t ∧ outRow1 r t < (n : Int) ∧
            low ≤ cellValue grid (outCell r t).row (outCell r t).col ∧
            cellValue grid (outCell r t).row (outCell r t).col ≤ high := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          0 ≤ outRow0 r t ∧ outRow0 r t < (m : Int) ∧
            0 ≤ outRow1 r t ∧ outRow1 r t < (n : Int) ∧
            low ≤ cellValue grid (outCell r t).row (outCell r t).col ∧
            cellValue grid (outCell r t).row (outCell r t).col ≤ high) := by
  sorry

/-- Define a cell (i,j) to be valid if 0 <= i < m and 0 <= j < n, and passable if it is valid and grid[i][j] > 0. Define a cell (i,j) to be reachable from (sr,sc) if there is a finite sequence of valid passable cells starting at (sr,sc), ending at (i,j), with consecutive cells adjacent (Manhattan distance 1). The function returns a result r and for every t with 0 <= t < len(r), the cell (r[t][0], r[t][1]) is valid and reachable from (sr,sc).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          NonnegCell r t ∧ ValidCell m n (outCell r t) ∧
            Reachable m n grid ⟨sr, sc⟩ (outCell r t) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ t, t < r.val.length →
          NonnegCell r t ∧ ValidCell m n (outCell r t) ∧
            Reachable m n grid ⟨sr, sc⟩ (outCell r t)) := by
  sorry

/-- Let cell(r[t]) = (r[t][0], r[t][1]). The function returns a result r and for every i and j with 0 <= i < j < len(r), cell(r[i]) != cell(r[j]).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ i j, i < j → j < r.val.length → outPair r i ≠ outPair r j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        ∀ i j, i < j → j < r.val.length → outPair r i ≠ outPair r j) := by
  sorry

/-- Define S to be the set of cells (i,j) with 0 <= i < m, 0 <= j < n, low <= grid[i][j] <= high, that are reachable from (sr,sc) by a path of adjacent cells all having grid > 0. The function returns a result r and len(r) = min(k, |S|).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        r.val.length = min k.val.toNat (cardS m n grid low high ⟨sr, sc⟩) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        r.val.length = min k.val.toNat (cardS m n grid low high ⟨sr, sc⟩)) := by
  sorry

/-- Define S to be the set of cells (i,j) with 0 <= i < m, 0 <= j < n, low <= grid[i][j] <= high, that are reachable from (sr,sc) by a path of adjacent cells all having grid > 0. For (i,j) in S let d(i,j) be the length of a shortest such path. For distinct a=(r1,c1) and b=(r2,c2) in S, write rank_better(a,b) iff (d(a), grid[r1][c1], r1, c1) is lexicographically smaller than (d(b), grid[r2][c2], r2, c2). The function returns a result r such that for every t with 0 <= t < len(r), r[t] is a vector of length 2 and cell(r[t]) = (r[t][0], r[t][1]) belongs to S, and for every t with 0 <= t < len(r)-1, cell(r[t]) != cell(r[t+1]) and rank_better(cell(r[t]), cell(r[t+1])).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ t, t + 1 < r.val.length →
          outPair r t ≠ outPair r (t + 1) ∧
            rankBetter m n grid ⟨sr, sc⟩ (outCell r t) (outCell r (t + 1))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ t, t + 1 < r.val.length →
          outPair r t ≠ outPair r (t + 1) ∧
            rankBetter m n grid ⟨sr, sc⟩ (outCell r t) (outCell r (t + 1)))) := by
  sorry

/-- Define S to be the set of cells (i,j) with 0 <= i < m, 0 <= j < n, low <= grid[i][j] <= high, that are reachable from (sr,sc) by a path of adjacent cells all having grid > 0. For (i,j) in S let d(i,j) be the length of a shortest such path. For distinct a=(r1,c1) and b=(r2,c2) in S, write rank_better(a,b) iff (d(a), grid[r1][c1], r1, c1) is lexicographically smaller than (d(b), grid[r2][c2], r2, c2). The function returns a result r such that for every t with 0 <= t < len(r), r[t] is a vector of length 2 and cell(r[t]) = (r[t][0], r[t][1]) belongs to S; and for every cell x in S that is not equal to cell(r[t]) for any t with 0 <= t < len(r), and for every t with 0 <= t < len(r), rank_better(cell(r[t]), x).
  Preconditions: m = len(grid) >= 1; there exists n >= 1 such that every row grid[i] (0 <= i < m) has length n and 1 <= m*n <= 100000; every grid[i][j] satisfies 0 <= grid[i][j] <= 100000; len(pricing) = 2, low = pricing[0], high = pricing[1], and 2 <= low <= high <= 100000; len(start) = 2, sr = start[0], sc = start[1], with 0 <= sr < m, 0 <= sc < n, and grid[sr][sc] > 0; 1 <= k <= m*n. -/
theorem spec_10
    (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ x, InS m n grid low high ⟨sr, sc⟩ x →
          (∀ t, t < r.val.length → ¬ entryEq r t x) →
            ∀ t, t < r.val.length → rankBetter m n grid ⟨sr, sc⟩ (outCell r t) x) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (pricing start : Slice I64) (k : I64)
    (m n : Nat) (low high : Int) (sr sc : Nat)
    (hgrid : grid.val.length = m)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hrows : ∀ (i : Nat), i < m → (gridRow grid i).length = n)
    (hsize : 1 ≤ m * n ∧ m * n ≤ 100000)
    (hvals : ∀ (i j : Nat), i < m → j < n →
      0 ≤ cellValue grid i j ∧ cellValue grid i j ≤ 100000)
    (hpricing : pricing.val.length = 2)
    (hlow : sliceVal pricing 0 = low)
    (hhigh : sliceVal pricing 1 = high)
    (hlow2 : 2 ≤ low)
    (hlh : low ≤ high)
    (hhighmax : high ≤ 100000)
    (hstart : start.val.length = 2)
    (hsr : sliceVal start 0 = (sr : Int))
    (hsc : sliceVal start 1 = (sc : Int))
    (hsr_m : sr < m)
    (hsc_n : sc < n)
    (hseed : 0 < cellValue grid sr sc)
    (hk : 1 ≤ k.val ∧ k.val ≤ ((m * n : Nat) : Int)), ∃ r : RankedItems,
      highest_ranked_k_items grid pricing start k = ok r ∧
        (∀ t, t < r.val.length →
          (outRow r t).length = 2 ∧ NonnegCell r t ∧
            InS m n grid low high ⟨sr, sc⟩ (outCell r t)) ∧
        (∀ x, InS m n grid low high ⟨sr, sc⟩ x →
          (∀ t, t < r.val.length → ¬ entryEq r t x) →
            ∀ t, t < r.val.length → rankBetter m n grid ⟨sr, sc⟩ (outCell r t) x)) := by
  sorry

end AegisSpec.HighestRankedKItems
