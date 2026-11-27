import Aegis.ConstructProductMatrix.Code.Funs

/-!
# Specifications of `Aegis.ConstructProductMatrix.construct_product_matrix`

LeetCode problem `construct-product-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result
open Aegis.ConstructProductMatrix

namespace AegisSpec.ConstructProductMatrix

def rowsOf (l : List (alloc.vec.Vec Std.I64)) : List (List Int) :=
  l.map (fun v => v.val.map (fun x => x.val))

def entry (g : List (List Int)) (i j : Nat) : Int :=
  (g.getD i []).getD j 0

def HasShape (g : List (List Int)) (n m : Nat) : Prop :=
  g.length = n ∧ ∀ i, i < n → (g.getD i []).length = m

def EntriesInRange (g : List (List Int)) (n m : Nat) : Prop :=
  ∀ i, i < n → ∀ j, j < m → 1 ≤ entry g i j ∧ entry g i j ≤ 10 ^ 9

def SizeBound (n m : Nat) : Prop :=
  2 ≤ n * m ∧ n * m ≤ 100000

def mod12345 (x : Int) : Int :=
  x % 12345

def prodAll (g : List (List Int)) (n m : Nat) : Int :=
  let cells : List (Nat × Nat) :=
    (List.range n).flatMap (fun a => (List.range m).map (fun b => (a, b)))
  (cells.map (fun p => entry g p.1 p.2)).foldl (fun x y => x * y) 1

def prodExcept (g : List (List Int)) (n m i j : Nat) : Int :=
  let cells : List (Nat × Nat) :=
    (List.range n).flatMap (fun a => (List.range m).map (fun b => (a, b)))
  ((cells.filter (fun p => p ≠ (i, j))).map (fun p => entry g p.1 p.2)).foldl
    (fun x y => x * y) 1

def transp (g : List (List Int)) (n m : Nat) : List (List Int) :=
  (List.range m).map (fun j => (List.range n).map (fun i => entry g i j))

/-- For every valid input grid, whenever construct_product_matrix(grid) returns a result r, the following holds. First, len(r) = n and for every i with 0 <= i < n, len(r[i]) = m. Second, for every i,j with 0 <= i < n and 0 <= j < m, r[i][j] = (the product of all grid[a][b] with 0 <= a < n, 0 <= b < m, and (a,b) != (i,j)) mod 12345, where x mod 12345 denotes the unique integer in [0,12344] congruent to x modulo 12345.
  Preconditions: Let n = len(grid) and m = len(grid[0]). The input grid is a rectangular matrix: n >= 1, m >= 1, every row of grid has length m, 2 <= n*m <= 100000, and for every i,j with 0 <= i < n and 0 <= j < m, 1 <= grid[i][j] <= 10^9. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r) :
    HasShape (rowsOf r.val) n m ∧
      ∀ i, i < n → ∀ j, j < m →
        entry (rowsOf r.val) i j = mod12345 (prodExcept (rowsOf grid.val) n m i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r), HasShape (rowsOf r.val) n m ∧
      ∀ i, i < n → ∀ j, j < m →
        entry (rowsOf r.val) i j = mod12345 (prodExcept (rowsOf grid.val) n m i j)) := by
  sorry

/-- For every valid input grid, construct_product_matrix(grid) returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(grid) and m = len(grid[0]). The input grid is a rectangular matrix: n >= 1, m >= 1, every row of grid has length m, 2 <= n*m <= 100000, and for every i,j with 0 <= i < n and 0 <= j < m, 1 <= grid[i][j] <= 10^9. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m) :
    ∃ r, construct_product_matrix grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m), ∃ r, construct_product_matrix grid = ok r) := by
  sorry

/-- For every valid input grid, whenever construct_product_matrix(grid) returns r, for every i,j with 0 <= i < n and 0 <= j < m, (r[i][j] * grid[i][j]) mod 12345 = T mod 12345, where T is the product of all grid[a][b] with 0 <= a < n and 0 <= b < m.
  Preconditions: Let n = len(grid) and m = len(grid[0]). The input grid is a rectangular matrix: n >= 1, m >= 1, every row of grid has length m, 2 <= n*m <= 100000, and for every i,j with 0 <= i < n and 0 <= j < m, 1 <= grid[i][j] <= 10^9. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r) :
    ∀ i, i < n → ∀ j, j < m →
      mod12345 (entry (rowsOf r.val) i j * entry (rowsOf grid.val) i j) =
        mod12345 (prodAll (rowsOf grid.val) n m) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r), ∀ i, i < n → ∀ j, j < m →
      mod12345 (entry (rowsOf r.val) i j * entry (rowsOf grid.val) i j) =
        mod12345 (prodAll (rowsOf grid.val) n m)) := by
  sorry

/-- Whenever construct_product_matrix(grid) returns r and construct_product_matrix(grid') returns r', for every i,j with 0 <= i < n and 0 <= j < m, r[i][j] = r'[i][j].
  Preconditions: Let grid and grid' be two valid inputs with the same dimensions: len(grid) = len(grid') = n and len(grid[i]) = len(grid'[i]) = m for every i. Suppose for every i,j with 0 <= i < n and 0 <= j < m, grid[i][j] is congruent to grid'[i][j] modulo 12345. -/
theorem spec_4
    (grid grid' : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hshape' : HasShape (rowsOf grid'.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hrange' : EntriesInRange (rowsOf grid'.val) n m)
    (hcongr : ∀ i, i < n → ∀ j, j < m →
      mod12345 (entry (rowsOf grid.val) i j) = mod12345 (entry (rowsOf grid'.val) i j))
    (hres : construct_product_matrix grid = ok r)
    (hres' : construct_product_matrix grid' = ok r') :
    ∀ i, i < n → ∀ j, j < m → entry (rowsOf r.val) i j = entry (rowsOf r'.val) i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hshape' : HasShape (rowsOf grid'.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hrange' : EntriesInRange (rowsOf grid'.val) n m)
    (hcongr : ∀ i, i < n → ∀ j, j < m →
      mod12345 (entry (rowsOf grid.val) i j) = mod12345 (entry (rowsOf grid'.val) i j))
    (hres : construct_product_matrix grid = ok r)
    (hres' : construct_product_matrix grid' = ok r'), ∀ i, i < n → ∀ j, j < m → entry (rowsOf r.val) i j = entry (rowsOf r'.val) i j) := by
  sorry

/-- Whenever construct_product_matrix(grid) returns r and construct_product_matrix(grid^T) returns r^T, for every i,j with 0 <= i < n and 0 <= j < m, r[i][j] = r^T[j][i].
  Preconditions: Let n = len(grid) and m = len(grid[0]). The input grid is a rectangular matrix: n >= 1, m >= 1, every row of grid has length m, 2 <= n*m <= 100000, and for every i,j with 0 <= i < n and 0 <= j < m, 1 <= grid[i][j] <= 10^9. Let grid^T be the m by n matrix defined by grid^T[j][i] = grid[i][j] for 0 <= i < n and 0 <= j < m. -/
theorem spec_5
    (grid gridT : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hshapeT : HasShape (rowsOf gridT.val) m n)
    (hT : rowsOf gridT.val = transp (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r)
    (hresT : construct_product_matrix gridT = ok rT) :
    ∀ i, i < n → ∀ j, j < m → entry (rowsOf r.val) i j = entry (rowsOf rT.val) j i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (n m : Nat)
    (r rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hshape : HasShape (rowsOf grid.val) n m)
    (hsize : SizeBound n m)
    (hrange : EntriesInRange (rowsOf grid.val) n m)
    (hshapeT : HasShape (rowsOf gridT.val) m n)
    (hT : rowsOf gridT.val = transp (rowsOf grid.val) n m)
    (hres : construct_product_matrix grid = ok r)
    (hresT : construct_product_matrix gridT = ok rT), ∀ i, i < n → ∀ j, j < m → entry (rowsOf r.val) i j = entry (rowsOf rT.val) j i) := by
  sorry

end AegisSpec.ConstructProductMatrix
