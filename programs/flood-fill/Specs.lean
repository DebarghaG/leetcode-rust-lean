import Aegis.FloodFill.Code.Funs

/-!
# Specifications of `Aegis.FloodFill.flood_fill`

LeetCode problem `flood-fill`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FloodFill

  namespace AegisSpec.FloodFill

  abbrev Image := Slice (alloc.vec.Vec Std.I64)

  abbrev ImageV := alloc.vec.Vec (alloc.vec.Vec Std.I64)

  def rowList (row : alloc.vec.Vec Std.I64) : List Int := row.val.map (fun x => x.val)

  def inGrid (image : Image) : List (List Int) := image.val.map rowList

  def outGrid (r : ImageV) : List (List Int) := r.val.map rowList

  def nrows (g : List (List Int)) : Nat := g.length

  def ncols (g : List (List Int)) : Nat := (g.getD 0 []).length

  def rowLen (g : List (List Int)) (i : Nat) : Nat := (g.getD i []).length

  def cell (g : List (List Int)) (i j : Nat) : Int := (g.getD i []).getD j 0

  def InRange (x : Int) (N : Nat) : Prop := 0 ≤ x ∧ x < (N : Int)

  def sideAdj (p q : Nat × Nat) : Prop :=
    ((p.1 : Int) - (q.1 : Int)).natAbs + ((p.2 : Int) - (q.2 : Int)).natAbs = 1

  def inBounds (g : List (List Int)) (p : Nat × Nat) : Prop :=
    p.1 < nrows g ∧ p.2 < ncols g

  def Consecutive (path : List (Nat × Nat)) : Prop :=
    ∀ k a b, path[k]? = some a → path[k + 1]? = some b → sideAdj a b

  def PathTo (g : List (List Int)) (c0 : Int) (p q : Nat × Nat) (path : List (Nat × Nat)) : Prop :=
    path.head? = some p ∧ path.getLast? = some q ∧
      (∀ x ∈ path, inBounds g x ∧ cell g x.1 x.2 = c0) ∧ Consecutive path

  def Reach (g : List (List Int)) (c0 : Int) (p q : Nat × Nat) : Prop :=
    ∃ path, PathTo g c0 p q path

  def startPos (sr sc : Std.I64) : Nat × Nat := (sr.val.toNat, sc.val.toNat)

  def c0At (g : List (List Int)) (sr sc : Std.I64) : Int :=
    cell g (startPos sr sc).1 (startPos sr sc).2

  def R (image : Image) (sr sc : Std.I64) (p : Nat × Nat) : Prop :=
    Reach (inGrid image) (c0At (inGrid image) sr sc) (startPos sr sc) p

  def asSlice (r : ImageV) : Image :=
    { leng := r.val.length
      list := Aeneas.Data.ListN.ListN.fromList r.val
      bound := by
        have h := Aeneas.Data.ListN.ListN_length r.slice.list
        have hb := r.slice.bound
        simp only [Aeneas.Std.alloc.vec.Vec.val, Aeneas.Std.Slice.val] at h ⊢
        omega }

  /-- Let c0 = image[sr][sc], and let R be the set of cells (i,j) with 0 <= i < m and 0 <= j < n for which there exists a finite sequence (i_0,j_0),...,(i_k,j_k) with k >= 0 such that (i_0,j_0) = (sr,sc), (i_k,j_k) = (i,j), every (i_t,j_t) lies in the grid, image[i_t][j_t] = c0 for every t, and for every t < k the cells (i_t,j_t) and (i_{t+1},j_{t+1}) share a side, i.e. |i_{t+1}-i_t| + |j_{t+1}-j_t| = 1. The function returns a result r such that len(r) = m, every row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n: if (i,j) is in R then r[i][j] = color, and if (i,j) is not in R then r[i][j] = image[i][j].
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_1 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∃ r : ImageV,
        flood_fill image sr sc color = ok r ∧
        (outGrid r).length = m ∧
        (∀ row ∈ outGrid r, row.length = n) ∧
        (∀ i j, i < m → j < n →
          (R image sr sc (i, j) → cell (outGrid r) i j = color.val) ∧
          (¬ R image sr sc (i, j) → cell (outGrid r) i j = cell (inGrid image) i j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∃ r : ImageV,
          flood_fill image sr sc color = ok r ∧
          (outGrid r).length = m ∧
          (∀ row ∈ outGrid r, row.length = n) ∧
          (∀ i j, i < m → j < n →
            (R image sr sc (i, j) → cell (outGrid r) i j = color.val) ∧
            (¬ R image sr sc (i, j) → cell (outGrid r) i j = cell (inGrid image) i j))) := by
    sorry

  /-- Whenever flood_fill returns a result r, len(r) = len(image), and for every i with 0 <= i < len(image), len(r[i]) = len(image[i]).
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_2 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        (outGrid r).length = (inGrid image).length ∧
        (∀ i, i < (inGrid image).length →
          rowLen (outGrid r) i = rowLen (inGrid image) i) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          (outGrid r).length = (inGrid image).length ∧
          (∀ i, i < (inGrid image).length →
            rowLen (outGrid r) i = rowLen (inGrid image) i)) := by
    sorry

  /-- Let c0 = image[sr][sc], and let R be the set of cells reachable from (sr,sc) by a path of side-adjacent cells all of whose image values equal c0, including (sr,sc) itself. Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, if (i,j) is not in R then r[i][j] = image[i][j].
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_3 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          ¬ R image sr sc (i, j) → cell (outGrid r) i j = cell (inGrid image) i j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            ¬ R image sr sc (i, j) → cell (outGrid r) i j = cell (inGrid image) i j) := by
    sorry

  /-- Let c0 = image[sr][sc], and let R be the set of cells reachable from (sr,sc) by a path of side-adjacent cells all of whose image values equal c0, including (sr,sc) itself. Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, if (i,j) is in R then r[i][j] = color.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_4 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          R image sr sc (i, j) → cell (outGrid r) i j = color.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            R image sr sc (i, j) → cell (outGrid r) i j = color.val) := by
    sorry

  /-- Whenever flood_fill returns a result r and color = image[sr][sc], r is elementwise equal to image: len(r) = len(image), len(r[i]) = len(image[i]) for every valid i, and r[i][j] = image[i][j] for every i,j with 0 <= i < m and 0 <= j < n.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_5 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        color.val = c0At (inGrid image) sr sc →
        (outGrid r).length = (inGrid image).length ∧
        (∀ i, i < m → rowLen (outGrid r) i = rowLen (inGrid image) i) ∧
        (∀ i j, i < m → j < n → cell (outGrid r) i j = cell (inGrid image) i j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          color.val = c0At (inGrid image) sr sc →
          (outGrid r).length = (inGrid image).length ∧
          (∀ i, i < m → rowLen (outGrid r) i = rowLen (inGrid image) i) ∧
          (∀ i j, i < m → j < n → cell (outGrid r) i j = cell (inGrid image) i j)) := by
    sorry

  /-- Let c0 = image[sr][sc]. Whenever flood_fill returns a result r and no side-neighbor of (sr,sc) that lies in the grid has image value c0, i.e. for all (i,j) in the grid with |i-sr| + |j-sc| = 1 we have image[i][j] != c0, then r[sr][sc] = color and for every (i,j) in the grid with (i,j) != (sr,sc) we have r[i][j] = image[i][j].
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_6 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        (∀ i j, i < m → j < n → sideAdj (i, j) (startPos sr sc) →
          cell (inGrid image) i j ≠ c0At (inGrid image) sr sc) →
        cell (outGrid r) (startPos sr sc).1 (startPos sr sc).2 = color.val ∧
        (∀ i j, i < m → j < n → (i, j) ≠ startPos sr sc →
          cell (outGrid r) i j = cell (inGrid image) i j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          (∀ i j, i < m → j < n → sideAdj (i, j) (startPos sr sc) →
            cell (inGrid image) i j ≠ c0At (inGrid image) sr sc) →
          cell (outGrid r) (startPos sr sc).1 (startPos sr sc).2 = color.val ∧
          (∀ i j, i < m → j < n → (i, j) ≠ startPos sr sc →
            cell (outGrid r) i j = cell (inGrid image) i j)) := by
    sorry

  /-- Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, either r[i][j] = image[i][j] or r[i][j] = color.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_7 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          cell (outGrid r) i j = cell (inGrid image) i j ∨ cell (outGrid r) i j = color.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            cell (outGrid r) i j = cell (inGrid image) i j ∨ cell (outGrid r) i j = color.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail or panic.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_8 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∃ r : ImageV, flood_fill image sr sc color = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∃ r : ImageV, flood_fill image sr sc color = ok r) := by
    sorry

  /-- Whenever flood_fill(image, sr, sc, color) returns a result r, the call flood_fill(r, sr, sc, color) also returns r, with r viewed as the image.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_9 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        flood_fill (asSlice r) sr sc color = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          flood_fill (asSlice r) sr sc color = ok r) := by
    sorry

  /-- Let c0 = image[sr][sc]. Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, if r[i][j] != image[i][j], then image[i][j] = c0 and r[i][j] = color.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_10 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          cell (outGrid r) i j ≠ cell (inGrid image) i j →
          cell (inGrid image) i j = c0At (inGrid image) sr sc ∧
            cell (outGrid r) i j = color.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            cell (outGrid r) i j ≠ cell (inGrid image) i j →
            cell (inGrid image) i j = c0At (inGrid image) sr sc ∧
              cell (outGrid r) i j = color.val) := by
    sorry

  /-- Let c0 = image[sr][sc], and let R be the set of cells reachable from (sr,sc) by a path of side-adjacent cells all of whose image values equal c0, including (sr,sc) itself. Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] != image[i][j] if and only if (i,j) is in R and color != c0.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_11 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          (cell (outGrid r) i j ≠ cell (inGrid image) i j ↔
            R image sr sc (i, j) ∧ color.val ≠ c0At (inGrid image) sr sc) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            (cell (outGrid r) i j ≠ cell (inGrid image) i j ↔
              R image sr sc (i, j) ∧ color.val ≠ c0At (inGrid image) sr sc)) := by
    sorry

  /-- Let c0 = image[sr][sc]. Whenever flood_fill returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, if r[i][j] != image[i][j], then there exists a finite sequence of grid cells (i_0,j_0),...,(i_k,j_k) with k >= 0 such that (i_0,j_0) = (sr,sc), (i_k,j_k) = (i,j), every cell in the sequence has image value c0, and consecutive cells share a side, i.e. |i_{t+1}-i_t| + |j_{t+1}-j_t| = 1 for every t < k.
    Preconditions: Let m = len(image) and n = len(image[0]). The input satisfies: 1 <= m <= 50, 1 <= n <= 50, every row of image has length n, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= image[i][j] < 65536, 0 <= color < 65536, 0 <= sr < m, and 0 <= sc < n. -/
  theorem spec_12 (image : Image) (sr sc color : Std.I64) (m n : Nat)
      (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hrows : ∀ row ∈ inGrid image, row.length = n)
      (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
      (hcolor : InRange color.val 65536)
      (hsr : InRange sr.val m) (hsc : InRange sc.val n) :
      ∀ r : ImageV,
        flood_fill image sr sc color = ok r →
        ∀ i j, i < m → j < n →
          cell (outGrid r) i j ≠ cell (inGrid image) i j →
          ∃ path : List (Nat × Nat),
            PathTo (inGrid image) (c0At (inGrid image) sr sc) (startPos sr sc) (i, j) path := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (image : Image) (sr sc color : Std.I64) (m n : Nat)
        (hm : m = nrows (inGrid image)) (hn : n = ncols (inGrid image))
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hrows : ∀ row ∈ inGrid image, row.length = n)
        (hvals : ∀ i j, i < m → j < n → InRange (cell (inGrid image) i j) 65536)
        (hcolor : InRange color.val 65536)
        (hsr : InRange sr.val m) (hsc : InRange sc.val n), ∀ r : ImageV,
          flood_fill image sr sc color = ok r →
          ∀ i j, i < m → j < n →
            cell (outGrid r) i j ≠ cell (inGrid image) i j →
            ∃ path : List (Nat × Nat),
              PathTo (inGrid image) (c0At (inGrid image) sr sc) (startPos sr sc) (i, j) path) := by
    sorry

  end AegisSpec.FloodFill
