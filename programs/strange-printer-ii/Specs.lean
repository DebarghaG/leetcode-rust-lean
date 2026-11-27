import Aegis.IsPrintable.Code.Funs

/-!
# Specifications of `Aegis.IsPrintable.is_printable`

LeetCode problem `strange-printer-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsPrintable

  namespace AegisSpec.IsPrintable

  abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

  def rowVals (g : Grid) (i : ℕ) : List ℤ :=
    (g.val[i]?).map (fun r => r.val.map (fun x => x.val)) |>.getD []

  def numCols (g : Grid) : ℕ :=
    (g.val.head?.map (fun r => r.val.length)).getD 0

  def cellVal (g : Grid) (i j : ℕ) : ℤ :=
    (rowVals g i)[j]?.getD 0

  def Occurs (g : Grid) (c : ℤ) : Prop :=
    ∃ row ∈ g.val, c ∈ row.val.map (fun x => x.val)

  def occRows (g : Grid) (c : ℤ) : List ℕ :=
    (List.range g.val.length).filter (fun i => c ∈ rowVals g i)

  def occCols (g : Grid) (c : ℤ) : List ℕ :=
    (List.range (numCols g)).filter
      (fun j => ∃ i, i < g.val.length ∧ j < (rowVals g i).length ∧ cellVal g i j = c)

  def minRow (g : Grid) (c : ℤ) : ℕ := (occRows g c).headD 0

  def maxRow (g : Grid) (c : ℤ) : ℕ := (occRows g c).getLastD 0

  def minCol (g : Grid) (c : ℤ) : ℕ := (occCols g c).headD 0

  def maxCol (g : Grid) (c : ℤ) : ℕ := (occCols g c).getLastD 0

  def InBBox (g : Grid) (c : ℤ) (i j : ℕ) : Prop :=
    minRow g c ≤ i ∧ i ≤ maxRow g c ∧ minCol g c ≤ j ∧ j ≤ maxCol g c

  def BoxHasColor (g : Grid) (c c' : ℤ) : Prop :=
    ∃ i j, InBBox g c i j ∧ cellVal g i j = c'

  def IsColorList (g : Grid) (cs : List ℤ) : Prop :=
    cs.Nodup ∧ ∀ c, c ∈ cs ↔ Occurs g c

  def OrderedColorList (g : Grid) (cs : List ℤ) : Prop :=
    ∀ (p : ℕ) (c : ℤ), cs[p]? = some c →
      ∀ i j, InBBox g c i j → cellVal g i j ≠ c →
        ∃ q, p < q ∧ cs[q]? = some (cellVal g i j)

  def HasBoxCycle (g : Grid) : Prop :=
    ∃ (k : ℕ) (cs : List ℤ),
      2 ≤ k ∧ cs.length = k ∧ cs.Nodup ∧
        (∀ c, c ∈ cs → Occurs g c) ∧
        ∀ (p : ℕ) (c c' : ℤ), p < k → cs[p]? = some c → cs[(p + 1) % k]? = some c' →
          BoxHasColor g c c'

  def Relabel (g g' : Grid) (f : ℤ → ℤ) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g → cellVal g' i j = f (cellVal g i j)

  def TransposeOf (g g' : Grid) : Prop :=
    g'.val.length = numCols g ∧ numCols g' = g.val.length ∧
      ∀ i j, i < g.val.length → j < numCols g → cellVal g' j i = cellVal g i j

  def Rotate180Of (g g' : Grid) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g →
        cellVal g' i j = cellVal g (g.val.length - 1 - i) (numCols g - 1 - j)

  def MirrorOf (g g' : Grid) : Prop :=
    g'.val.length = g.val.length ∧ numCols g' = numCols g ∧
      ∀ i j, i < g.val.length → j < numCols g →
        cellVal g' i j = cellVal g i (numCols g - 1 - j)

  /-- The function returns a result r (not a failure), and r = true if and only if there exists a finite list c_1, ..., c_k containing exactly the distinct color values that occur in targetGrid, each once, such that: for every p with 1 <= p <= k, and every cell (i,j) in the bounding box of c_p (that is, minRow(c_p) <= i <= maxRow(c_p) and minCol(c_p) <= j <= maxCol(c_p), where minRow(c), maxRow(c), minCol(c), maxCol(c) are the minimum and maximum row and column indices of cells of color c in targetGrid), if targetGrid[i][j] != c_p then the color targetGrid[i][j] occurs later in the list, i.e. there is q with p < q <= k and c_q = targetGrid[i][j].
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      ∃ r, is_printable targetGrid = ok r ∧
        (r = true ↔ ∃ cs : List ℤ, IsColorList targetGrid cs ∧ OrderedColorList targetGrid cs) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60), ∃ r, is_printable targetGrid = ok r ∧
          (r = true ↔ ∃ cs : List ℤ, IsColorList targetGrid cs ∧ OrderedColorList targetGrid cs)) := by
    sorry

  /-- There is a Boolean r such that is_printable(targetGrid) returns r; equivalently, the call does not fail (no panic, overflow, or out-of-bounds).
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      ∃ r : Bool, is_printable targetGrid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60), ∃ r : Bool, is_printable targetGrid = ok r) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. Also, there exists a color c such that targetGrid[i][j] = c for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hconst : ∃ c : ℤ, ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        cellVal targetGrid i j = c) :
      ∃ r, is_printable targetGrid = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (hconst : ∃ c : ℤ, ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          cellVal targetGrid i j = c), ∃ r, is_printable targetGrid = ok r ∧ r = true) := by
    sorry

  /-- Whenever the function returns r = true, there exists a color c occurring in targetGrid such that every cell in the bounding box of c has color c: for every i,j with minRow(c) <= i <= maxRow(c) and minCol(c) <= j <= maxCol(c), targetGrid[i][j] = c, where minRow(c), maxRow(c), minCol(c), maxCol(c) are the minimum and maximum row and column indices of cells of color c in targetGrid.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok true →
        ∃ c : ℤ, Occurs targetGrid c ∧
          ∀ i j, InBBox targetGrid c i j → cellVal targetGrid i j = c := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60), is_printable targetGrid = ok true →
          ∃ c : ℤ, Occurs targetGrid c ∧
            ∀ i j, InBBox targetGrid c i j → cellVal targetGrid i j = c) := by
    sorry

  /-- Whenever the function returns r = true, there exists a color c occurring in targetGrid such that no other occurring color d != c has a cell of color c inside the bounding box of d. Explicitly, for every occurring color d != c and every position (i,j) with targetGrid[i][j] = c, it is not the case that minRow(d) <= i <= maxRow(d) and minCol(d) <= j <= maxCol(d), where minRow(x), maxRow(x), minCol(x), maxCol(x) are the minimum and maximum row and column indices of cells of color x.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok true →
        ∃ c : ℤ, Occurs targetGrid c ∧
          ∀ d : ℤ, Occurs targetGrid d → d ≠ c →
            ∀ i j, cellVal targetGrid i j = c → ¬ InBBox targetGrid d i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60), is_printable targetGrid = ok true →
          ∃ c : ℤ, Occurs targetGrid c ∧
            ∀ d : ℤ, Occurs targetGrid d → d ≠ c →
              ∀ i j, cellVal targetGrid i j = c → ¬ InBBox targetGrid d i j) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. Also, there exist distinct colors a and b occurring in targetGrid such that the bounding box of a contains at least one cell whose target color is b, and the bounding box of b contains at least one cell whose target color is a. -/
  theorem spec_6 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (a b : ℤ) (ha : Occurs targetGrid a) (hb : Occurs targetGrid b) (hab : a ≠ b)
      (hbox_ab : BoxHasColor targetGrid a b) (hbox_ba : BoxHasColor targetGrid b a) :
      ∃ r, is_printable targetGrid = ok r ∧ r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (a b : ℤ) (ha : Occurs targetGrid a) (hb : Occurs targetGrid b) (hab : a ≠ b)
        (hbox_ab : BoxHasColor targetGrid a b) (hbox_ba : BoxHasColor targetGrid b a), ∃ r, is_printable targetGrid = ok r ∧ r = false) := by
    sorry

  /-- Whenever the function returns r = false, there exist an integer k >= 2 and distinct colors c_1, ..., c_k occurring in targetGrid such that, setting c_{k+1} = c_1, for every p with 1 <= p <= k the bounding box of c_p contains at least one cell whose targetGrid color is c_{p+1}. Here the bounding box of a color x is the smallest rectangle of positions containing every occurrence of x.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60) :
      is_printable targetGrid = ok false → HasBoxCycle targetGrid := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60), is_printable targetGrid = ok false → HasBoxCycle targetGrid) := by
    sorry

  /-- For every injective function f from the set of color values occurring in targetGrid into {1,2,...,60}, let targetGrid' be the same-shaped grid with targetGrid'[i][j] = f(targetGrid[i][j]) for all i,j. Whenever is_printable(targetGrid) returns r and is_printable(targetGrid') returns r', we have r = r'.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (targetGrid targetGrid' : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (f : ℤ → ℤ)
      (hf_range : ∀ c : ℤ, Occurs targetGrid c → 1 ≤ f c ∧ f c ≤ 60)
      (hf_inj : ∀ c d : ℤ, Occurs targetGrid c → Occurs targetGrid d → f c = f d → c = d)
      (hrelabel : Relabel targetGrid targetGrid' f) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable targetGrid' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (targetGrid targetGrid' : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (f : ℤ → ℤ)
        (hf_range : ∀ c : ℤ, Occurs targetGrid c → 1 ≤ f c ∧ f c ≤ 60)
        (hf_inj : ∀ c d : ℤ, Occurs targetGrid c → Occurs targetGrid d → f c = f d → c = d)
        (hrelabel : Relabel targetGrid targetGrid' f), ∀ r r' : Bool, is_printable targetGrid = ok r →
          is_printable targetGrid' = ok r' → r = r') := by
    sorry

  /-- Let T be the n by m grid defined by T[j][i] = targetGrid[i][j] for 0 <= i < m and 0 <= j < n. Whenever is_printable(targetGrid) returns r and is_printable(T) returns r', we have r = r'.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (targetGrid T : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hT : TransposeOf targetGrid T) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable T = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (targetGrid T : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (hT : TransposeOf targetGrid T), ∀ r r' : Bool, is_printable targetGrid = ok r →
          is_printable T = ok r' → r = r') := by
    sorry

  /-- Let R be the m by n grid defined by R[i][j] = targetGrid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Whenever is_printable(targetGrid) returns r and is_printable(R) returns r', we have r = r'.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (targetGrid R : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hR : Rotate180Of targetGrid R) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable R = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (targetGrid R : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (hR : Rotate180Of targetGrid R), ∀ r r' : Bool, is_printable targetGrid = ok r →
          is_printable R = ok r' → r = r') := by
    sorry

  /-- Let H be the m by n grid defined by H[i][j] = targetGrid[i][n-1-j] for 0 <= i < m and 0 <= j < n. Whenever is_printable(targetGrid) returns r and is_printable(H) returns r', we have r = r'.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (targetGrid H : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hH : MirrorOf targetGrid H) :
      ∀ r r' : Bool, is_printable targetGrid = ok r →
        is_printable H = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (targetGrid H : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (hH : MirrorOf targetGrid H), ∀ r r' : Bool, is_printable targetGrid = ok r →
          is_printable H = ok r' → r = r') := by
    sorry

  /-- The function returns a result r and r = false. This is the converse of spec_7 and generalizes S7: any directed cycle of bounding-box containments is an obstruction to printability.
    Preconditions: targetGrid is a valid grid: writing m = len(targetGrid) and n = len(targetGrid[0]), 1 <= m <= 60, 1 <= n <= 60, every row of targetGrid has length n, and 1 <= targetGrid[i][j] <= 60 for every 0 <= i < m and 0 <= j < n. Also, there exist an integer k >= 2 and distinct colors c_1, ..., c_k occurring in targetGrid such that, setting c_{k+1} = c_1, for every p with 1 <= p <= k the bounding box of c_p contains at least one cell whose targetGrid color is c_{p+1}. -/
  theorem spec_12 (targetGrid : Grid)
      (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
      (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
      (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
      (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
        1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
      (hcycle : HasBoxCycle targetGrid) :
      ∃ r, is_printable targetGrid = ok r ∧ r = false := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (targetGrid : Grid)
        (hm : 1 ≤ targetGrid.val.length ∧ targetGrid.val.length ≤ 60)
        (hn : 1 ≤ numCols targetGrid ∧ numCols targetGrid ≤ 60)
        (hrows : ∀ row ∈ targetGrid.val, row.val.length = numCols targetGrid)
        (hentries : ∀ i j, i < targetGrid.val.length → j < numCols targetGrid →
          1 ≤ cellVal targetGrid i j ∧ cellVal targetGrid i j ≤ 60)
        (hcycle : HasBoxCycle targetGrid), ∃ r, is_printable targetGrid = ok r ∧ r = false) := by
    sorry

  end AegisSpec.IsPrintable
