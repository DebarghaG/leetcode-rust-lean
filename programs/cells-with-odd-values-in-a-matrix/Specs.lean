import Aegis.OddCells.Code.Funs

/-!
# Specifications of `Aegis.OddCells.odd_cells`

LeetCode problem `cells-with-odd-values-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.OddCells

  open Aegis.OddCells

  abbrev Idx := Slice (alloc.vec.Vec Std.I64)

  def entry (indices : Idx) (k : ℕ) : Option (alloc.vec.Vec Std.I64) := indices.val[k]?

  def entryLen (indices : Idx) (k : ℕ) : Option ℕ := (entry indices k).map (fun v => v.val.length)

  def entryRow (indices : Idx) (k : ℕ) : Option ℤ :=
    (entry indices k).bind (fun v => (v.val[0]?).map (fun x => x.val))

  def entryCol (indices : Idx) (k : ℕ) : Option ℤ :=
    (entry indices k).bind (fun v => (v.val[1]?).map (fun x => x.val))

  def rowCount (indices : Idx) (i : ℤ) : ℕ :=
    (List.range indices.val.length).countP (fun k => decide (entryRow indices k = some i))

  def colCount (indices : Idx) (j : ℤ) : ℕ :=
    (List.range indices.val.length).countP (fun k => decide (entryCol indices k = some j))

  def rowOddCount (m : ℤ) (indices : Idx) : ℕ :=
    (List.range m.toNat).countP (fun i => decide (rowCount indices (i : ℤ) % 2 = 1))

  def colOddCount (n : ℤ) (indices : Idx) : ℕ :=
    (List.range n.toNat).countP (fun j => decide (colCount indices (j : ℤ) % 2 = 1))

  def oddCellCount (m n : ℤ) (indices : Idx) : ℕ :=
    ((List.range m.toNat).product (List.range n.toNat)).countP
      (fun p => decide ((rowCount indices (p.1 : ℤ) + colCount indices (p.2 : ℤ)) % 2 = 1))

  def IsTranspose (indices indicesT : Idx) : Prop :=
    indicesT.val.length = indices.val.length ∧
      ∀ k, k < indices.val.length →
        entryLen indicesT k = some 2 ∧ entryRow indicesT k = entryCol indices k ∧
          entryCol indicesT k = entryRow indices k

  def IsReordering (indices indices' : Idx) : Prop :=
    ∃ (p : Fin indices.val.length ≃ Fin indices.val.length)
      (hlen : indices'.val.length = indices.val.length),
      ∀ k : Fin indices'.val.length, indices'.val.get k = indices.val.get (p ⟨k.val, hlen ▸ k.isLt⟩)

  def IsAppendPair (indices indices' : Idx) (a b : ℤ) : Prop :=
    indices'.val.length = indices.val.length + 2 ∧
      (∀ k, k < indices.val.length →
        entryLen indices' k = entryLen indices k ∧ entryRow indices' k = entryRow indices k ∧
          entryCol indices' k = entryCol indices k) ∧
      entryLen indices' indices.val.length = some 2 ∧
      entryRow indices' indices.val.length = some a ∧
      entryCol indices' indices.val.length = some b ∧
      entryLen indices' (indices.val.length + 1) = some 2 ∧
      entryRow indices' (indices.val.length + 1) = some a ∧
      entryCol indices' (indices.val.length + 1) = some b

  /-- The function returns a result r (a 64-bit integer) and r = |{ (i,j) | 0 <= i < m and 0 <= j < n and R(i)+C(j) is odd }|, where R(i) = |{ k | 0 <= k < len(indices) and indices[k][0] = i }| for 0 <= i < m, and C(j) = |{ k | 0 <= k < len(indices) and indices[k][1] = j }| for 0 <= j < n.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_1
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧ r.val = (oddCellCount m.val n.val indices : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧ r.val = (oddCellCount m.val n.val indices : ℤ)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= m*n.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_2
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧ 0 ≤ r.val ∧ r.val ≤ m.val * n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧ 0 ≤ r.val ∧ r.val ≤ m.val * n.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow for every input satisfying the preconditions.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_3
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r) := by
    sorry

  /-- Let R(i) = |{ k | 0 <= k < len(indices) and indices[k][0] = i }| for 0 <= i < m, and C(j) = |{ k | 0 <= k < len(indices) and indices[k][1] = j }| for 0 <= j < n. Let rowOdd = |{ i | 0 <= i < m and R(i) is odd }| and colOdd = |{ j | 0 <= j < n and C(j) is odd }|. The function returns a result r and r = rowOdd*(n - colOdd) + (m - rowOdd)*colOdd.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_4
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        r.val = (rowOddCount m.val indices : ℤ) *
            (n.val - (colOddCount n.val indices : ℤ)) +
          (m.val - (rowOddCount m.val indices : ℤ)) * (colOddCount n.val indices : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          r.val = (rowOddCount m.val indices : ℤ) *
              (n.val - (colOddCount n.val indices : ℤ)) +
            (m.val - (rowOddCount m.val indices : ℤ)) * (colOddCount n.val indices : ℤ)) := by
    sorry

  /-- The function returns a result r and r mod 2 = ((m+n) * len(indices)) mod 2.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_5
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        r.val % 2 = ((m.val + n.val) * (indices.val.length : ℤ)) % 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          r.val % 2 = ((m.val + n.val) * (indices.val.length : ℤ)) % 2) := by
    sorry

  /-- The function returns a result r; if len(indices) is odd then r = m + n - 2, and otherwise r = 0.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and there exist integers a,b with 0 <= a < m and 0 <= b < n such that for every k with 0 <= k < len(indices), len(indices[k]) = 2, indices[k][0] = a, and indices[k][1] = b. -/
  theorem spec_6
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (a b : ℤ) (ha : 0 ≤ a) (ham : a < m.val) (hb : 0 ≤ b) (hbn : b < n.val)
      (hconst : ∀ k, k < indices.val.length →
        entryLen indices k = some 2 ∧ entryRow indices k = some a ∧ entryCol indices k = some b) :
      ∃ r, odd_cells m n indices = ok r ∧
        r.val = (if indices.val.length % 2 = 1 then m.val + n.val - 2 else 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (a b : ℤ) (ha : 0 ≤ a) (ham : a < m.val) (hb : 0 ≤ b) (hbn : b < n.val)
        (hconst : ∀ k, k < indices.val.length →
          entryLen indices k = some 2 ∧ entryRow indices k = some a ∧ entryCol indices k = some b), ∃ r, odd_cells m n indices = ok r ∧
          r.val = (if indices.val.length % 2 = 1 then m.val + n.val - 2 else 0)) := by
    sorry

  /-- Let R(i) = |{ k | 0 <= k < len(indices) and indices[k][0] = i }| for 0 <= i < m, and C(j) = |{ k | 0 <= k < len(indices) and indices[k][1] = j }| for 0 <= j < n. The function returns a result r, and (r = 0) if and only if ( (for every i with 0 <= i < m, R(i) is even) and (for every j with 0 <= j < n, C(j) is even) ) or ( (for every i with 0 <= i < m, R(i) is odd) and (for every j with 0 <= j < n, C(j) is odd) ).
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_7
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        (r.val = 0 ↔
          ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 0) ∧
            (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 0)) ∨
          ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 1) ∧
            (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 1))) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          (r.val = 0 ↔
            ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 0) ∧
              (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 0)) ∨
            ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 1) ∧
              (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 1)))) := by
    sorry

  /-- Let indicesT be the slice of vectors of the same length with len(indicesT[k]) = 2, indicesT[k][0] = indices[k][1], and indicesT[k][1] = indices[k][0] for every k with 0 <= k < len(indices). The function returns a result r on (m,n,indices), and the call odd_cells(n,m,indicesT) also returns the same result r.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_8
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        ∀ indicesT : Idx, IsTranspose indices indicesT → odd_cells n m indicesT = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          ∀ indicesT : Idx, IsTranspose indices indicesT → odd_cells n m indicesT = ok r) := by
    sorry

  /-- For every slice indices' that is a reordering of indices — that is, len(indices') = len(indices) and there is a bijection p from {0,...,len(indices)-1} to itself such that indices'[k] = indices[p(k)] for every k — the function returns a result r on (m,n,indices), and odd_cells(m,n,indices') also returns the same result r.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_9
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        ∀ indices' : Idx, IsReordering indices indices' → odd_cells m n indices' = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          ∀ indices' : Idx, IsReordering indices indices' → odd_cells m n indices' = ok r) := by
    sorry

  /-- For every a,b with 0 <= a < m and 0 <= b < n, let indices' be the slice obtained from indices by appending two vectors [a,b], so len(indices') = len(indices)+2 and the last two entries both have first component a and second component b. The function returns a result r on (m,n,indices), and odd_cells(m,n,indices') also returns the same result r.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, len(indices)+2 <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_10
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hlen102 : indices.val.length + 2 ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        ∀ (a b : ℤ), 0 ≤ a → a < m.val → 0 ≤ b → b < n.val →
          ∀ indices' : Idx, IsAppendPair indices indices' a b → odd_cells m n indices' = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hlen102 : indices.val.length + 2 ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          ∀ (a b : ℤ), 0 ≤ a → a < m.val → 0 ≤ b → b < n.val →
            ∀ indices' : Idx, IsAppendPair indices indices' a b → odd_cells m n indices' = ok r) := by
    sorry

  /-- Let R(i) = |{ k | 0 <= k < len(indices) and indices[k][0] = i }| for 0 <= i < m, and C(j) = |{ k | 0 <= k < len(indices) and indices[k][1] = j }| for 0 <= j < n. The function returns a result r and, if there exist i with 0 <= i < m such that R(i) is odd and j with 0 <= j < n such that C(j) is even, then r > 0.
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_11
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        ((∃ i : ℤ, 0 ≤ i ∧ i < m.val ∧ rowCount indices i % 2 = 1) ∧
            (∃ j : ℤ, 0 ≤ j ∧ j < n.val ∧ colCount indices j % 2 = 0) →
          0 < r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          ((∃ i : ℤ, 0 ≤ i ∧ i < m.val ∧ rowCount indices i % 2 = 1) ∧
              (∃ j : ℤ, 0 ≤ j ∧ j < n.val ∧ colCount indices j % 2 = 0) →
            0 < r.val)) := by
    sorry

  /-- Let R(i) = |{ k | 0 <= k < len(indices) and indices[k][0] = i }| for 0 <= i < m, and C(j) = |{ k | 0 <= k < len(indices) and indices[k][1] = j }| for 0 <= j < n. The function returns a result r, and r = m*n if and only if either (for every i with 0 <= i < m, R(i) is odd and for every j with 0 <= j < n, C(j) is even) or (for every i with 0 <= i < m, R(i) is even and for every j with 0 <= j < n, C(j) is odd).
    Preconditions: m and n are 64-bit integers with 1 <= m <= 50 and 1 <= n <= 50. indices is a slice of vectors, 1 <= len(indices) <= 100, and for every k with 0 <= k < len(indices), len(indices[k]) = 2, 0 <= indices[k][0] < m, and 0 <= indices[k][1] < n. -/
  theorem spec_12
      (m n : Std.I64) (indices : Idx)
      (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
      (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
      (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
      (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
      (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
      (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val) :
      ∃ r, odd_cells m n indices = ok r ∧
        (r.val = m.val * n.val ↔
          ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 1) ∧
            (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 0)) ∨
          ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 0) ∧
            (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 1))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (m n : Std.I64) (indices : Idx)
        (hm1 : 1 ≤ m.val) (hm50 : m.val ≤ 50)
        (hn1 : 1 ≤ n.val) (hn50 : n.val ≤ 50)
        (hlen1 : 1 ≤ indices.val.length) (hlen100 : indices.val.length ≤ 100)
        (hentry : ∀ k, k < indices.val.length → entryLen indices k = some 2)
        (hrow : ∀ k, k < indices.val.length → ∀ a, entryRow indices k = some a → 0 ≤ a ∧ a < m.val)
        (hcol : ∀ k, k < indices.val.length → ∀ b, entryCol indices k = some b → 0 ≤ b ∧ b < n.val), ∃ r, odd_cells m n indices = ok r ∧
          (r.val = m.val * n.val ↔
            ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 1) ∧
              (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 0)) ∨
            ((∀ i : ℤ, 0 ≤ i → i < m.val → rowCount indices i % 2 = 0) ∧
              (∀ j : ℤ, 0 ≤ j → j < n.val → colCount indices j % 2 = 1)))) := by
    sorry

  end AegisSpec.OddCells
