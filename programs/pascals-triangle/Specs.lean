import Aegis.Generate.Code.Funs

/-!
# Specifications of `Aegis.Generate.generate`

LeetCode problem `pascals-triangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Generate

  abbrev Matrix : Type := Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  def row (r : Matrix) (i : Nat) : List Std.I64 :=
    match r.val[i]? with
    | some row => row.val
    | none => []

  def entry (r : Matrix) (i j : Nat) : Int :=
    match (row r i)[j]? with
    | some x => x.val
    | none => 0

  def fact : Nat → Nat
    | 0 => 1
    | m + 1 => (m + 1) * fact m

  def binom (i j : Nat) : Nat := fact i / (fact j * fact (i - j))

  def rangeSum : Nat → (Nat → Int) → Int
    | 0, _ => 0
    | n + 1, f => rangeSum n f + f n

  def rowSum (r : Matrix) (i : Nat) : Int := rangeSum (i + 1) (fun j => entry r i j)

  def rowAltSum (r : Matrix) (i : Nat) : Int :=
    rangeSum (i + 1) (fun j => (-1 : Int) ^ j * entry r i j)

  /-- The function returns a result r such that: (a) len(r) = numRows; (b) for every i with 0 <= i < numRows, len(r[i]) = i + 1; (c) for every i with 0 <= i < numRows and every j with 0 <= j <= i, r[i][j] = C(i, j), where C(i, j) = i! / (j! * (i - j)!) for 0 <= j <= i, with 0! = 1 and m! = m * (m - 1)! for m >= 1. Thus r is exactly the first numRows rows of Pascal's triangle.
    Preconditions: numRows is an i64 with 1 <= numRows <= 30. -/
  theorem spec_1 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        r.val.length = numRows.val.toNat ∧
        (∀ i : Nat, i < numRows.val.toNat → (row r i).length = i + 1) ∧
        (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i → entry r i j = (binom i j : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          r.val.length = numRows.val.toNat ∧
          (∀ i : Nat, i < numRows.val.toNat → (row r i).length = i + 1) ∧
          (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i → entry r i j = (binom i j : Int))) := by
    sorry

  /-- The function returns a result r such that len(r) = numRows; that is, the returned vector has exactly numRows rows.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_2 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧ r.val.length = numRows.val.toNat := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧ r.val.length = numRows.val.toNat) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows, len(r[i]) = i + 1; that is, row i has exactly i + 1 entries.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_3 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat → (row r i).length = i + 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat → (row r i).length = i + 1)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows, r[i][0] = 1; that is, every row begins with 1.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_4 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat → entry r i 0 = 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat → entry r i 0 = 1)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows, r[i][i] = 1; that is, every row ends with 1.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_5 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat → entry r i i = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat → entry r i i = 1)) := by
    sorry

  /-- The function returns a result r such that for every i with 1 <= i < numRows and every j with 1 <= j < i, r[i][j] = r[i - 1][j - 1] + r[i - 1][j].
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_6 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ (i j : Nat), 1 ≤ i → i < numRows.val.toNat → 1 ≤ j → j < i →
          entry r i j = entry r (i - 1) (j - 1) + entry r (i - 1) j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ (i j : Nat), 1 ≤ i → i < numRows.val.toNat → 1 ≤ j → j < i →
            entry r i j = entry r (i - 1) (j - 1) + entry r (i - 1) j)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows and every j with 0 <= j <= i, r[i][j] = r[i][i - j].
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_7 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i → entry r i j = entry r i (i - j)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i → entry r i j = entry r i (i - j))) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows and every j with 0 <= j <= i, 1 <= r[i][j] <= C(i, floor(i/2)), where C(i, k) = i! / (k! * (i - k)!) and floor(i/2) is the integer division of i by 2. Since C(i, floor(i/2)) <= 77558760 < 2^63 - 1, no entry overflows i64.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_8 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i →
          1 ≤ entry r i j ∧ entry r i j ≤ (binom i (i / 2) : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ (i j : Nat), i < numRows.val.toNat → j ≤ i →
            1 ≤ entry r i j ∧ entry r i j ≤ (binom i (i / 2) : Int))) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows, the sum of all entries of row i satisfies sum_{j=0}^{i} r[i][j] = 2^i.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_9 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat → rowSum r i = (2 : Int) ^ i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat → rowSum r i = (2 : Int) ^ i)) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows, sum_{j=0}^{i} (-1)^j * r[i][j] equals 1 when i = 0 and equals 0 when i >= 1.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_10 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat → rowAltSum r i = if i = 0 then 1 else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat → rowAltSum r i = if i = 0 then 1 else 0)) := by
    sorry

  /-- For every numRows with 1 <= numRows <= 30, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_11 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix, Aegis.Generate.generate numRows = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix, Aegis.Generate.generate numRows = ok r) := by
    sorry

  /-- The function returns a result r such that for every i with 1 <= i < numRows, r[i][1] = i.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_12 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, 1 ≤ i → i < numRows.val.toNat → entry r i 1 = (i : Int)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, 1 ≤ i → i < numRows.val.toNat → entry r i 1 = (i : Int))) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < numRows there exists an integer m with 0 <= m <= i for which r[i][j] <= r[i][j + 1] for every j with 0 <= j < m, and r[i][j] >= r[i][j + 1] for every j with m <= j < i; that is, each row is nondecreasing up to a peak and nonincreasing afterward.
    Preconditions: 1 <= numRows <= 30. -/
  theorem spec_13 (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30) :
      ∃ r : Matrix,
        Aegis.Generate.generate numRows = ok r ∧
        (∀ i : Nat, i < numRows.val.toNat →
          ∃ m : Nat, m ≤ i ∧
            (∀ j : Nat, j < m → entry r i j ≤ entry r i (j + 1)) ∧
            (∀ j : Nat, m ≤ j → j < i → entry r i j ≥ entry r i (j + 1))) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (numRows : Std.I64) (hlo : 1 ≤ numRows.val) (hhi : numRows.val ≤ 30), ∃ r : Matrix,
          Aegis.Generate.generate numRows = ok r ∧
          (∀ i : Nat, i < numRows.val.toNat →
            ∃ m : Nat, m ≤ i ∧
              (∀ j : Nat, j < m → entry r i j ≤ entry r i (j + 1)) ∧
              (∀ j : Nat, m ≤ j → j < i → entry r i j ≥ entry r i (j + 1)))) := by
    sorry

  end AegisSpec.Generate
