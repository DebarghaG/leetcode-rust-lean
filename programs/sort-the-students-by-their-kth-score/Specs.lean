import Aegis.SortTheStudents.Code.Funs

/-!
# Specifications of `Aegis.SortTheStudents.sort_the_students`

LeetCode problem `sort-the-students-by-their-kth-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.SortTheStudents

def rowsOf (rows : List (alloc.vec.Vec I64)) : List (List Int) :=
  rows.map (fun v => v.val)

def row (rows : List (alloc.vec.Vec I64)) (i : Nat) : List Int :=
  (rowsOf rows).getD i []

def entry (rows : List (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  (row rows i).getD j 0

def column (rows : List (alloc.vec.Vec I64)) (kk : Nat) : List Int :=
  (rowsOf rows).map (fun l => l.getD kk 0)

def countOcc {α : Type} [DecidableEq α] (a : α) (l : List α) : Nat :=
  l.countP (fun x => decide (x = a))

def IsIthLargest (l : List Int) (i : Nat) (x : Int) : Prop :=
  x ∈ l ∧ l.countP (fun y => decide (x < y)) = i

/-- The function returns a result r (i.e., it does not fail) such that: (1) len(r) = m and for every i with 0 <= i < m, len(r[i]) = n; (2) r is a permutation of the rows of score: there exists a bijection π from {0,...,m-1} to {0,...,m-1} such that for all i with 0 <= i < m, r[i] = score[π(i)]; (3) for all i, j with 0 <= i < j < m, r[i][k] > r[j][k].
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_1 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → (row r.val i).length = n) ∧
        (∃ π : Fin m → Fin m, Function.Bijective π ∧
          ∀ i : Fin m, row r.val i.val = row score.val (π i).val) ∧
        (∀ i j, i < j → j < m → entry r.val i k.val.toNat > entry r.val j k.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → (row r.val i).length = n) ∧
        (∃ π : Fin m → Fin m, Function.Bijective π ∧
          ∀ i : Fin m, row r.val i.val = row score.val (π i).val) ∧
        (∀ i j, i < j → j < m → entry r.val i k.val.toNat > entry r.val j k.val.toNat)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic) for any input satisfying the preconditions.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_2 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r) := by
  sorry

/-- The function returns a result r with len(r) = m.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_3 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧ r.val.length = m := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧ r.val.length = m) := by
  sorry

/-- The function returns a result r such that for every i with 0 <= i < m, len(r[i]) = n.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_4 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m → (row r.val i).length = n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m → (row r.val i).length = n) := by
  sorry

/-- The function returns a result r such that for every vector v, the number of occurrences of v in r equals the number of occurrences of v in score. Equivalently, the multiset of rows of r equals the multiset of rows of score.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_5 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ v : List Int, countOcc v (rowsOf r.val) = countOcc v (rowsOf score.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ v : List Int, countOcc v (rowsOf r.val) = countOcc v (rowsOf score.val)) := by
  sorry

/-- The function returns a result r such that for all i, j with 0 <= i < j < m, r[i][k] > r[j][k].
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_6 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < j → j < m →
          entry r.val i k.val.toNat > entry r.val j k.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < j → j < m →
          entry r.val i k.val.toNat > entry r.val j k.val.toNat) := by
  sorry

/-- The function returns a result r such that for every i with 0 <= i < m, the value r[i][k] is the i-th largest element (0-indexed, so i=0 is the largest) of the multiset {score[t][k] | 0 <= t < m}.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_7 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m →
          IsIthLargest (column score.val k.val.toNat) i (entry r.val i k.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m →
          IsIthLargest (column score.val k.val.toNat) i (entry r.val i k.val.toNat)) := by
  sorry

/-- The function returns a result r such that for every i with 0 <= i < m, r[i] = score[j] where j is the unique index with 0 <= j < m such that score[j][k] is the i-th largest element of {score[t][k] | 0 <= t < m}.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_8 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m →
          ∃ j, j < m ∧
            IsIthLargest (column score.val k.val.toNat) i (entry score.val j k.val.toNat) ∧
            row r.val i = row score.val j ∧
            (∀ j', j' < m →
              IsIthLargest (column score.val k.val.toNat) i (entry score.val j' k.val.toNat) →
                j' = j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i, i < m →
          ∃ j, j < m ∧
            IsIthLargest (column score.val k.val.toNat) i (entry score.val j k.val.toNat) ∧
            row r.val i = row score.val j ∧
            (∀ j', j' < m →
              IsIthLargest (column score.val k.val.toNat) i (entry score.val j' k.val.toNat) →
                j' = j)) := by
  sorry

/-- The function returns a result r such that all rows of r are distinct: for all i, j with 0 <= i < j < m, r[i] != r[j].
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_9 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < j → j < m → row r.val i ≠ row r.val j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < j → j < m → row r.val i ≠ row r.val j) := by
  sorry

/-- The function returns a result r such that for every i, j with 0 <= i < m and 0 <= j < n, 1 <= r[i][j] <= 100000.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_10 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < m → j < n → 1 ≤ entry r.val i j ∧ entry r.val i j ≤ 100000 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ i j, i < m → j < n → 1 ≤ entry r.val i j ∧ entry r.val i j ≤ 100000) := by
  sorry

/-- The function returns a result r such that for any matrix s satisfying len(s) = m, len(s[i]) = n for all i with 0 <= i < m, the multiset of rows of s equals that of score, and s[i][k] > s[j][k] for all i, j with 0 <= i < j < m, it holds that s = r.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_11 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ s : Slice (alloc.vec.Vec I64),
          s.val.length = m →
          (∀ i, i < m → (row s.val i).length = n) →
          (∀ v : List Int, countOcc v (rowsOf s.val) = countOcc v (rowsOf score.val)) →
          (∀ i j, i < j → j < m → entry s.val i k.val.toNat > entry s.val j k.val.toNat) →
          rowsOf s.val = rowsOf r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ s : Slice (alloc.vec.Vec I64),
          s.val.length = m →
          (∀ i, i < m → (row s.val i).length = n) →
          (∀ v : List Int, countOcc v (rowsOf s.val) = countOcc v (rowsOf score.val)) →
          (∀ i j, i < j → j < m → entry s.val i k.val.toNat > entry s.val j k.val.toNat) →
          rowsOf s.val = rowsOf r.val) := by
  sorry

/-- The function returns a result r such that the multiset of elements in the k-th column of r, i.e., {r[i][k] | 0 <= i < m}, equals the multiset {score[i][k] | 0 <= i < m}.
  Preconditions: Let m = len(score) and n = len(score[0]). Assume: - m >= 1 and n >= 1; - for all i with 0 <= i < m, len(score[i]) = n; - k is an integer with 0 <= k < n; - for all i, j with 0 <= i < m and 0 <= j < n, 1 <= score[i][j] <= 100000; - all elements of score are distinct: for any (i1,j1) != (i2,j2) with 0 <= i1,i2 < m and 0 <= j1,j2 < n, score[i1][j1] != score[i2][j2]. -/
theorem spec_12 (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ x : Int, countOcc x (column r.val k.val.toNat) = countOcc x (column score.val k.val.toNat) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (score : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
    (hm : score.val.length = m)
    (hm1 : 1 ≤ m)
    (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → (row score.val i).length = n)
    (hk0 : 0 ≤ k.val)
    (hkn : k.val < (n : Int))
    (hentries : ∀ i j, i < m → j < n → 1 ≤ entry score.val i j ∧ entry score.val i j ≤ 100000)
    (hdistinct : ∀ i1 j1 i2 j2, i1 < m → j1 < n → i2 < m → j2 < n → (i1 ≠ i2 ∨ j1 ≠ j2) →
      entry score.val i1 j1 ≠ entry score.val i2 j2), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.SortTheStudents.sort_the_students score k = ok r ∧
        ∀ x : Int, countOcc x (column r.val k.val.toNat) = countOcc x (column score.val k.val.toNat)) := by
  sorry

end AegisSpec.SortTheStudents
