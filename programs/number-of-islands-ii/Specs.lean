import Aegis.NumIslands2.Code.Funs

/-!
# Specifications of `Aegis.NumIslands2.num_islands2`

LeetCode problem `number-of-islands-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical
open Aegis.NumIslands2 (num_islands2)

namespace AegisSpec.NumIslands2

abbrev VecI64 : Type := alloc.vec.Vec I64

abbrev Cell : Type := ℤ × ℤ

def posList (positions : Slice VecI64) (i : ℕ) : List I64 :=
  (positions.val.getD i default).val

def coordAt (positions : Slice VecI64) (i j : ℕ) : ℤ :=
  ((posList positions i).getD j default).val

def cellAt (positions : Slice VecI64) (i : ℕ) : Cell :=
  (coordAt positions i 0, coordAt positions i 1)

def entry (v : VecI64) (i : ℕ) : ℤ := (v.val.getD i default).val

def Adj4 (p q : Cell) : Prop :=
  Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2) = 1

def inGrid (m n : ℤ) (p : Cell) : Prop :=
  0 ≤ p.1 ∧ p.1 < m ∧ 0 ≤ p.2 ∧ p.2 < n

noncomputable def pointSet (m n : ℤ) (positions : Slice VecI64) (t : ℕ) : Finset Cell :=
  ((Finset.range t).image (fun j => cellAt positions j)).filter (inGrid m n)

def adjIn (L : Finset Cell) (p q : Cell) : Prop :=
  p ∈ L ∧ q ∈ L ∧ Adj4 p q

def reachIn (L : Finset Cell) (p q : Cell) : Prop :=
  p ∈ L ∧ q ∈ L ∧ Relation.ReflTransGen (adjIn L) p q

noncomputable def comps (L : Finset Cell) : Finset (Finset Cell) :=
  L.image (fun p => L.filter (fun q => reachIn L p q))

noncomputable def numComps (L : Finset Cell) : ℕ := (comps L).card

noncomputable def neighborComps (L : Finset Cell) (p : Cell) : ℕ :=
  ((comps L).filter (fun C => ∃ q ∈ C, Adj4 q p)).card

def ConnectedSet (L : Finset Cell) : Prop :=
  ∀ p ∈ L, ∀ q ∈ L, reachIn L p q

def numBlocks (C : Finset ℤ) : ℕ :=
  (C.filter (fun c => c = 0 ∨ c - 1 ∉ C)).card

noncomputable def colSet (m n : ℤ) (positions : Slice VecI64) (i : ℕ) : Finset ℤ :=
  ((pointSet m n positions (i + 1)).filter (fun p => p.1 = 0)).image (fun p => p.2)

noncomputable def rowSet (m n : ℤ) (positions : Slice VecI64) (i : ℕ) : Finset ℤ :=
  ((pointSet m n positions (i + 1)).filter (fun p => p.2 = 0)).image (fun p => p.1)

/-- Whenever the function returns a result r, len(r) = len(positions) and for every i with 0 <= i < len(positions), r[i] equals the number of connected components of the set L_{i+1}, where for 0 <= t <= len(positions), L_t = { (a,b) | 0 <= a < m, 0 <= b < n, and there exists j with 0 <= j < t such that positions[j][0] = a and positions[j][1] = b }; two cells (a,b) and (c,d) are adjacent iff |a-c| + |b-d| = 1, and the connected components are the equivalence classes of L_{i+1} under the reflexive-transitive closure of this adjacency restricted to L_{i+1} (with 0 components when the set is empty).
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_1 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      r.val.length = positions.val.length ∧
      ∀ i, i < positions.val.length →
        entry r i = (numComps (pointSet m.val n.val positions (i + 1)) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      r.val.length = positions.val.length ∧
      ∀ i, i < positions.val.length →
        entry r i = (numComps (pointSet m.val n.val positions (i + 1)) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or go out of bounds).
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_2 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∃ r, num_islands2 m n positions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∃ r, num_islands2 m n positions = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(positions).
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_3 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      r.val.length = positions.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      r.val.length = positions.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(positions), 1 <= r[i] <= |L_{i+1}| <= min(i+1, m*n), where L_{i+1} is the set of distinct positions among positions[0], ..., positions[i].
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_4 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        1 ≤ entry r i ∧
        entry r i ≤ ((pointSet m.val n.val positions (i + 1)).card : ℤ) ∧
        (pointSet m.val n.val positions (i + 1)).card ≤ min (i + 1) (m.val * n.val).toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        1 ≤ entry r i ∧
        entry r i ≤ ((pointSet m.val n.val positions (i + 1)).card : ℤ) ∧
        (pointSet m.val n.val positions (i + 1)).card ≤ min (i + 1) (m.val * n.val).toNat) := by
  sorry

/-- Whenever the function returns a result r, r[0] = 1.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_5 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r → entry r 0 = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r → entry r 0 = 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < len(positions), if there exists j with 0 <= j < i such that positions[j][0] = positions[i][0] and positions[j][1] = positions[i][1], then r[i] = r[i-1].
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_6 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, 1 ≤ i → i < positions.val.length →
        (∃ j, j < i ∧ cellAt positions j = cellAt positions i) →
        entry r i = entry r (i - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, 1 ≤ i → i < positions.val.length →
        (∃ j, j < i ∧ cellAt positions j = cellAt positions i) →
        entry r i = entry r (i - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < len(positions) such that positions[i] is not in L_i (where L_i is the set of distinct positions among positions[0], ..., positions[i-1]), let c_i be the number of distinct connected components of L_i that contain at least one cell 4-adjacent to positions[i]; then r[i] = r[i-1] + 1 - c_i. Here cells (a,b) and (c,d) are 4-adjacent iff |a-c| + |b-d| = 1.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_7 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, 1 ≤ i → i < positions.val.length →
        cellAt positions i ∉ pointSet m.val n.val positions i →
        entry r i = entry r (i - 1) + 1 -
          (neighborComps (pointSet m.val n.val positions i) (cellAt positions i) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, 1 ≤ i → i < positions.val.length →
        cellAt positions i ∉ pointSet m.val n.val positions i →
        entry r i = entry r (i - 1) + 1 -
          (neighborComps (pointSet m.val n.val positions i) (cellAt positions i) : ℤ)) := by
  sorry

/-- Let T(positions) be the array of length len(positions) with T[i][0] = positions[i][1] and T[i][1] = positions[i][0] for every i. Whenever the call num_islands2(m, n, positions) returns r and the call num_islands2(n, m, T(positions)) returns r', it holds that len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(positions).
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n. -/
theorem spec_8 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ positions' : Slice VecI64,
        positions'.val.length = positions.val.length →
        (∀ j, j < positions.val.length →
          coordAt positions' j 0 = coordAt positions j 1 ∧
          coordAt positions' j 1 = coordAt positions j 0) →
        ∀ r', num_islands2 n m positions' = ok r' →
          r.val.length = r'.val.length ∧
          ∀ i, i < positions.val.length → entry r i = entry r' i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val), ∀ r, num_islands2 m n positions = ok r →
      ∀ positions' : Slice VecI64,
        positions'.val.length = positions.val.length →
        (∀ j, j < positions.val.length →
          coordAt positions' j 0 = coordAt positions j 1 ∧
          coordAt positions' j 1 = coordAt positions j 0) →
        ∀ r', num_islands2 n m positions' = ok r' →
          r.val.length = r'.val.length ∧
          ∀ i, i < positions.val.length → entry r i = entry r' i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(positions), r[i] = i + 1.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n; for every a and b with 0 <= a < b < len(positions), positions[a] != positions[b] and |positions[a][0] - positions[b][0]| + |positions[a][1] - positions[b][1]| != 1. -/
theorem spec_9 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hsep : ∀ a b, a < b → b < positions.val.length →
      cellAt positions a ≠ cellAt positions b ∧ ¬ Adj4 (cellAt positions a) (cellAt positions b)) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length → entry r i = (i : ℤ) + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hsep : ∀ a b, a < b → b < positions.val.length →
      cellAt positions a ≠ cellAt positions b ∧ ¬ Adj4 (cellAt positions a) (cellAt positions b)), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length → entry r i = (i : ℤ) + 1) := by
  sorry

/-- Whenever the function returns a result r, r[len(positions)-1] = 1.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n; let L be the set of distinct positions occurring in positions, and assume L is connected under 4-adjacency: for any two cells p and q in L there is a sequence p = x_0, x_1, ..., x_s = q of cells in L such that x_{j-1} and x_j are 4-adjacent for every 1 <= j <= s. -/
theorem spec_10 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hconn : ConnectedSet (pointSet m.val n.val positions positions.val.length)) :
    ∀ r, num_islands2 m n positions = ok r → entry r (positions.val.length - 1) = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hconn : ConnectedSet (pointSet m.val n.val positions positions.val.length)), ∀ r, num_islands2 m n positions = ok r → entry r (positions.val.length - 1) = 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(positions), let C_i = { c | 0 <= c < n and there exists j with 0 <= j <= i such that positions[j][0] = 0 and positions[j][1] = c }. Then r[i] equals the number of maximal contiguous blocks of columns in C_i, i.e., the number of integers c in C_i such that c = 0 or c - 1 is not in C_i.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n; and m = 1. -/
theorem spec_11 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hm : m.val = 1) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        entry r i = (numBlocks (colSet m.val n.val positions i) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hm : m.val = 1), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        entry r i = (numBlocks (colSet m.val n.val positions i) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(positions), let R_i = { a | 0 <= a < m and there exists j with 0 <= j <= i such that positions[j][0] = a and positions[j][1] = 0 }. Then r[i] equals the number of maximal contiguous blocks of rows in R_i, i.e., the number of integers a in R_i such that a = 0 or a - 1 is not in R_i.
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m, and 0 <= positions[i][1] < n; and n = 1. -/
theorem spec_12 (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hn : n.val = 1) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        entry r i = (numBlocks (rowSet m.val n.val positions i) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (m n : I64) (positions : Slice VecI64)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n.val)
    (hn : n.val = 1), ∀ r, num_islands2 m n positions = ok r →
      ∀ i, i < positions.val.length →
        entry r i = (numBlocks (rowSet m.val n.val positions i) : ℤ)) := by
  sorry

/-- Whenever num_islands2(m, n, positions) returns r and num_islands2(m, n, positions') returns r', it holds that r[i] = r'[i].
  Preconditions: m and n are integers with 1 <= m <= 10000, 1 <= n <= 10000, and m*n <= 10000; positions and positions' are slices of vectors, each with length between 1 and 10000, each element of length 2, and all coordinates within the m by n grid; i is an integer with 0 <= i < min(len(positions), len(positions')); and positions[j][0] = positions'[j][0] and positions[j][1] = positions'[j][1] for every j with 0 <= j <= i. -/
theorem spec_13 (m n : I64) (positions positions' : Slice VecI64) (i : ℕ)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ j, j < positions.val.length → (posList positions j).length = 2)
    (hbound : ∀ j, j < positions.val.length →
      0 ≤ coordAt positions j 0 ∧ coordAt positions j 0 < m.val ∧
      0 ≤ coordAt positions j 1 ∧ coordAt positions j 1 < n.val)
    (hlen'_lo : 1 ≤ positions'.val.length) (hlen'_hi : positions'.val.length ≤ 10000)
    (hinner' : ∀ j, j < positions'.val.length → (posList positions' j).length = 2)
    (hbound' : ∀ j, j < positions'.val.length →
      0 ≤ coordAt positions' j 0 ∧ coordAt positions' j 0 < m.val ∧
      0 ≤ coordAt positions' j 1 ∧ coordAt positions' j 1 < n.val)
    (hi : i < min positions.val.length positions'.val.length)
    (hagree : ∀ j, j ≤ i → cellAt positions j = cellAt positions' j) :
    ∀ r, num_islands2 m n positions = ok r →
      ∀ r', num_islands2 m n positions' = ok r' → entry r i = entry r' i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (m n : I64) (positions positions' : Slice VecI64) (i : ℕ)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 10000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hmn : m.val * n.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ j, j < positions.val.length → (posList positions j).length = 2)
    (hbound : ∀ j, j < positions.val.length →
      0 ≤ coordAt positions j 0 ∧ coordAt positions j 0 < m.val ∧
      0 ≤ coordAt positions j 1 ∧ coordAt positions j 1 < n.val)
    (hlen'_lo : 1 ≤ positions'.val.length) (hlen'_hi : positions'.val.length ≤ 10000)
    (hinner' : ∀ j, j < positions'.val.length → (posList positions' j).length = 2)
    (hbound' : ∀ j, j < positions'.val.length →
      0 ≤ coordAt positions' j 0 ∧ coordAt positions' j 0 < m.val ∧
      0 ≤ coordAt positions' j 1 ∧ coordAt positions' j 1 < n.val)
    (hi : i < min positions.val.length positions'.val.length)
    (hagree : ∀ j, j ≤ i → cellAt positions j = cellAt positions' j), ∀ r, num_islands2 m n positions = ok r →
      ∀ r', num_islands2 m n positions' = ok r' → entry r i = entry r' i) := by
  sorry

/-- Whenever num_islands2(m1, n1, positions) returns r and num_islands2(m2, n2, positions) returns r', it holds that len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(positions).
  Preconditions: m1, m2, n1, n2 are integers with 1 <= m1 <= m2 <= 10000, 1 <= n1 <= n2 <= 10000, m1*n1 <= 10000, and m2*n2 <= 10000; positions is a slice of vectors with 1 <= len(positions) <= 10000; for every i with 0 <= i < len(positions), len(positions[i]) = 2, 0 <= positions[i][0] < m1, and 0 <= positions[i][1] < n1. -/
theorem spec_14 (m1 m2 n1 n2 : I64) (positions : Slice VecI64)
    (hm1_lo : 1 ≤ m1.val) (hm1_hi : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ 10000)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 10000)
    (hpr1 : m1.val * n1.val ≤ 10000) (hpr2 : m2.val * n2.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m1.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n1.val) :
    ∀ r, num_islands2 m1 n1 positions = ok r →
      ∀ r', num_islands2 m2 n2 positions = ok r' →
        r.val.length = r'.val.length ∧
        ∀ i, i < positions.val.length → entry r i = entry r' i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (m1 m2 n1 n2 : I64) (positions : Slice VecI64)
    (hm1_lo : 1 ≤ m1.val) (hm1_hi : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ 10000)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 10000)
    (hpr1 : m1.val * n1.val ≤ 10000) (hpr2 : m2.val * n2.val ≤ 10000)
    (hlen_lo : 1 ≤ positions.val.length) (hlen_hi : positions.val.length ≤ 10000)
    (hinner : ∀ i, i < positions.val.length → (posList positions i).length = 2)
    (hbound : ∀ i, i < positions.val.length →
      0 ≤ coordAt positions i 0 ∧ coordAt positions i 0 < m1.val ∧
      0 ≤ coordAt positions i 1 ∧ coordAt positions i 1 < n1.val), ∀ r, num_islands2 m1 n1 positions = ok r →
      ∀ r', num_islands2 m2 n2 positions = ok r' →
        r.val.length = r'.val.length ∧
        ∀ i, i < positions.val.length → entry r i = entry r' i) := by
  sorry

end AegisSpec.NumIslands2
