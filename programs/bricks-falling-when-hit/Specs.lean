import Aegis.HitBricks.Code.Funs

/-!
# Specifications of `Aegis.HitBricks.hit_bricks`

LeetCode problem `bricks-falling-when-hit`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HitBricks

  noncomputable section

  open Classical

  abbrev Pos : Type := ℕ × ℕ

  def entry (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Option ℤ :=
    (grid.val[i]?).bind (fun row => (row.val[j]?).map (fun v => v.val))

  def getI (l : List I64) (k : ℕ) : Option ℤ := (l[k]?).map (fun v => v.val)

  def sumI (l : List I64) (L : ℕ) : ℤ := ((l.take L).map (fun v => v.val)).sum

  def Adjacent (p q : Pos) : Prop :=
    (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
      (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

  def ConnIn (S : Set Pos) (p q : Pos) : Prop :=
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adjacent a b) p q

  def stable (S : Set Pos) : Set Pos :=
    {p | p ∈ S ∧ ∃ q, q ∈ S ∧ q.1 = 0 ∧ ConnIn S p q}

  def bricks (grid : Slice (alloc.vec.Vec I64)) : Set Pos :=
    {p | entry grid p.1 p.2 = some 1}

  def afterHit (S : Set Pos) (p : Pos) : Set Pos := {q | q ∈ S ∧ q ≠ p}

  def state (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) : ℕ → Set Pos
    | 0 => stable (bricks grid)
    | k + 1 => stable (afterHit (state grid hit k) (hit k))

  def hitState (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) (k : ℕ) : Set Pos :=
    afterHit (state grid hit k) (hit k)

  def fallCount (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) (k : ℕ) : ℤ :=
    ((hitState grid hit k).ncard : ℤ) - ((state grid hit (k + 1)).ncard : ℤ)

  def removed (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) : ℕ → Set Pos
    | 0 => ∅
    | k + 1 => removed grid hit k ∪ (state grid hit k \ state grid hit (k + 1))

  def fell (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) (k : ℕ) : Set Pos :=
    hitState grid hit k \ state grid hit (k + 1)

  def directHitCount (grid : Slice (alloc.vec.Vec I64)) (hit : ℕ → Pos) (L : ℕ) : ℤ :=
    ((List.range L).map (fun k => if hit k ∈ state grid hit k then (1 : ℤ) else 0)).sum

  structure GridOK (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop where

    m_eq : m = grid.val.length

    m_pos : 1 ≤ m

    n_pos : 1 ≤ n
    m_bound : m ≤ 200
    n_bound : n ≤ 200

    rows_len : ∀ row ∈ grid.val, row.val.length = n

    entries_binary : ∀ i j, i < m → j < n → entry grid i j = some 0 ∨ entry grid i j = some 1

  structure HitsOK (hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos) : Prop where

    L_eq : L = hits.val.length

    L_pos : 1 ≤ L
    L_bound : L ≤ 40000

    hit_len : ∀ k, k < L → ∃ v : alloc.vec.Vec I64, hits.val[k]? = some v ∧ v.val.length = 2

    hit_eq : ∀ k, k < L → ∃ (v : alloc.vec.Vec I64) (x y : I64),
      hits.val[k]? = some v ∧ v.val = [x, y] ∧ hit k = (x.val.toNat, y.val.toNat) ∧
        x.val = ((hit k).1 : ℤ) ∧ y.val = ((hit k).2 : ℤ)

    hit_bounds : ∀ k, k < L → (hit k).1 < m ∧ (hit k).2 < n

    hit_distinct : ∀ k l, k < L → l < L → hit k = hit l → k = l

  /-- Let B = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}. For a set S of positions, define stable(S) as the union of all 4-connected components of S that contain at least one position in row 0 (i.e., with first coordinate 0). Let S_0 = stable(B). For k = 0,1,...,len(hits)-1, let h_k = (hits[k][0], hits[k][1]). Define T_k = S_k \ {h_k} if h_k ∈ S_k, else T_k = S_k. Define S_{k+1} = stable(T_k). The function returns a result r such that len(r) = len(hits) and for every k with 0 <= k < len(hits), r[k] = |T_k| - |S_{k+1}|.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_1 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r ∧
        r.val.length = L ∧ ∀ k, k < L → getI r.val k = some (fallCount grid hit k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r ∧
          r.val.length = L ∧ ∀ k, k < L → getI r.val k = some (fallCount grid hit k)) := by
    sorry

  /-- The function returns a result r and len(r) = len(hits).
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_2 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r ∧
        r.val.length = L := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r ∧
          r.val.length = L) := by
    sorry

  /-- The function returns a result r (it does not panic, overflow, or go out of bounds).
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_3 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∃ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r) := by
    sorry

  /-- For every k with 0 <= k < len(hits), 0 <= r[k] <= |S_k| - (1 if h_k ∈ S_k else 0), where S_k and h_k are defined as in spec_1.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_4 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
        ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧ 0 ≤ v ∧
          v ≤ ((state grid hit k).ncard : ℤ) -
            (if hit k ∈ state grid hit k then (1 : ℤ) else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
          ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧ 0 ≤ v ∧
            v ≤ ((state grid hit k).ncard : ℤ) -
              (if hit k ∈ state grid hit k then (1 : ℤ) else 0)) := by
    sorry

  /-- For every k with 0 <= k < len(hits), |S_{k+1}| = |S_k| - (1 if h_k ∈ S_k else 0) - r[k], where S_k and h_k are defined as in spec_1.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_5 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
        ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧
          ((state grid hit (k + 1)).ncard : ℤ) = ((state grid hit k).ncard : ℤ) -
            (if hit k ∈ state grid hit k then (1 : ℤ) else 0) - v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
          ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧
            ((state grid hit (k + 1)).ncard : ℤ) = ((state grid hit k).ncard : ℤ) -
              (if hit k ∈ state grid hit k then (1 : ℤ) else 0) - v) := by
    sorry

  /-- Let L = len(hits) and let D = sum_{k=0}^{L-1} (1 if h_k ∈ S_k else 0). Then sum_{k=0}^{L-1} r[k] = |S_0| - |S_L| - D, where S_k and h_k are defined as in spec_1.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_6 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
        sumI r.val L = ((state grid hit 0).ncard : ℤ) - ((state grid hit L).ncard : ℤ) -
          directHitCount grid hit L := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
          sumI r.val L = ((state grid hit 0).ncard : ℤ) - ((state grid hit L).ncard : ℤ) -
            directHitCount grid hit L) := by
    sorry

  /-- For every k with 0 <= k < len(hits), if h_k ∈ S_k and h_k is the only position in S_k with row 0, then r[k] = |S_k| - 1, where S_k and h_k are defined as in spec_1.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_7 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
        ∀ k, k < L → hit k ∈ state grid hit k →
          (∀ q : Pos, q ∈ state grid hit k → q.1 = 0 → q = hit k) →
          ∃ v : ℤ, getI r.val k = some v ∧ v = ((state grid hit k).ncard : ℤ) - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
          ∀ k, k < L → hit k ∈ state grid hit k →
            (∀ q : Pos, q ∈ state grid hit k → q.1 = 0 → q = hit k) →
            ∃ v : ℤ, getI r.val k = some v ∧ v = ((state grid hit k).ncard : ℤ) - 1) := by
    sorry

  /-- For every k with 0 <= k < len(hits), r[k] = 0 if and only if S_{k+1} = T_k, where T_k and S_k are defined as in spec_1.
    Preconditions: grid is a non-empty slice of non-empty vectors of 64-bit integers, all rows have the same length n, with m = len(grid) and 1 <= m, n <= 200. Every entry of grid is 0 or 1. hits is a non-empty slice of vectors of 64-bit integers, each of length 2, with 1 <= len(hits) <= 40000. For every k with 0 <= k < len(hits), hits[k] = [x_k, y_k] with 0 <= x_k < m and 0 <= y_k < n. All pairs (x_k, y_k) are distinct. -/
  theorem spec_8 (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
      (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit) :
      ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
        ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧
          (v = 0 ↔ state grid hit (k + 1) = hitState grid hit k) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid hits : Slice (alloc.vec.Vec I64)) (m n L : ℕ) (hit : ℕ → Pos)
        (hgrid : GridOK grid m n) (hhits : HitsOK hits m n L hit), ∀ r : alloc.vec.Vec I64, Aegis.HitBricks.hit_bricks grid hits = ok r →
          ∀ k, k < L → ∃ v : ℤ, getI r.val k = some v ∧
            (v = 0 ↔ state grid hit (k + 1) = hitState grid hit k)) := by
    sorry

  end

  end AegisSpec.HitBricks
