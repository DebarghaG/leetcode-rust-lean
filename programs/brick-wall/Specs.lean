import Aegis.LeastBricks.Code.Funs

/-!
# Specifications of `Aegis.LeastBricks.least_bricks`

LeetCode problem `brick-wall`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LeastBricks

  open Aegis.LeastBricks (least_bricks)

  abbrev Wall := Slice (alloc.vec.Vec Std.I64)

  def prefixSum (r : List Std.I64) (j : ℕ) : ℤ := ((r.take j).map (fun x => x.val)).sum

  def rowSum (r : List Std.I64) : ℤ := (r.map (fun x => x.val)).sum

  def IsBoundary (row : alloc.vec.Vec Std.I64) (c : ℤ) : Prop :=
    ∃ j, 1 ≤ j ∧ j < row.val.length ∧ prefixSum row.val j = c

  noncomputable def cnt (wall : Wall) (c : ℤ) : ℕ := by
    classical
    exact (wall.val.filter (fun row => decide (IsBoundary row c))).length

  noncomputable def maxCnt (wall : Wall) (W : ℤ) : ℤ :=
    ((List.range (W - 1).toNat).map (fun k => (cnt wall ((k : ℤ) + 1) : ℤ))).foldr
      (fun a b => max a b) 0

  def countSingleton (wall : Wall) : ℕ :=
    (wall.val.filter (fun row => row.val.length == 1)).length

  def RowsRel (R : alloc.vec.Vec Std.I64 → alloc.vec.Vec Std.I64 → Prop)
      (wall wall' : Wall) : Prop :=
    List.Forall₂ R wall.val wall'.val

  def WallPre (wall : Wall) (Nmax Smax : ℕ) (W : ℤ) : Prop :=
    1 ≤ wall.val.length ∧
      wall.val.length ≤ Nmax ∧
      (∀ row ∈ wall.val, 1 ≤ row.val.length ∧ row.val.length ≤ 10000) ∧
      (wall.val.map (fun row => row.val.length)).sum ≤ Smax ∧
      (∀ row ∈ wall.val, ∀ x ∈ row.val, 1 ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1) ∧
      (∀ row ∈ wall.val, rowSum row.val = W)

  /-- Whenever the function returns a result r, r = n - M, where M = max(0, max_{c in Z, 1 <= c <= W-1} cnt(c)), and for every such c, cnt(c) = #{ i | 0 <= i < n and there exists j with 1 <= j < len(wall[i]) and sum_{k=0}^{j-1} wall[i][k] = c }.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_1 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        r.val = (wall.val.length : ℤ) - maxCnt wall W := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          r.val = (wall.val.length : ℤ) - maxCnt wall W) := by
    sorry

  /-- The function returns a result r; it does not fail (no arithmetic overflow, no out-of-bounds access, and no panic).
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_2 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∃ r : Std.I64, least_bricks wall = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∃ r : Std.I64, least_bricks wall = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_3 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        0 ≤ r.val ∧ r.val ≤ (wall.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          0 ≤ r.val ∧ r.val ≤ (wall.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r >= s, where s = #{ i | 0 <= i < n and len(wall[i]) = 1 }.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_4 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        (countSingleton wall : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          (countSingleton wall : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = n iff for every i with 0 <= i < n, len(wall[i]) = 1.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_5 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        (r.val = (wall.val.length : ℤ) ↔ ∀ row ∈ wall.val, row.val.length = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          (r.val = (wall.val.length : ℤ) ↔ ∀ row ∈ wall.val, row.val.length = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 iff there exists an integer c with 1 <= c <= W-1 such that for every i with 0 <= i < n there exists j with 1 <= j < len(wall[i]) and sum_{k=0}^{j-1} wall[i][k] = c.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_6 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        (r.val = 0 ↔ ∃ c : ℤ, 1 ≤ c ∧ c ≤ W - 1 ∧ ∀ row ∈ wall.val, IsBoundary row c) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          (r.val = 0 ↔ ∃ c : ℤ, 1 ≤ c ∧ c ≤ W - 1 ∧ ∀ row ∈ wall.val, IsBoundary row c)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 1 <= c <= W-1, r <= n - cnt(c), where cnt(c) = #{ i | 0 <= i < n and there exists j with 1 <= j < len(wall[i]) and sum_{k=0}^{j-1} wall[i][k] = c }.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_7 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        ∀ c : ℤ, 1 ≤ c → c ≤ W - 1 →
          r.val ≤ (wall.val.length : ℤ) - (cnt wall c : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          ∀ c : ℤ, 1 ≤ c → c ≤ W - 1 →
            r.val ≤ (wall.val.length : ℤ) - (cnt wall c : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if W = 1 then r = n; if W >= 2 then there exists an integer c with 1 <= c <= W-1 such that cnt(c) = n - r, where cnt(c) = #{ i | 0 <= i < n and there exists j with 1 <= j < len(wall[i]) and sum_{k=0}^{j-1} wall[i][k] = c }.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_8 (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W) :
      ∀ r : Std.I64, least_bricks wall = ok r →
        (W = 1 → r.val = (wall.val.length : ℤ)) ∧
          (2 ≤ W → ∃ c : ℤ, 1 ≤ c ∧ c ≤ W - 1 ∧
            (cnt wall c : ℤ) = (wall.val.length : ℤ) - r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (wall : Wall) (W : ℤ) (hpre : WallPre wall 10000 20000 W), ∀ r : Std.I64, least_bricks wall = ok r →
          (W = 1 → r.val = (wall.val.length : ℤ)) ∧
            (2 ≤ W → ∃ c : ℤ, 1 ≤ c ∧ c ≤ W - 1 ∧
              (cnt wall c : ℤ) = (wall.val.length : ℤ) - r.val)) := by
    sorry

  /-- Let wall' be any slice of vectors satisfying the preconditions that is a permutation of the rows of wall, i.e. there is a bijection pi on {0,...,n-1} such that wall'[i] = wall[pi(i)] for every i with 0 <= i < n. If least_bricks wall returns r and least_bricks wall' returns r', then r = r'.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_9 (wall wall' : Wall) (W : ℤ)
      (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W)
      (hperm : wall.val.Perm wall'.val) :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (wall wall' : Wall) (W : ℤ)
        (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W)
        (hperm : wall.val.Perm wall'.val), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let wall' be the wall with the same shape as wall and with each row reversed: wall'[i][j] = wall[i][len(wall[i])-1-j] for every i with 0 <= i < n and every j with 0 <= j < len(wall[i]). Assume wall' satisfies the preconditions. If least_bricks wall returns r and least_bricks wall' returns r', then r = r'.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_10 (wall wall' : Wall) (W : ℤ)
      (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W)
      (hrev : RowsRel (fun w w' => w'.val = w.val.reverse) wall wall') :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (wall wall' : Wall) (W : ℤ)
        (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W)
        (hrev : RowsRel (fun w w' => w'.val = w.val.reverse) wall wall'), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let k >= 1 be an integer and let wall' be defined by wall'[i][j] = k * wall[i][j] for every i with 0 <= i < n and every j with 0 <= j < len(wall[i]). Assume wall' satisfies the preconditions (in particular every entry is positive and within the i64 and problem bounds). If least_bricks wall returns r and least_bricks wall' returns r', then r = r'.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_11 (wall wall' : Wall) (W k : ℤ)
      (hk : 1 ≤ k)
      (hpre : WallPre wall 10000 20000 W)
      (hpre' : WallPre wall' 10000 20000 (k * W))
      (hscale : RowsRel (fun w w' =>
        List.Forall₂ (fun x x' => x'.val = k * x.val) w.val w'.val) wall wall') :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (wall wall' : Wall) (W k : ℤ)
        (hk : 1 ≤ k)
        (hpre : WallPre wall 10000 20000 W)
        (hpre' : WallPre wall' 10000 20000 (k * W))
        (hscale : RowsRel (fun w w' =>
          List.Forall₂ (fun x x' => x'.val = k * x.val) w.val w'.val) wall wall'), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let wall' be any slice of vectors satisfying the preconditions with the same number of rows n. Suppose that for every i with 0 <= i < n and every integer c, there exists j with 1 <= j < len(wall[i]) and sum_{k=0}^{j-1} wall[i][k] = c if and only if there exists j' with 1 <= j' < len(wall'[i]) and sum_{k=0}^{j'-1} wall'[i][k] = c. If least_bricks wall returns r and least_bricks wall' returns r', then r = r'.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 10000; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 20000; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W. -/
  theorem spec_12 (wall wall' : Wall) (W W' : ℤ)
      (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W')
      (hlen : wall'.val.length = wall.val.length)
      (hbound : RowsRel (fun w w' => ∀ c : ℤ, IsBoundary w c ↔ IsBoundary w' c) wall wall') :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (wall wall' : Wall) (W W' : ℤ)
        (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W')
        (hlen : wall'.val.length = wall.val.length)
        (hbound : RowsRel (fun w w' => ∀ c : ℤ, IsBoundary w c ↔ IsBoundary w' c) wall wall'), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let wall' be obtained from wall by appending one new row consisting of the single brick [W]. Then wall' satisfies the preconditions (n+1 rows, total length +1 <= 20000, common row sum W, all entries within bounds). If least_bricks wall returns r and least_bricks wall' returns r', then r' = r + 1.
    Preconditions: Let n = len(wall). Assume: 1 <= n <= 9999; for every i with 0 <= i < n, 1 <= len(wall[i]) <= 10000; sum_{i=0}^{n-1} len(wall[i]) <= 19999; for every i,j with 0 <= i < n and 0 <= j < len(wall[i]), 1 <= wall[i][j] <= 2^31-1; and all row sums are equal, i.e. there exists an integer W such that for every i with 0 <= i < n, sum_{j=0}^{len(wall[i])-1} wall[i][j] = W; additionally W <= 2^31-1. -/
  theorem spec_13 (wall wall' : Wall) (W : ℤ)
      (hpre : WallPre wall 9999 19999 W) (hW : W ≤ 2 ^ 31 - 1)
      (hpre' : WallPre wall' 10000 20000 W)
      (happ : ∃ last : alloc.vec.Vec Std.I64, wall'.val = wall.val ++ [last] ∧
        ∃ x : Std.I64, last.val = [x] ∧ x.val = W) :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r'.val = r.val + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (wall wall' : Wall) (W : ℤ)
        (hpre : WallPre wall 9999 19999 W) (hW : W ≤ 2 ^ 31 - 1)
        (hpre' : WallPre wall' 10000 20000 W)
        (happ : ∃ last : alloc.vec.Vec Std.I64, wall'.val = wall.val ++ [last] ∧
          ∃ x : Std.I64, last.val = [x] ∧ x.val = W), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r'.val = r.val + 1) := by
    sorry

  /-- If least_bricks wall returns r and least_bricks wall' returns r', then r' = r or r' = r + 1 (equivalently r <= r' <= r + 1).
    Preconditions: Let n = len(wall). Assume the usual preconditions for wall with common row sum W. Let R be a slice of positive integers with 1 <= len(R) <= 10000 and sum_{j=0}^{len(R)-1} R[j] = W. Let wall' be the (n+1)-row wall obtained by appending R to wall. Assume wall' satisfies the usual preconditions (n+1 <= 10000, sum_i len(wall[i]) + len(R) <= 20000, and every entry of R is <= 2^31-1). -/
  theorem spec_14 (wall wall' : Wall) (W : ℤ) (R : List Std.I64)
      (hpre : WallPre wall 10000 20000 W)
      (hRne : 1 ≤ R.length) (hRle : R.length ≤ 10000) (hRsum : rowSum R = W)
      (hRpos : ∀ x ∈ R, 1 ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
      (hpre' : WallPre wall' 10000 20000 W)
      (happ : ∃ row : alloc.vec.Vec Std.I64, wall'.val = wall.val ++ [row] ∧ row.val = R) :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (wall wall' : Wall) (W : ℤ) (R : List Std.I64)
        (hpre : WallPre wall 10000 20000 W)
        (hRne : 1 ≤ R.length) (hRle : R.length ≤ 10000) (hRsum : rowSum R = W)
        (hRpos : ∀ x ∈ R, 1 ≤ x.val ∧ x.val ≤ 2 ^ 31 - 1)
        (hpre' : WallPre wall' 10000 20000 W)
        (happ : ∃ row : alloc.vec.Vec Std.I64, wall'.val = wall.val ++ [row] ∧ row.val = R), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
    sorry

  /-- If least_bricks wall returns r and least_bricks wall' returns r', then r' <= r.
    Preconditions: Let n = len(wall). Assume the usual preconditions for wall with common row sum W. Let wall' be another wall satisfying the usual preconditions with the same number of rows n and the same common row sum W. Suppose for every i with 0 <= i < n and every integer c, if c is an internal boundary in row i of wall, then c is an internal boundary in row i of wall'. -/
  theorem spec_15 (wall wall' : Wall) (W W' : ℤ)
      (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W')
      (hlen : wall'.val.length = wall.val.length)
      (hmono : RowsRel (fun w w' => ∀ c : ℤ, IsBoundary w c → IsBoundary w' c) wall wall') :
      ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
        r'.val ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (wall wall' : Wall) (W W' : ℤ)
        (hpre : WallPre wall 10000 20000 W) (hpre' : WallPre wall' 10000 20000 W')
        (hlen : wall'.val.length = wall.val.length)
        (hmono : RowsRel (fun w w' => ∀ c : ℤ, IsBoundary w c → IsBoundary w' c) wall wall'), ∀ r r' : Std.I64, least_bricks wall = ok r → least_bricks wall' = ok r' →
          r'.val ≤ r.val) := by
    sorry

  end AegisSpec.LeastBricks
