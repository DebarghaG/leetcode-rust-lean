import Aegis.ResultGrid.Code.Funs

/-!
# Specifications of `Aegis.ResultGrid.result_grid`

LeetCode problem `find-the-grid-of-region-average`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result
open Aegis.ResultGrid

namespace AegisSpec.ResultGrid

def matOf (rows : List (alloc.vec.Vec I64)) : List (List Int) :=
  rows.map (fun row => row.val.map (fun x => x.val))

def imgMat (image : Slice (alloc.vec.Vec I64)) : List (List Int) := matOf image.val

def resMat (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List (List Int) := matOf r.val

def rowOf (M : List (List Int)) (i : Nat) : List Int := M.getD i []

def px (M : List (List Int)) (i j : Nat) : Int := (rowOf M i).getD j 0

def winSum (M : List (List Int)) (a b : Nat) : Int :=
  ((List.range 3).map (fun r => ((List.range 3).map (fun c => px M (a + r) (b + c))).sum)).sum

def winAvg (M : List (List Int)) (a b : Nat) : Int := winSum M a b / 9

def winOKB (M : List (List Int)) (t : Int) (a b : Nat) : Bool :=
  (List.range 3).all (fun r =>
    (List.range 3).all (fun c =>
      let p := px M (a + r) (b + c)
      (if r + 1 < 3 then decide (|px M (a + r + 1) (b + c) - p| ≤ t) else true) &&
        (if c + 1 < 3 then decide (|px M (a + r) (b + c + 1) - p| ≤ t) else true)))

def ValidWin (M : List (List Int)) (t : Int) (a b : Nat) : Prop := winOKB M t a b = true

abbrev covers (a b i j : Nat) : Prop := a ≤ i ∧ i ≤ a + 2 ∧ b ≤ j ∧ j ≤ b + 2

def Rset (M : List (List Int)) (t : Int) (m n i j : Nat) : List (Nat × Nat) :=
  ((List.range (m - 2)).product (List.range (n - 2))).filter
    (fun p => winOKB M t p.1 p.2 && decide (covers p.1 p.2 i j))

def Rvals (M : List (List Int)) (t : Int) (m n i j : Nat) : List Int :=
  (Rset M t m n i j).map (fun p => winAvg M p.1 p.2)

def listMin? : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => min a b) x)

def listMax? : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => max a b) x)

def Rlo (M : List (List Int)) (t : Int) (m n i j : Nat) : Option Int :=
  listMin? (Rvals M t m n i j)

def Rhi (M : List (List Int)) (t : Int) (m n i j : Nat) : Option Int :=
  listMax? (Rvals M t m n i j)

def constOKB (M : List (List Int)) (a b : Nat) : Bool :=
  (List.range 3).all (fun r => (List.range 3).all (fun c => px M (a + r) (b + c) == px M a b))

def ConstWin (M : List (List Int)) (a b : Nat) : Prop := constOKB M a b = true

def C0set (M : List (List Int)) (m n i j : Nat) : List (Nat × Nat) :=
  ((List.range (m - 2)).product (List.range (n - 2))).filter
    (fun p => constOKB M p.1 p.2 && decide (covers p.1 p.2 i j))

def C0vals (M : List (List Int)) (m n i j : Nat) : List Int :=
  (C0set M m n i j).map (fun p => px M p.1 p.2)

/-- The function returns a result r and both of the following hold: (1) len(r) = m and for every 0 <= i < m, len(r[i]) = n. (2) For every 0 <= i < m and 0 <= j < n, if R(i,j) is empty then r[i][j] = image[i][j]; if R(i,j) is nonempty and k = |R(i,j)|, then r[i][j] = floor( (sum_{(a,b) in R(i,j)} A(a,b)) / k ).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. For a pixel (i,j), let R(i,j) be the set of pairs (a,b) such that S(a,b) is valid and a <= i <= a+2 and b <= j <= b+2. For a valid S(a,b), let A(a,b) = floor( (sum_{u=a}^{a+2} sum_{v=b}^{b+2} image[u][v]) / 9 ). -/
theorem spec_1 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → (rowOf (resMat r) i).length = n) ∧
        (∀ i j, i < m → j < n →
          (Rset (imgMat image) threshold.val m n i j = [] →
              px (resMat r) i j = px (imgMat image) i j) ∧
            (Rset (imgMat image) threshold.val m n i j ≠ [] →
              px (resMat r) i j =
                (Rvals (imgMat image) threshold.val m n i j).sum /
                  ((Rset (imgMat image) threshold.val m n i j).length : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → (rowOf (resMat r) i).length = n) ∧
        (∀ i j, i < m → j < n →
          (Rset (imgMat image) threshold.val m n i j = [] →
              px (resMat r) i j = px (imgMat image) i j) ∧
            (Rset (imgMat image) threshold.val m n i j ≠ [] →
              px (resMat r) i j =
                (Rvals (imgMat image) threshold.val m n i j).sum /
                  ((Rset (imgMat image) threshold.val m n i j).length : Int)))) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. -/
theorem spec_2 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), result_grid image threshold = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), result_grid image threshold = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m and for every 0 <= i < m, len(r[i]) = n.
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. -/
theorem spec_3 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        r.val.length = m ∧ ∀ i, i < m → (rowOf (resMat r) i).length = n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        r.val.length = m ∧ ∀ i, i < m → (rowOf (resMat r) i).length = n) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, 0 <= r[i][j] <= 255.
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. -/
theorem spec_4 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → 0 ≤ px (resMat r) i j ∧ px (resMat r) i j ≤ 255 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → 0 ≤ px (resMat r) i j ∧ px (resMat r) i j ≤ 255) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, if R(i,j) is empty then r[i][j] = image[i][j].
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. For a pixel (i,j), let R(i,j) be the set of pairs (a,b) such that S(a,b) is valid and a <= i <= a+2 and b <= j <= b+2. -/
theorem spec_5 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          Rset (imgMat image) threshold.val m n i j = [] →
            px (resMat r) i j = px (imgMat image) i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          Rset (imgMat image) threshold.val m n i j = [] →
            px (resMat r) i j = px (imgMat image) i j) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, if R(i,j) has exactly one element (a,b), then r[i][j] = A(a,b).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. For a pixel (i,j), let R(i,j) be the set of pairs (a,b) such that S(a,b) is valid and a <= i <= a+2 and b <= j <= b+2. For a valid S(a,b), let A(a,b) = floor( (sum_{u=a}^{a+2} sum_{v=b}^{b+2} image[u][v]) / 9 ). -/
theorem spec_6 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ (i j a b : Nat), i < m → j < n →
          Rset (imgMat image) threshold.val m n i j = [(a, b)] →
            px (resMat r) i j = winAvg (imgMat image) a b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ (i j a b : Nat), i < m → j < n →
          Rset (imgMat image) threshold.val m n i j = [(a, b)] →
            px (resMat r) i j = winAvg (imgMat image) a b) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, if k = |R(i,j)| >= 2, then r[i][j] = floor( (sum_{(a,b) in R(i,j)} A(a,b)) / k ).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. For a pixel (i,j), let R(i,j) be the set of pairs (a,b) such that S(a,b) is valid and a <= i <= a+2 and b <= j <= b+2. For a valid S(a,b), let A(a,b) = floor( (sum_{u=a}^{a+2} sum_{v=b}^{b+2} image[u][v]) / 9 ). -/
theorem spec_7 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ (i j k : Nat), i < m → j < n →
          (Rset (imgMat image) threshold.val m n i j).length = k → 2 ≤ k →
            px (resMat r) i j =
              (Rvals (imgMat image) threshold.val m n i j).sum / (k : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ (i j k : Nat), i < m → j < n →
          (Rset (imgMat image) threshold.val m n i j).length = k → 2 ≤ k →
            px (resMat r) i j =
              (Rvals (imgMat image) threshold.val m n i j).sum / (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n with R(i,j) nonempty, let lo(i,j) = min{A(a,b) | (a,b) in R(i,j)} and hi(i,j) = max{A(a,b) | (a,b) in R(i,j)}. Then lo(i,j) <= r[i][j] <= hi(i,j).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. For a pixel (i,j), let R(i,j) be the set of pairs (a,b) such that S(a,b) is valid and a <= i <= a+2 and b <= j <= b+2. For a valid S(a,b), let A(a,b) = floor( (sum_{u=a}^{a+2} sum_{v=b}^{b+2} image[u][v]) / 9 ). -/
theorem spec_8 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → Rset (imgMat image) threshold.val m n i j ≠ [] →
          ∀ lo hi : Int,
            Rlo (imgMat image) threshold.val m n i j = some lo →
              Rhi (imgMat image) threshold.val m n i j = some hi →
                lo ≤ px (resMat r) i j ∧ px (resMat r) i j ≤ hi := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → Rset (imgMat image) threshold.val m n i j ≠ [] →
          ∀ lo hi : Int,
            Rlo (imgMat image) threshold.val m n i j = some lo →
              Rhi (imgMat image) threshold.val m n i j = some hi →
                lo ≤ px (resMat r) i j ∧ px (resMat r) i j ≤ hi) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = image[i][j].
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. For 0 <= a <= m-3 and 0 <= b <= n-3, let S(a,b) be the 3 by 3 subgrid consisting of pixels (i,j) with a <= i <= a+2 and b <= j <= b+2. Call S(a,b) valid when for every two pixels (x,y) and (u,v) in S(a,b) with |x-u| + |y-v| = 1, we have |image[x][y] - image[u][v]| <= threshold. Assume additionally that for every 0 <= a <= m-3 and 0 <= b <= n-3, S(a,b) is not valid (equivalently, no valid 3 by 3 subgrid exists). -/
theorem spec_9 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hnov : ∀ a b, a < m - 2 → b < n - 2 → ¬ ValidWin (imgMat image) threshold.val a b) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (imgMat image) i j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hnov : ∀ a b, a < m - 2 → b < n - 2 → ¬ ValidWin (imgMat image) threshold.val a b), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (imgMat image) i j) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = v.
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. Assume there is an integer v with 0 <= v <= 255 such that image[i][j] = v for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (v : Int) (hv0 : 0 ≤ v) (hv255 : v ≤ 255)
    (hconst : ∀ i j, i < m → j < n → px (imgMat image) i j = v) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (v : Int) (hv0 : 0 ≤ v) (hv255 : v ≤ 255)
    (hconst : ∀ i j, i < m → j < n → px (imgMat image) i j = v), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = v) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = r[i][n-1-j].
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. Assume image[i][j] = image[i][n-1-j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) i (n - 1 - j)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (resMat r) i (n - 1 - j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) i (n - 1 - j)), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (resMat r) i (n - 1 - j)) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = r[m-1-i][j].
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. Assume image[i][j] = image[m-1-i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) (m - 1 - i) j) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (resMat r) (m - 1 - i) j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) (m - 1 - i) j), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n → px (resMat r) i j = px (resMat r) (m - 1 - i) j) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < n and 0 <= j < n, r[i][j] = r[j][i].
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 255. Assume m = n and image[i][j] = image[j][i] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hmn : m = n)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) j i) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < n → j < n → px (resMat r) i j = px (resMat r) j i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht0 : 0 ≤ threshold.val) (ht255 : threshold.val ≤ 255)
    (hmn : m = n)
    (hsym : ∀ i j, i < m → j < n → px (imgMat image) i j = px (imgMat image) j i), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < n → j < n → px (resMat r) i j = px (resMat r) j i) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, let C(i,j) be the set of all pairs (a,b) with 0 <= a <= m-3, 0 <= b <= n-3, a <= i <= a+2, and b <= j <= b+2. Then C(i,j) is nonempty and r[i][j] = floor( (sum_{(a,b) in C(i,j)} floor( (sum_{u=a}^{a+2} sum_{v=b}^{b+2} image[u][v]) / 9 )) / |C(i,j)| ).
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and threshold = 255. -/
theorem spec_14 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht : threshold.val = 255) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          Rset (imgMat image) 255 m n i j ≠ [] ∧
            px (resMat r) i j =
              (Rvals (imgMat image) 255 m n i j).sum /
                ((Rset (imgMat image) 255 m n i j).length : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht : threshold.val = 255), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          Rset (imgMat image) 255 m n i j ≠ [] ∧
            px (resMat r) i j =
              (Rvals (imgMat image) 255 m n i j).sum /
                ((Rset (imgMat image) 255 m n i j).length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, let C0(i,j) be the set of pairs (a,b) with 0 <= a <= m-3, 0 <= b <= n-3, a <= i <= a+2, b <= j <= b+2, and image[x][y] is the same for all x in [a,a+2] and y in [b,b+2]. If C0(i,j) is empty then r[i][j] = image[i][j]; otherwise r[i][j] = floor( (sum_{(a,b) in C0(i,j)} v(a,b)) / |C0(i,j)| ), where v(a,b) is that common value.
  Preconditions: Let m = len(image) and n = len(image[0]). Assume len(image) = m with 3 <= m <= 500, every row of image has length n with 3 <= n <= 500, every entry satisfies 0 <= image[i][j] <= 255 for 0 <= i < m and 0 <= j < n, and threshold = 0. -/
theorem spec_15 (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht : threshold.val = 0) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          (C0set (imgMat image) m n i j = [] → px (resMat r) i j = px (imgMat image) i j) ∧
            (C0set (imgMat image) m n i j ≠ [] →
              px (resMat r) i j =
                (C0vals (imgMat image) m n i j).sum /
                  ((C0set (imgMat image) m n i j).length : Int)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (image : Slice (alloc.vec.Vec I64)) (threshold : I64) (m n : Nat)
    (hm : image.val.length = m) (hm3 : 3 ≤ m) (hm500 : m ≤ 500)
    (hn : ∀ i, i < m → (rowOf (imgMat image) i).length = n) (hn3 : 3 ≤ n) (hn500 : n ≤ 500)
    (he : ∀ i j, i < m → j < n → 0 ≤ px (imgMat image) i j ∧ px (imgMat image) i j ≤ 255)
    (ht : threshold.val = 0), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
      result_grid image threshold = ok r →
        ∀ i j, i < m → j < n →
          (C0set (imgMat image) m n i j = [] → px (resMat r) i j = px (imgMat image) i j) ∧
            (C0set (imgMat image) m n i j ≠ [] →
              px (resMat r) i j =
                (C0vals (imgMat image) m n i j).sum /
                  ((C0set (imgMat image) m n i j).length : Int))) := by
  sorry

end AegisSpec.ResultGrid
