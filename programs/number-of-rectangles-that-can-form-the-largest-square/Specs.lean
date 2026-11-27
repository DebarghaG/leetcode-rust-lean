import Aegis.CountGoodRectangles.Code.Funs

/-!
# Specifications of `Aegis.CountGoodRectangles.count_good_rectangles`

LeetCode problem `number-of-rectangles-that-can-form-the-largest-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountGoodRectangles

  def rowsOf (rectangles : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    rectangles.val.map (fun row => row.val.map (fun x => x.val))

  def rowSide (row : List ℤ) : ℤ :=
    match row with
    | a :: b :: _ => min a b
    | _ => 0

  def sides (rs : List (List ℤ)) : List ℤ := rs.map rowSide

  def maxSide (rs : List (List ℤ)) : ℤ := (sides rs).foldr max 0

  def countSideEq (rs : List (List ℤ)) (m : ℤ) : ℕ :=
    (sides rs).countP (fun s => decide (s = m))

  def countSideMaximal (rs : List (List ℤ)) : ℕ :=
    (sides rs).countP (fun s => (sides rs).all (fun t => decide (t ≤ s)))

  def countBothGe (rs : List (List ℤ)) (m : ℤ) : ℕ :=
    rs.countP (fun row => row.all (fun x => decide (m ≤ x)))

  def snocRow (xs : List (List ℤ)) (a b : ℤ) : List (List ℤ) := xs ++ [[a, b]]

  def swapRows (rs : List (List ℤ)) : List (List ℤ) :=
    rs.map (fun row =>
      match row with
      | a :: b :: [] => [b, a]
      | r => r)

  def PermBy (xs ys : List (List ℤ)) : Prop :=
    ∃ m : ℕ, xs.length = m ∧ ys.length = m ∧
      ∃ π : ℕ → ℕ,
        (∀ i, i < m → π i < m) ∧
        (∀ i j, i < m → j < m → π i = π j → i = j) ∧
        (∀ k, k < m → ys[k]? = xs[π k]?)

  def WellFormed (rs : List (List ℤ)) : Prop :=
    1 ≤ rs.length ∧ rs.length ≤ 1000 ∧
      ∀ row ∈ rs, ∃ a b : ℤ,
        row = [a, b] ∧ 1 ≤ a ∧ a ≤ 1000000000 ∧ 1 ≤ b ∧ b ≤ 1000000000

  /-- Whenever the function returns a result r, let side(i) = min(rectangles[i][0], rectangles[i][1]) for 0 <= i < n, and let M = max{side(j) | 0 <= j < n}. Then r = |{i | 0 <= i < n and side(i) = M}|; that is, r is exactly the number of rectangles whose shorter side equals the largest shorter side among all rectangles.
    Preconditions: Let n = len(rectangles). Assume 1 <= n <= 1000. For every i with 0 <= i < n, assume len(rectangles[i]) = 2 and, writing rectangles[i] = [a_i, b_i], assume 1 <= a_i <= 1000000000 and 1 <= b_i <= 1000000000. -/
  theorem spec_1 (rectangles : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles))
      (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r) :
      r.val = (countSideEq (rowsOf rectangles) (maxSide (rowsOf rectangles)) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles))
        (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r), r.val = (countSideEq (rowsOf rectangles) (maxSide (rowsOf rectangles)) : ℤ)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail by panic, out-of-bounds access, or machine-integer overflow.
    Preconditions: Let n = len(rectangles). Assume 1 <= n <= 1000. For every i with 0 <= i < n, assume len(rectangles[i]) = 2 and, writing rectangles[i] = [a_i, b_i], assume 1 <= a_i <= 1000000000 and 1 <= b_i <= 1000000000. -/
  theorem spec_2 (rectangles : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles)) :
      ∃ r : I64, Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles)), ∃ r : I64, Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n.
    Preconditions: Let n = len(rectangles). Assume 1 <= n <= 1000. For every i with 0 <= i < n, assume len(rectangles[i]) = 2 and, writing rectangles[i] = [a_i, b_i], assume 1 <= a_i <= 1000000000 and 1 <= b_i <= 1000000000. -/
  theorem spec_3 (rectangles : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles))
      (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r) :
      1 ≤ r.val ∧ r.val ≤ ((rowsOf rectangles).length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles))
        (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r), 1 ≤ r.val ∧ r.val ≤ ((rowsOf rectangles).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let side(i) = min(rectangles[i][0], rectangles[i][1]) for 0 <= i < n. Then r = |{i | 0 <= i < n and for every j with 0 <= j < n, side(i) >= side(j)}|.
    Preconditions: Let n = len(rectangles). Assume 1 <= n <= 1000. For every i with 0 <= i < n, assume len(rectangles[i]) = 2 and, writing rectangles[i] = [a_i, b_i], assume 1 <= a_i <= 1000000000 and 1 <= b_i <= 1000000000. -/
  theorem spec_4 (rectangles : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles))
      (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r) :
      r.val = (countSideMaximal (rowsOf rectangles) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles))
        (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r), r.val = (countSideMaximal (rowsOf rectangles) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let M = max{min(rectangles[j][0], rectangles[j][1]) | 0 <= j < n}. Then r = |{i | 0 <= i < n and rectangles[i][0] >= M and rectangles[i][1] >= M}|.
    Preconditions: Let n = len(rectangles). Assume 1 <= n <= 1000. For every i with 0 <= i < n, assume len(rectangles[i]) = 2 and, writing rectangles[i] = [a_i, b_i], assume 1 <= a_i <= 1000000000 and 1 <= b_i <= 1000000000. -/
  theorem spec_5 (rectangles : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles))
      (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r) :
      r.val = (countBothGe (rowsOf rectangles) (maxSide (rowsOf rectangles)) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles))
        (r : I64) (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r), r.val = (countBothGe (rowsOf rectangles) (maxSide (rowsOf rectangles)) : ℤ)) := by
    sorry

  /-- Suppose ys is a permutation of xs, meaning there is a bijection pi on {0,...,m-1} such that ys[k] = xs[pi(k)] for every k with 0 <= k < m. If the function returns r_x on xs and r_y on ys, then r_x = r_y.
    Preconditions: Let xs and ys be two inputs, each satisfying: len = m with 1 <= m <= 1000; every row has length 2; every entry is between 1 and 1000000000 inclusive. -/
  theorem spec_6 (xs ys : Slice (alloc.vec.Vec I64))
      (hwf_x : WellFormed (rowsOf xs))
      (hwf_y : WellFormed (rowsOf ys))
      (hperm : PermBy (rowsOf xs) (rowsOf ys))
      (r_x r_y : I64)
      (h_x : Aegis.CountGoodRectangles.count_good_rectangles xs = ok r_x)
      (h_y : Aegis.CountGoodRectangles.count_good_rectangles ys = ok r_y) :
      r_x.val = r_y.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (xs ys : Slice (alloc.vec.Vec I64))
        (hwf_x : WellFormed (rowsOf xs))
        (hwf_y : WellFormed (rowsOf ys))
        (hperm : PermBy (rowsOf xs) (rowsOf ys))
        (r_x r_y : I64)
        (h_x : Aegis.CountGoodRectangles.count_good_rectangles xs = ok r_x)
        (h_y : Aegis.CountGoodRectangles.count_good_rectangles ys = ok r_y), r_x.val = r_y.val) := by
    sorry

  /-- If the function returns r on rectangles and r' on rectangles', then r = r'.
    Preconditions: Let rectangles satisfy: n = len(rectangles) with 1 <= n <= 1000; every row has length 2; every entry is between 1 and 1000000000 inclusive. Let rectangles' be obtained by replacing each row [a,b] with [b,a]. -/
  theorem spec_7 (rectangles rectangles' : Slice (alloc.vec.Vec I64))
      (hwf : WellFormed (rowsOf rectangles))
      (hswap : rowsOf rectangles' = swapRows (rowsOf rectangles))
      (r r' : I64)
      (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r)
      (hr' : Aegis.CountGoodRectangles.count_good_rectangles rectangles' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec I64))
        (hwf : WellFormed (rowsOf rectangles))
        (hswap : rowsOf rectangles' = swapRows (rowsOf rectangles))
        (r r' : I64)
        (hr : Aegis.CountGoodRectangles.count_good_rectangles rectangles = ok r)
        (hr' : Aegis.CountGoodRectangles.count_good_rectangles rectangles' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let M = max{min(xs[j][0], xs[j][1]) | 0 <= j < m} and let s = min(a,b). If the function returns r_x on xs and r_y on ys, then: (1) if s < M then r_y = r_x; (2) if s = M then r_y = r_x + 1; (3) if s > M then r_y = 1.
    Preconditions: Let xs be an input satisfying: m = len(xs) with 1 <= m <= 999; every row has length 2; every entry is between 1 and 1000000000 inclusive. Let [a,b] be a row with 1 <= a <= 1000000000 and 1 <= b <= 1000000000, and let ys be xs followed by [a,b]. -/
  theorem spec_8 (xs ys : Slice (alloc.vec.Vec I64)) (a b : ℤ)
      (hwf : WellFormed (rowsOf xs))
      (hlen : (rowsOf xs).length ≤ 999)
      (ha : 1 ≤ a ∧ a ≤ 1000000000)
      (hb : 1 ≤ b ∧ b ≤ 1000000000)
      (hys : rowsOf ys = snocRow (rowsOf xs) a b)
      (r_x r_y : I64)
      (h_x : Aegis.CountGoodRectangles.count_good_rectangles xs = ok r_x)
      (h_y : Aegis.CountGoodRectangles.count_good_rectangles ys = ok r_y) :
      (min a b < maxSide (rowsOf xs) → r_y.val = r_x.val) ∧
      (min a b = maxSide (rowsOf xs) → r_y.val = r_x.val + 1) ∧
      (maxSide (rowsOf xs) < min a b → r_y.val = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (xs ys : Slice (alloc.vec.Vec I64)) (a b : ℤ)
        (hwf : WellFormed (rowsOf xs))
        (hlen : (rowsOf xs).length ≤ 999)
        (ha : 1 ≤ a ∧ a ≤ 1000000000)
        (hb : 1 ≤ b ∧ b ≤ 1000000000)
        (hys : rowsOf ys = snocRow (rowsOf xs) a b)
        (r_x r_y : I64)
        (h_x : Aegis.CountGoodRectangles.count_good_rectangles xs = ok r_x)
        (h_y : Aegis.CountGoodRectangles.count_good_rectangles ys = ok r_y), (min a b < maxSide (rowsOf xs) → r_y.val = r_x.val) ∧
        (min a b = maxSide (rowsOf xs) → r_y.val = r_x.val + 1) ∧
        (maxSide (rowsOf xs) < min a b → r_y.val = 1)) := by
    sorry

  end AegisSpec.CountGoodRectangles
