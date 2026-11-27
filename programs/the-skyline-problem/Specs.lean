import Aegis.GetSkyline.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.GetSkyline.get_skyline`

LeetCode problem `the-skyline-problem`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.GetSkyline

  def coords (b : alloc.vec.Vec Std.I64) : List ℤ := b.val.map (fun x => x.val)

  def entry (b : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ := (coords b).getD k 0

  def bldAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : alloc.vec.Vec Std.I64 :=
    buildings.val.getD i default

  def leftAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := entry (bldAt buildings i) 0

  def rightAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := entry (bldAt buildings i) 1

  def heightAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := entry (bldAt buildings i) 2

  def outAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : ℕ) : alloc.vec.Vec Std.I64 :=
    r.val.getD j default

  def xAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := entry (outAt r j) 0

  def yAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := entry (outAt r j) 1

  def minLeft (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    match buildings.val.map (fun b => entry b 0) with
    | [] => 0
    | x :: xs => xs.foldl min x

  def maxRight (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    match buildings.val.map (fun b => entry b 1) with
    | [] => 0
    | x :: xs => xs.foldl max x

  def maxHeight (buildings : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (buildings.val.map fun b => entry b 2).foldr max 0

  def maxHeightAtLeft (buildings : Slice (alloc.vec.Vec Std.I64)) (l : ℤ) : ℤ :=
    ((buildings.val.filter fun b => entry b 0 = l).map fun b => entry b 2).foldr max 0

  noncomputable def H (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℝ) : ℤ :=
    (buildings.val.filterMap fun b =>
        if (entry b 0 : ℝ) ≤ x ∧ x < (entry b 1 : ℝ) then some (entry b 2) else none).foldr max 0

  noncomputable def Hminus (buildings : Slice (alloc.vec.Vec Std.I64)) (x : ℝ) : ℤ :=
    (buildings.val.filterMap fun b =>
        if (entry b 0 : ℝ) < x ∧ x ≤ (entry b 1 : ℝ) then some (entry b 2) else none).foldr max 0

  def WellFormed (buildings : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ buildings.val.length ∧
    buildings.val.length ≤ 10 ^ 4 ∧
    (∀ i : ℕ, i < buildings.val.length → (bldAt buildings i).val.length = 3) ∧
    (∀ i : ℕ, i < buildings.val.length →
      0 ≤ leftAt buildings i ∧ leftAt buildings i < rightAt buildings i ∧
        rightAt buildings i ≤ (2 : ℤ) ^ 31 - 1 ∧ 1 ≤ heightAt buildings i ∧
        heightAt buildings i ≤ (2 : ℤ) ^ 31 - 1) ∧
    (∀ i : ℕ, i + 1 < buildings.val.length → leftAt buildings i ≤ leftAt buildings (i + 1))

  def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => Aeneas.Data.ListN.ListN.nil
    | a :: tl => Aeneas.Data.ListN.ListN.cons a (listNOfList tl)

  def sliceOfList {α : Type} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
    ⟨l.length, listNOfList l, h⟩

  def eraseAt (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) :
      Slice (alloc.vec.Vec Std.I64) :=
    sliceOfList (buildings.val.eraseIdx i) (by
      refine le_trans (List.length_eraseIdx_le buildings.val i) ?_
      have hb : buildings.val.length ≤ Usize.max := by
        simp only [Slice.val, Aeneas.Data.ListN.ListN_length]
        exact buildings.bound
      exact hb)

  theorem listNOfList_toList {α : Type} : ∀ l : List α, (listNOfList l).toList = l
    | [] => rfl
    | a :: tl => by
        show a :: (listNOfList tl).toList = a :: tl
        rw [listNOfList_toList tl]

  theorem eraseAt_val (buildings : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) :
      (eraseAt buildings i).val = buildings.val.eraseIdx i := by
    show (listNOfList (buildings.val.eraseIdx i)).toList = buildings.val.eraseIdx i
    rw [listNOfList_toList]

  /-- The function returns a result r (a vector of vectors of i64) and r satisfies the following. Let L = min_{0 <= i < len(buildings)} left_i and R = max_{0 <= i < len(buildings)} right_i. For real x, define H(x) = max({0} ∪ {height_i | 0 <= i < len(buildings) and left_i <= x < right_i}). Let m = len(r). Then: (a) m >= 2; (b) for every j with 0 <= j < m, len(r[j]) = 2; (c) writing x_j = r[j][0] and y_j = r[j][1], we have x_0 = L; (d) x_{m-1} = R and y_{m-1} = 0; (e) for every j with 0 <= j < m-1, x_j < x_{j+1}; (f) for every j with 0 <= j < m, y_j = H(x_j); (g) for every j with 0 <= j < m-1 and every real x with x_j <= x < x_{j+1}, H(x) = y_j; (h) for every j with 0 <= j < m-1, y_j != y_{j+1}.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_1 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r ∧
          2 ≤ r.val.length ∧
          (∀ j : ℕ, j < r.val.length → (outAt r j).val.length = 2) ∧
          xAt r 0 = minLeft buildings ∧
          xAt r (r.val.length - 1) = maxRight buildings ∧
          yAt r (r.val.length - 1) = 0 ∧
          (∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1)) ∧
          (∀ j : ℕ, j < r.val.length →
            yAt r j = H buildings ((xAt r j : ℝ))) ∧
          (∀ (j : ℕ), j + 1 < r.val.length →
            ∀ x : ℝ, (xAt r j : ℝ) ≤ x → x < (xAt r (j + 1) : ℝ) →
              H buildings x = yAt r j) ∧
          (∀ j : ℕ, j + 1 < r.val.length → yAt r j ≠ yAt r (j + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r ∧
            2 ≤ r.val.length ∧
            (∀ j : ℕ, j < r.val.length → (outAt r j).val.length = 2) ∧
            xAt r 0 = minLeft buildings ∧
            xAt r (r.val.length - 1) = maxRight buildings ∧
            yAt r (r.val.length - 1) = 0 ∧
            (∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1)) ∧
            (∀ j : ℕ, j < r.val.length →
              yAt r j = H buildings ((xAt r j : ℝ))) ∧
            (∀ (j : ℕ), j + 1 < r.val.length →
              ∀ x : ℝ, (xAt r j : ℝ) ≤ x → x < (xAt r (j + 1) : ℝ) →
                H buildings x = yAt r j) ∧
            (∀ j : ℕ, j + 1 < r.val.length → yAt r j ≠ yAt r (j + 1))) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_2 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j < r.val.length → (outAt r j).val.length = 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j < r.val.length → (outAt r j).val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r)-1, r[j][0] < r[j+1][0].
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_3 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1)) := by
    sorry

  /-- Whenever the function returns a result r, let L = min_{0 <= i < len(buildings)} left_i. Then len(r) > 0, r[0][0] = L, and r[0][1] = max({height_i | 0 <= i < len(buildings) and left_i = L}).
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_4 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          0 < r.val.length ∧
            xAt r 0 = minLeft buildings ∧
            yAt r 0 = maxHeightAtLeft buildings (minLeft buildings) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            0 < r.val.length ∧
              xAt r 0 = minLeft buildings ∧
              yAt r 0 = maxHeightAtLeft buildings (minLeft buildings)) := by
    sorry

  /-- Whenever the function returns a result r, let R = max_{0 <= i < len(buildings)} right_i. Then len(r) > 0, r[len(r)-1][0] = R, and r[len(r)-1][1] = 0.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_5 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          0 < r.val.length ∧
            xAt r (r.val.length - 1) = maxRight buildings ∧
            yAt r (r.val.length - 1) = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            0 < r.val.length ∧
              xAt r (r.val.length - 1) = maxRight buildings ∧
              yAt r (r.val.length - 1) = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), r[j][1] = H(r[j][0]), where H(x) = max({0} ∪ {height_i | 0 <= i < len(buildings) and left_i <= x < right_i}) for real x.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_6 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j < r.val.length → yAt r j = H buildings ((xAt r j : ℝ)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j < r.val.length → yAt r j = H buildings ((xAt r j : ℝ))) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r)-1 and every real x with r[j][0] <= x < r[j+1][0], H(x) = r[j][1], where H(x) = max({0} ∪ {height_i | 0 <= i < len(buildings) and left_i <= x < right_i}).
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_7 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ (j : ℕ), j + 1 < r.val.length →
            ∀ x : ℝ, (xAt r j : ℝ) ≤ x → x < (xAt r (j + 1) : ℝ) →
              H buildings x = yAt r j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ (j : ℕ), j + 1 < r.val.length →
              ∀ x : ℝ, (xAt r j : ℝ) ≤ x → x < (xAt r (j + 1) : ℝ) →
                H buildings x = yAt r j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r)-1, r[j][1] != r[j+1][1].
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_8 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j + 1 < r.val.length → yAt r j ≠ yAt r (j + 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j + 1 < r.val.length → yAt r j ≠ yAt r (j + 1)) := by
    sorry

  /-- Whenever the function returns a result r, let Hmax = max({0} ∪ {height_i | 0 <= i < len(buildings)}). Then for every j with 0 <= j < len(r), 0 <= r[j][1] <= Hmax.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_9 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j < r.val.length → 0 ≤ yAt r j ∧ yAt r j ≤ maxHeight buildings := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j < r.val.length → 0 ≤ yAt r j ∧ yAt r j ≤ maxHeight buildings) := by
    sorry

  /-- Whenever the function returns a result r, let L = min_{0 <= i < len(buildings)} left_i and R = max_{0 <= i < len(buildings)} right_i. Then for every j with 0 <= j < len(r), L <= r[j][0] <= R.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_10 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ j : ℕ, j < r.val.length → minLeft buildings ≤ xAt r j ∧ xAt r j ≤ maxRight buildings := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ j : ℕ, j < r.val.length → minLeft buildings ≤ xAt r j ∧ xAt r j ≤ maxRight buildings) := by
    sorry

  /-- Whenever the function returns a result r, let L = min_i left_i and R = max_i right_i. For real x, define H(x) = max({0} ∪ {height_i | left_i <= x < right_i}) and H^-(x) = max({0} ∪ {height_i | left_i < x <= right_i}). Then for every real x with L < x < R, x is equal to r[j][0] for some j with 0 <= j < len(r) if and only if H(x) != H^-(x).
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_11 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ x : ℝ, (minLeft buildings : ℝ) < x → x < (maxRight buildings : ℝ) →
            ((∃ j : ℕ, j < r.val.length ∧ (xAt r j : ℝ) = x) ↔
              H buildings x ≠ Hminus buildings x) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ x : ℝ, (minLeft buildings : ℝ) < x → x < (maxRight buildings : ℝ) →
              ((∃ j : ℕ, j < r.val.length ∧ (xAt r j : ℝ) = x) ↔
                H buildings x ≠ Hminus buildings x)) := by
    sorry

  /-- For any index i with 0 <= i < len(buildings), if len(buildings) > 1 and there exists an index j with 0 <= j < len(buildings), j != i, such that left_j <= left_i, right_i <= right_j, and height_i <= height_j, then let buildings' be the slice obtained from buildings by deleting the element at index i. The result returned by get_skyline on buildings equals the result returned by get_skyline on buildings'.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_12 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings)
      (i : ℕ) (hi : i < buildings.val.length) (hn : 1 < buildings.val.length)
      (j : ℕ) (hj : j < buildings.val.length) (hji : j ≠ i)
      (hleft : leftAt buildings j ≤ leftAt buildings i)
      (hright : rightAt buildings i ≤ rightAt buildings j)
      (hheight : heightAt buildings i ≤ heightAt buildings j) :
      Aegis.GetSkyline.get_skyline buildings = Aegis.GetSkyline.get_skyline (eraseAt buildings i) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings)
        (i : ℕ) (hi : i < buildings.val.length) (hn : 1 < buildings.val.length)
        (j : ℕ) (hj : j < buildings.val.length) (hji : j ≠ i)
        (hleft : leftAt buildings j ≤ leftAt buildings i)
        (hright : rightAt buildings i ≤ rightAt buildings j)
        (hheight : heightAt buildings i ≤ heightAt buildings j), Aegis.GetSkyline.get_skyline buildings = Aegis.GetSkyline.get_skyline (eraseAt buildings i)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, panic, or out-of-bounds access).
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_13 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r) := by
    sorry

  /-- Whenever the function returns a result r, let L = min_i left_i, R = max_i right_i, and x_j = r[j][0] for 0 <= j < len(r). Then x_0 = L, x_{len(r)-1} = R, and the half-open intervals [x_j, x_{j+1}) for j = 0, 1, ..., len(r)-2 are pairwise disjoint and their union is exactly the real interval [L, R).
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_14 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          xAt r 0 = minLeft buildings ∧
            xAt r (r.val.length - 1) = maxRight buildings ∧
            (∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1)) ∧
            (∀ (j k : ℕ), j + 1 < r.val.length → k + 1 < r.val.length → j ≠ k →
              Disjoint (Set.Ico (xAt r j : ℝ) (xAt r (j + 1) : ℝ))
                (Set.Ico (xAt r k : ℝ) (xAt r (k + 1) : ℝ))) ∧
            (∀ x : ℝ, (minLeft buildings : ℝ) ≤ x → x < (maxRight buildings : ℝ) →
              ∃ j : ℕ, j + 1 < r.val.length ∧ (xAt r j : ℝ) ≤ x ∧ x < (xAt r (j + 1) : ℝ)) ∧
            (∀ x : ℝ,
              (∃ j : ℕ, j + 1 < r.val.length ∧ (xAt r j : ℝ) ≤ x ∧ x < (xAt r (j + 1) : ℝ)) →
                (minLeft buildings : ℝ) ≤ x ∧ x < (maxRight buildings : ℝ)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            xAt r 0 = minLeft buildings ∧
              xAt r (r.val.length - 1) = maxRight buildings ∧
              (∀ j : ℕ, j + 1 < r.val.length → xAt r j < xAt r (j + 1)) ∧
              (∀ (j k : ℕ), j + 1 < r.val.length → k + 1 < r.val.length → j ≠ k →
                Disjoint (Set.Ico (xAt r j : ℝ) (xAt r (j + 1) : ℝ))
                  (Set.Ico (xAt r k : ℝ) (xAt r (k + 1) : ℝ))) ∧
              (∀ x : ℝ, (minLeft buildings : ℝ) ≤ x → x < (maxRight buildings : ℝ) →
                ∃ j : ℕ, j + 1 < r.val.length ∧ (xAt r j : ℝ) ≤ x ∧ x < (xAt r (j + 1) : ℝ)) ∧
              (∀ x : ℝ,
                (∃ j : ℕ, j + 1 < r.val.length ∧ (xAt r j : ℝ) ≤ x ∧ x < (xAt r (j + 1) : ℝ)) →
                  (minLeft buildings : ℝ) ≤ x ∧ x < (maxRight buildings : ℝ))) := by
    sorry

  /-- Whenever the function returns a result r, let L = min_i left_i, R = max_i right_i, and H(x) = max({0} ∪ {height_i | left_i <= x < right_i}) for real x. For every real x with L < x < R such that H(x) = 0 and there exists epsilon > 0 with H(z) > 0 for all z in (x - epsilon, x), there exists an index j with 0 <= j < len(r) such that r[j][0] = x and r[j][1] = 0.
    Preconditions: buildings is a nonempty slice of vectors of i64 with len(buildings) >= 1 and len(buildings) <= 10^4. For every i with 0 <= i < len(buildings), buildings[i] has length 3; write left_i = buildings[i][0], right_i = buildings[i][1], height_i = buildings[i][2]. For every i, 0 <= left_i < right_i <= 2^31 - 1 and 1 <= height_i <= 2^31 - 1. The buildings are sorted by left coordinate in non-decreasing order: for every i with 0 <= i < len(buildings)-1, left_i <= left_{i+1}. -/
  theorem spec_15 (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.GetSkyline.get_skyline buildings = ok r →
          ∀ x : ℝ, (minLeft buildings : ℝ) < x → x < (maxRight buildings : ℝ) →
            H buildings x = 0 →
              (∃ eps : ℝ, 0 < eps ∧ ∀ z : ℝ, x - eps < z → z < x → 0 < H buildings z) →
                ∃ j : ℕ, j < r.val.length ∧ (xAt r j : ℝ) = x ∧ yAt r j = 0 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (buildings : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed buildings), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.GetSkyline.get_skyline buildings = ok r →
            ∀ x : ℝ, (minLeft buildings : ℝ) < x → x < (maxRight buildings : ℝ) →
              H buildings x = 0 →
                (∃ eps : ℝ, 0 < eps ∧ ∀ z : ℝ, x - eps < z → z < x → 0 < H buildings z) →
                  ∃ j : ℕ, j < r.val.length ∧ (xAt r j : ℝ) = x ∧ yAt r j = 0) := by
    sorry

  end AegisSpec.GetSkyline
