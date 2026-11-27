import Aegis.ShortestDistanceColor.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistanceColor.shortest_distance_color`

LeetCode problem `shortest-distance-to-target-color`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestDistanceColor

open Aegis.ShortestDistanceColor (shortest_distance_color)

def absDiff (a b : Int) : Int := ((b - a).natAbs : Int)

def colorAtInt (colors : Slice Std.I64) (j : Int) : Int :=
  ((colors.val[j.toNat]?).map (fun x => x.val)).getD 0

def colorAt (colors : Slice Std.I64) (j : Nat) : Int := colorAtInt colors (j : Int)

def queryAt (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : List Int :=
  ((queries.val[k]?).map (fun q => q.val.map (fun x => x.val))).getD []

def queryLen (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Nat :=
  (queryAt queries k).length

def queryIndex (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Int :=
  (queryAt queries k)[0]?.getD 0

def queryColor (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Int :=
  (queryAt queries k)[1]?.getD 0

def resultAt (r : alloc.vec.Vec Std.I64) (k : Nat) : Int :=
  ((r.val[k]?).map (fun x => x.val)).getD 0

def Occurs (colors : Slice Std.I64) (c : Int) : Prop :=
  ∃ j, j < colors.val.length ∧ colorAt colors j = c

def IsNearestDistance (colors : Slice Std.I64) (i c d : Int) : Prop :=
  (∃ j, j < colors.val.length ∧ colorAt colors j = c ∧ d = absDiff i (j : Int)) ∧
    ∀ j, j < colors.val.length → colorAt colors j = c → d ≤ absDiff i (j : Int)

/-- The function returns a result r and len(r) = len(queries). For every k with 0 <= k < len(queries), write i = queries[k][0] and c = queries[k][1]. If there exists j with 0 <= j < len(colors) and colors[j] = c, then r[k] is the minimum of |j - i| over all such j; otherwise r[k] = -1.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_1 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3) :
    ∃ r : alloc.vec.Vec Std.I64,
      shortest_distance_color colors queries = ok r ∧
        r.val.length = queries.val.length ∧
          ∀ k, k < queries.val.length →
            (Occurs colors (queryColor queries k) →
              IsNearestDistance colors (queryIndex queries k) (queryColor queries k)
                (resultAt r k)) ∧
            (¬ Occurs colors (queryColor queries k) → resultAt r k = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3), ∃ r : alloc.vec.Vec Std.I64,
      shortest_distance_color colors queries = ok r ∧
        r.val.length = queries.val.length ∧
          ∀ k, k < queries.val.length →
            (Occurs colors (queryColor queries k) →
              IsNearestDistance colors (queryIndex queries k) (queryColor queries k)
                (resultAt r k)) ∧
            (¬ Occurs colors (queryColor queries k) → resultAt r k = -1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or return an error.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_2 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3) :
    ∃ r : alloc.vec.Vec Std.I64, shortest_distance_color colors queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3), ∃ r : alloc.vec.Vec Std.I64, shortest_distance_color colors queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries).
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_3 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), r.val.length = queries.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), either r[k] = -1 or 0 <= r[k] <= len(colors) - 1.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_4 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length →
      resultAt r k = -1 ∨
        (0 ≤ resultAt r k ∧ resultAt r k ≤ ((colors.val.length - 1 : Nat) : Int)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length →
      resultAt r k = -1 ∨
        (0 ≤ resultAt r k ∧ resultAt r k ≤ ((colors.val.length - 1 : Nat) : Int))) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), write c = queries[k][1]. Then r[k] = -1 if and only if there is no j with 0 <= j < len(colors) and colors[j] = c.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_5 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length →
      (resultAt r k = -1 ↔ ¬ Occurs colors (queryColor queries k)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length →
      (resultAt r k = -1 ↔ ¬ Occurs colors (queryColor queries k))) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries) and r[k] >= 0, write i = queries[k][0] and c = queries[k][1]. Then there exists j with 0 <= j < len(colors), colors[j] = c, and r[k] = |j - i|.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_6 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      ∃ j, j < colors.val.length ∧ colorAt colors j = queryColor queries k ∧
        resultAt r k = absDiff (queryIndex queries k) (j : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      ∃ j, j < colors.val.length ∧ colorAt colors j = queryColor queries k ∧
        resultAt r k = absDiff (queryIndex queries k) (j : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries) and r[k] >= 0, write i = queries[k][0] and c = queries[k][1]. Then for every j with 0 <= j < len(colors) and colors[j] = c, r[k] <= |j - i|.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_7 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      ∀ j, j < colors.val.length → colorAt colors j = queryColor queries k →
        resultAt r k ≤ absDiff (queryIndex queries k) (j : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      ∀ j, j < colors.val.length → colorAt colors j = queryColor queries k →
        resultAt r k ≤ absDiff (queryIndex queries k) (j : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), write i = queries[k][0] and c = queries[k][1]. Then r[k] = 0 if and only if colors[i] = c.
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_8 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length →
      (resultAt r k = 0 ↔ colorAtInt colors (queryIndex queries k) = queryColor queries k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length →
      (resultAt r k = 0 ↔ colorAtInt colors (queryIndex queries k) = queryColor queries k)) := by
  sorry

/-- Whenever the function returns a result r, for every k and l with 0 <= k < len(queries) and 0 <= l < len(queries), if queries[k][0] = queries[l][0] and queries[k][1] = queries[l][1], then r[k] = r[l].
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_9 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k l, k < queries.val.length → l < queries.val.length →
      queryIndex queries k = queryIndex queries l →
        queryColor queries k = queryColor queries l →
          resultAt r k = resultAt r l := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k l, k < queries.val.length → l < queries.val.length →
      queryIndex queries k = queryIndex queries l →
        queryColor queries k = queryColor queries l →
          resultAt r k = resultAt r l) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(queries) and r[k] >= 0, write i = queries[k][0]. Then r[k] <= max(i, len(colors) - 1 - i).
  Preconditions: Let n = len(colors) and m = len(queries). Assume 1 <= n <= 50000 and 1 <= m <= 50000; for every j with 0 <= j < n, colors[j] is 1, 2, or 3; for every k with 0 <= k < m, len(queries[k]) = 2, 0 <= queries[k][0] < n, and 1 <= queries[k][1] <= 3. -/
theorem spec_10 (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r) :
    ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      resultAt r k ≤
        max (queryIndex queries k) ((colors.val.length : Int) - 1 - queryIndex queries k) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (colors : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_pos : 1 ≤ colors.val.length) (hn_le : colors.val.length ≤ 50000)
    (hm_pos : 1 ≤ queries.val.length) (hm_le : queries.val.length ≤ 50000)
    (hcolors : ∀ j, j < colors.val.length →
      colorAt colors j = 1 ∨ colorAt colors j = 2 ∨ colorAt colors j = 3)
    (hqueries : ∀ k, k < queries.val.length → queryLen queries k = 2 ∧
      0 ≤ queryIndex queries k ∧ queryIndex queries k < (colors.val.length : Int) ∧
      1 ≤ queryColor queries k ∧ queryColor queries k ≤ 3)
    (r : alloc.vec.Vec Std.I64) (hres : shortest_distance_color colors queries = ok r), ∀ k, k < queries.val.length → 0 ≤ resultAt r k →
      resultAt r k ≤
        max (queryIndex queries k) ((colors.val.length : Int) - 1 - queryIndex queries k)) := by
  sorry

end AegisSpec.ShortestDistanceColor
