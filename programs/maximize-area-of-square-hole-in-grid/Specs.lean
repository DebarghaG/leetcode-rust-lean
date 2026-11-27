import Aegis.MaximizeSquareHoleArea.Code.Funs

/-!
# Specifications of `Aegis.MaximizeSquareHoleArea.maximize_square_hole_area`

LeetCode problem `maximize-area-of-square-hole-in-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximizeSquareHoleArea

  open Aegis.MaximizeSquareHoleArea

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def Occurs (x : ℤ) (l : List ℤ) : Prop := x ∈ l

  def HasConsecBlock (l : List ℤ) (k : ℕ) : Prop :=
    ∃ a : ℤ, ∀ t : ℕ, t < k → a + (t : ℤ) ∈ l

  noncomputable def run (l : List ℤ) : ℕ :=
    max 1 (sSup {k : ℕ | HasConsecBlock l k})

  /-- Let run(h) be the largest k >= 1 such that there exists an integer a with a, a+1, ..., a+k-1 all occurring in h; if h is empty, set run(h)=1. The function returns a result r, and r = (1 + min(run(hBars), run(vBars)))^2.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_1
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup) :
      ∃ r : Std.I64,
        maximize_square_hole_area n m hBars vBars = ok r ∧
          r.val = ((min (run (vals hBars)) (run (vals vBars)) : ℤ) + 1) ^ 2 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup), ∃ r : Std.I64,
          maximize_square_hole_area n m hBars vBars = ok r ∧
            r.val = ((min (run (vals hBars)) (run (vals vBars)) : ℤ) + 1) ^ 2) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_2
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup) :
      ∃ r : Std.I64, maximize_square_hole_area n m hBars vBars = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup), ∃ r : Std.I64, maximize_square_hole_area n m hBars vBars = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 4 <= r <= (min(n+1, m+1))^2.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_3
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      4 ≤ r.val ∧ r.val ≤ (min (n.val + 1) (m.val + 1)) ^ 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), 4 ≤ r.val ∧ r.val ≤ (min (n.val + 1) (m.val + 1)) ^ 2) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer s with 2 <= s <= min(n+1, m+1) such that r = s*s; in particular, r is a perfect square.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_4
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      ∃ s : ℤ, 2 ≤ s ∧ s ≤ min (n.val + 1) (m.val + 1) ∧ r.val = s * s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), ∃ s : ℤ, 2 ≤ s ∧ s ≤ min (n.val + 1) (m.val + 1) ∧ r.val = s * s) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers s, i, j with s >= 2, 1 <= i <= n+2-s, 1 <= j <= m+2-s, and r = s*s, such that the set of horizontal bars {i+1, i+2, ..., i+s-1} is a subset of hBars and the set of vertical bars {j+1, j+2, ..., j+s-1} is a subset of vBars. Here unit cell row i is between horizontal bars i and i+1, and unit cell column j is between vertical bars j and j+1. Hence, after removing exactly those internal bars, the s by s block of unit cells in rows i through i+s-1 and columns j through j+s-1 is a square hole of area r.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_5
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      ∃ s i j : ℤ,
        2 ≤ s ∧ 1 ≤ i ∧ i ≤ n.val + 2 - s ∧ 1 ≤ j ∧ j ≤ m.val + 2 - s ∧
          r.val = s * s ∧
          (∀ t : ℤ, 1 ≤ t → t ≤ s - 1 → i + t ∈ vals hBars) ∧
          (∀ t : ℤ, 1 ≤ t → t ≤ s - 1 → j + t ∈ vals vBars) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), ∃ s i j : ℤ,
          2 ≤ s ∧ 1 ≤ i ∧ i ≤ n.val + 2 - s ∧ 1 ≤ j ∧ j ≤ m.val + 2 - s ∧
            r.val = s * s ∧
            (∀ t : ℤ, 1 ≤ t → t ≤ s - 1 → i + t ∈ vals hBars) ∧
            (∀ t : ℤ, 1 ≤ t → t ≤ s - 1 → j + t ∈ vals vBars)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer s with 2 <= s <= min(n+1, m+1) and s*s > r, and for every i with 1 <= i <= n+2-s and j with 1 <= j <= m+2-s, at least one of the horizontal bars i+1, i+2, ..., i+s-1 is not in hBars, or at least one of the vertical bars j+1, j+2, ..., j+s-1 is not in vBars. Equivalently, no square hole of side s (and hence area greater than r) can be formed by removing any allowed bars.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_6
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      ∀ s : ℤ, 2 ≤ s → s ≤ min (n.val + 1) (m.val + 1) → r.val < s * s →
        ∀ i j : ℤ, 1 ≤ i → i ≤ n.val + 2 - s → 1 ≤ j → j ≤ m.val + 2 - s →
          (∃ t : ℤ, 1 ≤ t ∧ t ≤ s - 1 ∧ i + t ∉ vals hBars) ∨
            (∃ t : ℤ, 1 ≤ t ∧ t ≤ s - 1 ∧ j + t ∉ vals vBars) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), ∀ s : ℤ, 2 ≤ s → s ≤ min (n.val + 1) (m.val + 1) → r.val < s * s →
          ∀ i j : ℤ, 1 ≤ i → i ≤ n.val + 2 - s → 1 ≤ j → j ≤ m.val + 2 - s →
            (∃ t : ℤ, 1 ≤ t ∧ t ≤ s - 1 ∧ i + t ∉ vals hBars) ∨
              (∃ t : ℤ, 1 ≤ t ∧ t ≤ s - 1 ∧ j + t ∉ vals vBars)) := by
    sorry

  /-- Whenever the function returns a result r, r = (1 + run(hBars))^2.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. Let run(h) be the largest k >= 1 such that some k consecutive integers all occur in h. Assume run(hBars) <= run(vBars). -/
  theorem spec_7
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (hrun : run (vals hBars) ≤ run (vals vBars))
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      r.val = ((run (vals hBars) : ℤ) + 1) ^ 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (hrun : run (vals hBars) ≤ run (vals vBars))
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), r.val = ((run (vals hBars) : ℤ) + 1) ^ 2) := by
    sorry

  /-- Whenever the function returns a result r, r = (1 + run(vBars))^2.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. Let run(h) be the largest k >= 1 such that some k consecutive integers all occur in h. Assume run(vBars) <= run(hBars). -/
  theorem spec_8
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (hrun : run (vals vBars) ≤ run (vals hBars))
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      r.val = ((run (vals vBars) : ℤ) + 1) ^ 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (hrun : run (vals vBars) ≤ run (vals hBars))
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), r.val = ((run (vals vBars) : ℤ) + 1) ^ 2) := by
    sorry

  /-- If the function returns r on input (n, m, hBars, vBars) and returns r' on input (n, m, hBars', vBars'), then r = r'.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct; hBars' is a permutation of hBars; vBars' is a permutation of vBars. -/
  theorem spec_9
      (n m : Std.I64) (hBars vBars hBars' vBars' : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (hBars'_perm : hBars'.val.Perm hBars.val)
      (vBars'_perm : vBars'.val.Perm vBars.val)
      (r r' : Std.I64)
      (hr : maximize_square_hole_area n m hBars vBars = ok r)
      (hr' : maximize_square_hole_area n m hBars' vBars' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars hBars' vBars' : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (hBars'_perm : hBars'.val.Perm hBars.val)
        (vBars'_perm : vBars'.val.Perm vBars.val)
        (r r' : Std.I64)
        (hr : maximize_square_hole_area n m hBars vBars = ok r)
        (hr' : maximize_square_hole_area n m hBars' vBars' = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on input (n, m, hBars, vBars) and returns r' on input (m, n, vBars, hBars), then r = r'.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct. -/
  theorem spec_10
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (r r' : Std.I64)
      (hr : maximize_square_hole_area n m hBars vBars = ok r)
      (hr' : maximize_square_hole_area m n vBars hBars = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (r r' : Std.I64)
        (hr : maximize_square_hole_area n m hBars vBars = ok r)
        (hr' : maximize_square_hole_area m n vBars hBars = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on input (n, m, hBars, vBars) and returns r' on input (n, m, hBars', vBars), then r' >= r.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct; hBars' is a slice of 64-bit integers with len(hBars') <= 100, all entries distinct and in [2, n+1], and every value occurring in hBars also occurs in hBars'. -/
  theorem spec_11
      (n m : Std.I64) (hBars vBars hBars' : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (hBars'_len : hBars'.val.length ≤ 100)
      (hBars'_bounds : ∀ x ∈ hBars'.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars'_distinct : hBars'.val.Nodup)
      (hBars'_subset : ∀ y : ℤ, Occurs y (vals hBars) → Occurs y (vals hBars'))
      (r r' : Std.I64)
      (hr : maximize_square_hole_area n m hBars vBars = ok r)
      (hr' : maximize_square_hole_area n m hBars' vBars = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars hBars' : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (hBars'_len : hBars'.val.length ≤ 100)
        (hBars'_bounds : ∀ x ∈ hBars'.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars'_distinct : hBars'.val.Nodup)
        (hBars'_subset : ∀ y : ℤ, Occurs y (vals hBars) → Occurs y (vals hBars'))
        (r r' : Std.I64)
        (hr : maximize_square_hole_area n m hBars vBars = ok r)
        (hr' : maximize_square_hole_area n m hBars' vBars = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- If the function returns r on input (n, m, hBars, vBars) and returns r' on input (n, m, hBars, vBars'), then r' >= r.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct; vBars' is a slice of 64-bit integers with len(vBars') <= 100, all entries distinct and in [2, m+1], and every value occurring in vBars also occurs in vBars'. -/
  theorem spec_12
      (n m : Std.I64) (hBars vBars vBars' : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (vBars'_len : vBars'.val.length ≤ 100)
      (vBars'_bounds : ∀ x ∈ vBars'.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars'_distinct : vBars'.val.Nodup)
      (vBars'_subset : ∀ y : ℤ, Occurs y (vals vBars) → Occurs y (vals vBars'))
      (r r' : Std.I64)
      (hr : maximize_square_hole_area n m hBars vBars = ok r)
      (hr' : maximize_square_hole_area n m hBars vBars' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars vBars' : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (vBars'_len : vBars'.val.length ≤ 100)
        (vBars'_bounds : ∀ x ∈ vBars'.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars'_distinct : vBars'.val.Nodup)
        (vBars'_subset : ∀ y : ℤ, Occurs y (vals vBars) → Occurs y (vals vBars'))
        (r r' : Std.I64)
        (hr : maximize_square_hole_area n m hBars vBars = ok r)
        (hr' : maximize_square_hole_area n m hBars vBars' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= (k+1)^2.
    Preconditions: n and m are integers with 1 <= n <= 10^9 and 1 <= m <= 10^9; hBars is a slice of 64-bit integers with 1 <= len(hBars) <= 100; vBars is a slice of 64-bit integers with 1 <= len(vBars) <= 100; every entry of hBars lies in [2, n+1] and all entries of hBars are distinct; every entry of vBars lies in [2, m+1] and all entries of vBars are distinct; k is an integer with k >= 1, and there exist integers a and b such that a, a+1, ..., a+k-1 all occur in hBars and b, b+1, ..., b+k-1 all occur in vBars. -/
  theorem spec_13
      (n m : Std.I64) (hBars vBars : Slice Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
      (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
      (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
      (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
      (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
      (hBars_distinct : hBars.val.Nodup)
      (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
      (vBars_distinct : vBars.val.Nodup)
      (k : ℤ) (hk : 1 ≤ k)
      (hblock_h : ∃ a : ℤ, ∀ t : ℤ, 1 ≤ t → t ≤ k - 1 → Occurs (a + t) (vals hBars))
      (hblock_v : ∃ b : ℤ, ∀ t : ℤ, 1 ≤ t → t ≤ k - 1 → Occurs (b + t) (vals vBars))
      (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r) :
      (k + 1) ^ 2 ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n m : Std.I64) (hBars vBars : Slice Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 9)
        (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 10 ^ 9)
        (hBars_lb : 1 ≤ hBars.val.length) (hBars_ub : hBars.val.length ≤ 100)
        (vBars_lb : 1 ≤ vBars.val.length) (vBars_ub : vBars.val.length ≤ 100)
        (hBars_bounds : ∀ x ∈ hBars.val, 2 ≤ x.val ∧ x.val ≤ n.val + 1)
        (hBars_distinct : hBars.val.Nodup)
        (vBars_bounds : ∀ x ∈ vBars.val, 2 ≤ x.val ∧ x.val ≤ m.val + 1)
        (vBars_distinct : vBars.val.Nodup)
        (k : ℤ) (hk : 1 ≤ k)
        (hblock_h : ∃ a : ℤ, ∀ t : ℤ, 1 ≤ t → t ≤ k - 1 → Occurs (a + t) (vals hBars))
        (hblock_v : ∃ b : ℤ, ∀ t : ℤ, 1 ≤ t → t ≤ k - 1 → Occurs (b + t) (vals vBars))
        (r : Std.I64) (hr : maximize_square_hole_area n m hBars vBars = ok r), (k + 1) ^ 2 ≤ r.val) := by
    sorry

  end AegisSpec.MaximizeSquareHoleArea
