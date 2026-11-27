import Aegis.LargestRectangleArea.Code.Funs

/-!
# Specifications of `Aegis.LargestRectangleArea.largest_rectangle_area`

LeetCode problem `largest-rectangle-in-histogram`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LargestRectangleArea

set_option autoImplicit false

namespace AegisSpec.LargestRectangleArea

def contents (heights : Slice Std.I64) : List ℤ := heights.val.map (fun x => x.val)

def sliceLen (heights : Slice Std.I64) : ℕ := heights.val.length

def elemAt (heights : Slice Std.I64) (i : ℕ) : ℤ := (contents heights).getD i 0

def windowMin (heights : Slice Std.I64) (i j : ℕ) : ℤ :=
  ((contents heights).drop i).take (j + 1 - i) |>.min?.getD 0

def windowArea (heights : Slice Std.I64) (i j : ℕ) : ℤ :=
  windowMin heights i j * ((j : ℤ) - (i : ℤ) + 1)

def windowAreas (heights : Slice Std.I64) : List ℤ :=
  (List.range (sliceLen heights)).flatMap fun i =>
    ((List.range (sliceLen heights)).filter (fun j => decide (i ≤ j))).map
      (fun j => windowArea heights i j)

def maxArea (heights : Slice Std.I64) : ℤ := (windowAreas heights).max?.getD 0

def maxHeight (heights : Slice Std.I64) : ℤ := (contents heights).max?.getD 0

/-- Let n = len(heights). For 0-based inclusive indices 0 <= i <= j < n, let m(i,j) = min { heights[k] | i <= k <= j } and let area(i,j) = m(i,j) * (j - i + 1). The function returns a result r and r = max { area(i,j) | 0 <= i <= j < n }.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_1 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∃ r, largest_rectangle_area heights = ok r ∧ r.val = maxArea heights := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∃ r, largest_rectangle_area heights = ok r ∧ r.val = maxArea heights) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, access an out-of-bounds index, or perform arithmetic that leaves the 64-bit integer range.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_2 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∃ r, largest_rectangle_area heights = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∃ r, largest_rectangle_area heights = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_3 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(heights) * max { heights[k] | 0 <= k < len(heights) }.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_4 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      r.val ≤ (sliceLen heights : ℤ) * maxHeight heights := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      r.val ≤ (sliceLen heights : ℤ) * maxHeight heights) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(heights), r >= heights[i].
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_5 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      ∀ i, i < sliceLen heights → r.val ≥ elemAt heights i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      ∀ i, i < sliceLen heights → r.val ≥ elemAt heights i) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(heights), heights[i] = 0.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_6 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      (r.val = 0 ↔ ∀ i, i < sliceLen heights → elemAt heights i = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      (r.val = 0 ↔ ∀ i, i < sliceLen heights → elemAt heights i = 0)) := by
  sorry

/-- Whenever the function returns a result r and len(heights) = 1, r = heights[0].
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_7 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      sliceLen heights = 1 → r.val = elemAt heights 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      sliceLen heights = 1 → r.val = elemAt heights 0) := by
  sorry

/-- Whenever the function returns a result r and there is an integer h such that for every i with 0 <= i < len(heights), heights[i] = h, then r = len(heights) * h.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_8 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      ∀ h0 : ℤ, (∀ i, i < sliceLen heights → elemAt heights i = h0) →
      r.val = (sliceLen heights : ℤ) * h0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      ∀ h0 : ℤ, (∀ i, i < sliceLen heights → elemAt heights i = h0) →
      r.val = (sliceLen heights : ℤ) * h0) := by
  sorry

/-- Let rev be the slice with len(rev) = len(heights) and rev[i] = heights[len(heights) - 1 - i] for every i with 0 <= i < len(heights). If the function returns r on heights and returns r_rev on rev, then r = r_rev.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_9 (heights rev : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hrev : contents rev = (contents heights).reverse) :
    ∀ r r_rev, largest_rectangle_area heights = ok r →
      largest_rectangle_area rev = ok r_rev → r.val = r_rev.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights rev : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hrev : contents rev = (contents heights).reverse), ∀ r r_rev, largest_rectangle_area heights = ok r →
      largest_rectangle_area rev = ok r_rev → r.val = r_rev.val) := by
  sorry

/-- For every integer c with c >= 0 and c * heights[i] <= 10000 for every i with 0 <= i < len(heights), let scaled be the slice with scaled[i] = c * heights[i]. If the function returns r on heights and returns r_scaled on scaled, then r_scaled = c * r.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_10 (heights scaled : Slice Std.I64) (c : ℤ)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hc : 0 ≤ c)
    (hcbound : ∀ i, i < sliceLen heights → c * elemAt heights i ≤ 10000)
    (hscaled : contents scaled = (contents heights).map (fun x => c * x)) :
    ∀ r r_scaled, largest_rectangle_area heights = ok r →
      largest_rectangle_area scaled = ok r_scaled → r_scaled.val = c * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights scaled : Slice Std.I64) (c : ℤ)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hc : 0 ≤ c)
    (hcbound : ∀ i, i < sliceLen heights → c * elemAt heights i ≤ 10000)
    (hscaled : contents scaled = (contents heights).map (fun x => c * x)), ∀ r r_scaled, largest_rectangle_area heights = ok r →
      largest_rectangle_area scaled = ok r_scaled → r_scaled.val = c * r.val) := by
  sorry

/-- If the function returns r on heights and returns r_larger on larger, then r <= r_larger.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. Let larger be another slice satisfying the same input bounds, with len(larger) = len(heights), and suppose that for every i with 0 <= i < len(heights), heights[i] <= larger[i]. -/
theorem spec_11 (heights larger : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hpos' : 1 ≤ sliceLen larger) (hlen' : sliceLen larger ≤ 100000)
    (hh' : ∀ i, i < sliceLen larger → 0 ≤ elemAt larger i ∧ elemAt larger i ≤ 10000)
    (hle_len : sliceLen larger = sliceLen heights)
    (hle : ∀ i, i < sliceLen heights → elemAt heights i ≤ elemAt larger i) :
    ∀ r r_larger, largest_rectangle_area heights = ok r →
      largest_rectangle_area larger = ok r_larger → r.val ≤ r_larger.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights larger : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000)
    (hpos' : 1 ≤ sliceLen larger) (hlen' : sliceLen larger ≤ 100000)
    (hh' : ∀ i, i < sliceLen larger → 0 ≤ elemAt larger i ∧ elemAt larger i ≤ 10000)
    (hle_len : sliceLen larger = sliceLen heights)
    (hle : ∀ i, i < sliceLen heights → elemAt heights i ≤ elemAt larger i), ∀ r r_larger, largest_rectangle_area heights = ok r →
      largest_rectangle_area larger = ok r_larger → r.val ≤ r_larger.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j with 0 <= i <= j < len(heights) such that r = (min { heights[k] | i <= k <= j }) * (j - i + 1).
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_12 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      ∃ i j, i ≤ j ∧ j < sliceLen heights ∧ r.val = windowArea heights i j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      ∃ i j, i ≤ j ∧ j < sliceLen heights ∧ r.val = windowArea heights i j) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i and j with 0 <= i <= j < len(heights), (min { heights[k] | i <= k <= j }) * (j - i + 1) <= r.
  Preconditions: heights is a slice of 64-bit integers with 1 <= len(heights) <= 100000, and for every i with 0 <= i < len(heights), 0 <= heights[i] <= 10000. -/
theorem spec_13 (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000) :
    ∀ r, largest_rectangle_area heights = ok r →
      ∀ i j, i ≤ j → j < sliceLen heights → windowArea heights i j ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (hpos : 1 ≤ sliceLen heights) (hlen : sliceLen heights ≤ 100000)
    (hh : ∀ i, i < sliceLen heights → 0 ≤ elemAt heights i ∧ elemAt heights i ≤ 10000), ∀ r, largest_rectangle_area heights = ok r →
      ∀ i j, i ≤ j → j < sliceLen heights → windowArea heights i j ≤ r.val) := by
  sorry

end AegisSpec.LargestRectangleArea
