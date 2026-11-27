import Aegis.MaxArea.Code.Funs

/-!
# Specifications of `Aegis.MaxArea.max_area`

LeetCode problem `container-with-most-water`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxArea

def size (height : Slice Std.I64) : ℕ := height.val.length

def elem (height : Slice Std.I64) (i : ℕ) : ℤ :=
  (height.val.map (fun x => Aeneas.Std.IScalar.val x)).getD i 0

def span (i j : ℕ) : ℤ := (j : ℤ) - (i : ℤ)

def pairArea (height : Slice Std.I64) (i j : ℕ) : ℤ :=
  span i j * min (elem height i) (elem height j)

noncomputable def areas (height : Slice Std.I64) : Finset ℤ :=
  Finset.image (fun p : ℕ × ℕ => pairArea height p.1 p.2)
    (Finset.filter (fun p : ℕ × ℕ => p.1 < p.2)
      ((Finset.range (size height)).product (Finset.range (size height))))

noncomputable def maxArea (height : Slice Std.I64) : ℤ :=
  if h : (areas height).Nonempty then (areas height).max' h else 0

noncomputable def areasAvoiding (height : Slice Std.I64) (k : ℕ) : Finset ℤ :=
  Finset.image (fun p : ℕ × ℕ => pairArea height p.1 p.2)
    (Finset.filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ p.1 ≠ k ∧ p.2 ≠ k)
      ((Finset.range (size height)).product (Finset.range (size height))))

noncomputable def maxAreaAvoiding (height : Slice Std.I64) (k : ℕ) : ℤ :=
  if h : (areasAvoiding height k).Nonempty then (areasAvoiding height k).max' h else 0

noncomputable def heights (height : Slice Std.I64) : Finset ℤ :=
  (Finset.range (size height)).image (fun i => elem height i)

noncomputable def maxHeight (height : Slice Std.I64) : ℤ :=
  if h : (heights height).Nonempty then (heights height).max' h else 0

/-- The function returns a result r (it does not fail), and r = max { (j - i) * min(height[i], height[j]) | 0 <= i < j < len(height) }, where min is the smaller of the two endpoint heights. This is the largest possible area of a container formed by two distinct vertical lines.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_1 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧ r.val = maxArea height := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧ r.val = maxArea height) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions; in particular, there is no overflow or out-of-bounds failure.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_2 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_3 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (len(height) - 1) * M, where M = max { height[i] | 0 <= i < len(height) }.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_4 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      r.val ≤ ((size height : ℤ) - 1) * maxHeight height := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      r.val ≤ ((size height : ℤ) - 1) * maxHeight height) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(height), (j - i) * min(height[i], height[j]) <= r.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_5 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∀ i j : ℕ, i < j → j < size height → pairArea height i j ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∀ i j : ℕ, i < j → j < size height → pairArea height i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < j < len(height) such that r = (j - i) * min(height[i], height[j]).
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_6 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∃ i j : ℕ, i < j ∧ j < size height ∧ r.val = pairArea height i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∃ i j : ℕ, i < j ∧ j < size height ∧ r.val = pairArea height i j) := by
  sorry

/-- The function returns a result r and r = min(height[0], height[1]).
  Preconditions: len(height) = 2 and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_7 (height : Slice Std.I64)
    (hlen : size height = 2)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧
      r.val = min (elem height 0) (elem height 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : size height = 2)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧
      r.val = min (elem height 0) (elem height 1)) := by
  sorry

/-- The function returns a result r and r = (len(height) - 1) * h.
  Preconditions: len(height) >= 2, len(height) <= 100000, and there is an integer h with 0 <= h <= 10000 such that height[i] = h for every i with 0 <= i < len(height). -/
theorem spec_8 (height : Slice Std.I64) (h : ℤ)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hh_low : 0 ≤ h) (hh_high : h ≤ 10000)
    (hconst : ∀ i, i < size height → elem height i = h) :
    ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧
      r.val = ((size height : ℤ) - 1) * h := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (height : Slice Std.I64) (h : ℤ)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hh_low : 0 ≤ h) (hh_high : h ≤ 10000)
    (hconst : ∀ i, i < size height → elem height i = h), ∃ r : Std.I64, Aegis.MaxArea.max_area height = ok r ∧
      r.val = ((size height : ℤ) - 1) * h) := by
  sorry

/-- Let rev be the slice of length len(height) defined by rev[i] = height[len(height) - 1 - i] for every 0 <= i < len(height). Whenever the function returns r on height and r' on rev, r = r'.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_9 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ rev : Slice Std.I64, rev.val = height.val.reverse →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area rev = ok r' →
          r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ rev : Slice Std.I64, rev.val = height.val.reverse →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area rev = ok r' →
          r.val = r'.val) := by
  sorry

/-- Let h' be the slice of length len(height) + 1 defined by h'[i] = height[i] for 0 <= i < len(height) and h'[len(height)] = 0. Whenever the function returns r on height and r' on h', r = r'.
  Preconditions: len(height) >= 2, len(height) < 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_10 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_small : size height < 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ h' : Slice Std.I64, h'.val = height.val ++ [0#i64] →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
          r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_small : size height < 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ h' : Slice Std.I64, h'.val = height.val ++ [0#i64] →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
          r.val = r'.val) := by
  sorry

/-- Let h' be the slice of length len(height) + 1 defined by h'[0] = 0 and h'[i + 1] = height[i] for 0 <= i < len(height). Whenever the function returns r on height and r' on h', r = r'.
  Preconditions: len(height) >= 2, len(height) < 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_11 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_small : size height < 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ h' : Slice Std.I64, h'.val = 0#i64 :: height.val →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
          r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_small : size height < 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ h' : Slice Std.I64, h'.val = 0#i64 :: height.val →
      ∀ r r' : Std.I64,
        Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
          r.val = r'.val) := by
  sorry

/-- Let h' be the slice defined by h'[i] = c * height[i] for every 0 <= i < len(height). Whenever the function returns r on height and r' on h', r' = c * r.
  Preconditions: len(height) >= 2 and len(height) <= 100000; c is an integer with c >= 1, and for every i with 0 <= i < len(height), the product c * height[i] is an integer in the range 0 <= c * height[i] <= 10000. -/
theorem spec_12 (height : Slice Std.I64) (c : ℤ)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hc : 1 ≤ c)
    (hbound : ∀ i, i < size height →
      0 ≤ c * elem height i ∧ c * elem height i ≤ 10000) :
    ∀ h' : Slice Std.I64, size h' = size height →
      (∀ i, i < size h' → elem h' i = c * elem height i) →
        ∀ r r' : Std.I64,
          Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
            r'.val = c * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (height : Slice Std.I64) (c : ℤ)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hc : 1 ≤ c)
    (hbound : ∀ i, i < size height →
      0 ≤ c * elem height i ∧ c * elem height i ≤ 10000), ∀ h' : Slice Std.I64, size h' = size height →
      (∀ i, i < size h' → elem h' i = c * elem height i) →
        ∀ r r' : Std.I64,
          Aegis.MaxArea.max_area height = ok r → Aegis.MaxArea.max_area h' = ok r' →
            r'.val = c * r.val) := by
  sorry

/-- For every index k with 0 <= k < len(height) and height[k] = 0, whenever the function returns a result r, r = max { (j - i) * min(height[i], height[j]) | 0 <= i < j < len(height), i != k and j != k }.
  Preconditions: len(height) >= 3, len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_13 (height : Slice Std.I64)
    (hlen : 3 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∀ k : ℕ, k < size height → elem height k = 0 → r.val = maxAreaAvoiding height k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 3 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      ∀ k : ℕ, k < size height → elem height k = 0 → r.val = maxAreaAvoiding height k) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j with 0 <= i < j < len(height), height[i] > 0, and height[j] > 0.
  Preconditions: len(height) >= 2 and len(height) <= 100000, and for every i with 0 <= i < len(height), 0 <= height[i] <= 10000. -/
theorem spec_14 (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000) :
    ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      (0 < r.val ↔ ∃ i j : ℕ, i < j ∧ j < size height ∧
        0 < elem height i ∧ 0 < elem height j) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (height : Slice Std.I64)
    (hlen : 2 ≤ size height) (hlen_max : size height ≤ 100000)
    (hbound : ∀ i, i < size height → 0 ≤ elem height i ∧ elem height i ≤ 10000), ∀ r : Std.I64, Aegis.MaxArea.max_area height = ok r →
      (0 < r.val ↔ ∃ i j : ℕ, i < j ∧ j < size height ∧
        0 < elem height i ∧ 0 < elem height j)) := by
  sorry

end AegisSpec.MaxArea
