import Aegis.MaxHeightOfTriangle.Code.Funs

/-!
# Specifications of `Aegis.MaxHeightOfTriangle.max_height_of_triangle`

LeetCode problem `maximum-height-of-a-triangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxHeightOfTriangle

namespace AegisSpec.MaxHeightOfTriangle

def div2 (x : Int) : Int := x / 2

def c (h : Int) : Int := div2 (h + 1)

def f (h : Int) : Int := div2 h

def needFirst (h : Int) : Int := c h * c h

def needSecond (h : Int) : Int := f h * (f h + 1)

def RedFirst (red blue : Int) (h : Int) : Prop :=
  red ≥ needFirst h ∧ blue ≥ needSecond h

def BlueFirst (red blue : Int) (h : Int) : Prop :=
  blue ≥ needFirst h ∧ red ≥ needSecond h

instance (red blue h : Int) : Decidable (RedFirst red blue h) := by
  unfold RedFirst needFirst needSecond c f div2
  infer_instance

instance (red blue h : Int) : Decidable (BlueFirst red blue h) := by
  unfold BlueFirst needFirst needSecond c f div2
  infer_instance

def HR (red blue : Int) : Nat :=
  Nat.findGreatest (fun h : Nat => RedFirst red blue (h : Int)) (red + blue).toNat

def HB (red blue : Int) : Nat :=
  Nat.findGreatest (fun h : Nat => BlueFirst red blue (h : Int)) (red + blue).toNat

def cNat (h : Nat) : Nat := (h + 1) / 2

def fNat (h : Nat) : Nat := h / 2

abbrev Color : Type := Bool

def IsAltTriangle (h : Nat) (rows : List (List Color)) : Prop :=
  rows.length = h ∧
  (∀ (i : Nat) (row : List Color), rows[i]? = some row → row.length = i + 1) ∧
  (∀ (i : Nat) (row : List Color), rows[i]? = some row → ∃ col : Color, ∀ cell ∈ row, cell = col) ∧
  (∀ (i : Nat) (r₁ r₂ : List Color) (c₁ c₂ : Color),
      rows[i]? = some r₁ → rows[i + 1]? = some r₂ →
      (∀ cell ∈ r₁, cell = c₁) → (∀ cell ∈ r₂, cell = c₂) → c₁ ≠ c₂)

def rowColor (row : List Color) : Color := row.headD false

def countRows (rows : List (List Color)) (col : Color) : Nat :=
  (rows.filter (fun row => rowColor row == col)).length

/-- Let c(h) = (h + 1) // 2 (integer division) and f(h) = h // 2 for every integer h >= 0. Define H_R as the largest h >= 0 such that red >= c(h) * c(h) and blue >= f(h) * (f(h) + 1). Define H_B as the largest h >= 0 such that blue >= c(h) * c(h) and red >= f(h) * (f(h) + 1). Whenever the function returns a result r, r = max(H_R, H_B).
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_1 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      r.val = ((Nat.max (HR red.val blue.val) (HB red.val blue.val) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      r.val = ((Nat.max (HR red.val blue.val) (HB red.val blue.val) : Nat) : Int)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_2 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∃ r : Std.I64, max_height_of_triangle red blue = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∃ r : Std.I64, max_height_of_triangle red blue = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_3 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64, max_height_of_triangle red blue = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64, max_height_of_triangle red blue = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 19.
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_4 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val ≤ 19 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val ≤ 19) := by
  sorry

/-- Whenever the function returns a result r, r * (r + 1) / 2 <= red + blue.
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_5 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      div2 (r.val * (r.val + 1)) ≤ red.val + blue.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      div2 (r.val * (r.val + 1)) ≤ red.val + blue.val) := by
  sorry

/-- Whenever the function returns a result r, let c = (r + 1) // 2 (integer division). Then c * c <= max(red, blue).
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_6 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      c r.val * c r.val ≤ max red.val blue.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      c r.val * c r.val ≤ max red.val blue.val) := by
  sorry

/-- If the function returns r1 on input (red, blue) and returns r2 on input (blue, red), then r1 = r2.
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_7 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r₁ r₂ : Std.I64,
      max_height_of_triangle red blue = ok r₁ →
      max_height_of_triangle blue red = ok r₂ → r₁.val = r₂.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r₁ r₂ : Std.I64,
      max_height_of_triangle red blue = ok r₁ →
      max_height_of_triangle blue red = ok r₂ → r₁.val = r₂.val) := by
  sorry

/-- If the function returns r1 on input (red1, blue1) and returns r2 on input (red2, blue2), then r1 <= r2.
  Preconditions: 1 <= red1, blue1, red2, blue2 <= 100, red1 <= red2, blue1 <= blue2 -/
theorem spec_8 (red₁ blue₁ red₂ blue₂ : Std.I64)
    (hred₁_lo : 1 ≤ red₁.val) (hred₁_hi : red₁.val ≤ 100)
    (hblue₁_lo : 1 ≤ blue₁.val) (hblue₁_hi : blue₁.val ≤ 100)
    (hred₂_lo : 1 ≤ red₂.val) (hred₂_hi : red₂.val ≤ 100)
    (hblue₂_lo : 1 ≤ blue₂.val) (hblue₂_hi : blue₂.val ≤ 100)
    (hred : red₁.val ≤ red₂.val) (hblue : blue₁.val ≤ blue₂.val) :
    ∀ r₁ r₂ : Std.I64,
      max_height_of_triangle red₁ blue₁ = ok r₁ →
      max_height_of_triangle red₂ blue₂ = ok r₂ → r₁.val ≤ r₂.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (red₁ blue₁ red₂ blue₂ : Std.I64)
    (hred₁_lo : 1 ≤ red₁.val) (hred₁_hi : red₁.val ≤ 100)
    (hblue₁_lo : 1 ≤ blue₁.val) (hblue₁_hi : blue₁.val ≤ 100)
    (hred₂_lo : 1 ≤ red₂.val) (hred₂_hi : red₂.val ≤ 100)
    (hblue₂_lo : 1 ≤ blue₂.val) (hblue₂_hi : blue₂.val ≤ 100)
    (hred : red₁.val ≤ red₂.val) (hblue : blue₁.val ≤ blue₂.val), ∀ r₁ r₂ : Std.I64,
      max_height_of_triangle red₁ blue₁ = ok r₁ →
      max_height_of_triangle red₂ blue₂ = ok r₂ → r₁.val ≤ r₂.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: red = 1 and blue = 1 -/
theorem spec_9 (red blue : Std.I64)
    (hred : red.val = 1) (hblue : blue.val = 1) :
    ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred : red.val = 1) (hblue : blue.val = 1), ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = 2.
  Preconditions: 1 <= red, blue <= 100, min(red, blue) = 1, and max(red, blue) >= 2 -/
theorem spec_10 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100)
    (hmin : min red.val blue.val = 1) (hmax : 2 ≤ max red.val blue.val) :
    ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val = 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100)
    (hmin : min red.val blue.val = 1) (hmax : 2 ≤ max red.val blue.val), ∀ r : Std.I64, max_height_of_triangle red blue = ok r → r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, at least one of the following two conditions holds: (1) red >= ((r+1)//2) * ((r+1)//2) and blue >= (r//2) * ((r//2) + 1); or (2) blue >= ((r+1)//2) * ((r+1)//2) and red >= (r//2) * ((r//2) + 1).
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_11 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      RedFirst red.val blue.val r.val ∨ BlueFirst red.val blue.val r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      RedFirst red.val blue.val r.val ∨ BlueFirst red.val blue.val r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer h > r, neither of the following two conditions holds: (1) red >= ((h+1)//2) * ((h+1)//2) and blue >= (h//2) * ((h//2) + 1); nor (2) blue >= ((h+1)//2) * ((h+1)//2) and red >= (h//2) * ((h//2) + 1).
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_12 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      ∀ h : Int, r.val < h →
        ¬ RedFirst red.val blue.val h ∧ ¬ BlueFirst red.val blue.val h := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      ∀ h : Int, r.val < h →
        ¬ RedFirst red.val blue.val h ∧ ¬ BlueFirst red.val blue.val h) := by
  sorry

/-- Whenever the function returns a result r, in any valid alternating-color triangle of height r, one color appears in exactly (r+1)//2 rows and the other color appears in exactly r//2 rows.
  Preconditions: 1 <= red <= 100 and 1 <= blue <= 100 -/
theorem spec_13 (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100) :
    ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      ∀ rows : List (List Color),
        IsAltTriangle r.val.toNat rows →
          (countRows rows true = cNat r.val.toNat ∧ countRows rows false = fNat r.val.toNat) ∨
          (countRows rows false = cNat r.val.toNat ∧ countRows rows true = fNat r.val.toNat) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (red blue : Std.I64)
    (hred_lo : 1 ≤ red.val) (hred_hi : red.val ≤ 100)
    (hblue_lo : 1 ≤ blue.val) (hblue_hi : blue.val ≤ 100), ∀ r : Std.I64,
      max_height_of_triangle red blue = ok r →
      ∀ rows : List (List Color),
        IsAltTriangle r.val.toNat rows →
          (countRows rows true = cNat r.val.toNat ∧ countRows rows false = fNat r.val.toNat) ∨
          (countRows rows false = cNat r.val.toNat ∧ countRows rows true = fNat r.val.toNat)) := by
  sorry

end AegisSpec.MaxHeightOfTriangle
