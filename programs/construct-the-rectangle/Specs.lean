import Aegis.ConstructRectangle.Code.Funs

/-!
# Specifications of `Aegis.ConstructRectangle.construct_rectangle`

LeetCode problem `construct-the-rectangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ConstructRectangle

  set_option autoImplicit false

  namespace AegisSpec.ConstructRectangle

  def entry (r : alloc.vec.Vec I64) (i : Nat) : Int :=
    (r.val[i]?).elim 0 fun x => x.val

  def IsSquare (n : Int) : Prop :=
    ∃ k : Int, k * k = n

  def IsPrime (p : Int) : Prop :=
    1 < p ∧ ∀ d : Int, 0 < d → d ∣ p → d = 1 ∨ d = p

  /-- Whenever construct_rectangle area returns a result r, we have len(r) = 2. Writing L = r[0] and W = r[1], L and W are positive integers, L * W = area, L >= W, and for every pair of positive integers (L', W') with L' * W' = area and L' >= W', the inequality L - W <= L' - W' holds.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_1 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r →
        r.val.length = 2 ∧
        1 ≤ entry r 0 ∧ 1 ≤ entry r 1 ∧
        entry r 0 * entry r 1 = area.val ∧
        entry r 1 ≤ entry r 0 ∧
        ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
          entry r 0 - entry r 1 ≤ L' - W' := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r →
          r.val.length = 2 ∧
          1 ≤ entry r 0 ∧ 1 ≤ entry r 1 ∧
          entry r 0 * entry r 1 = area.val ∧
          entry r 1 ≤ entry r 0 ∧
          ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
            entry r 0 - entry r 1 ≤ L' - W') := by
    sorry

  /-- The function construct_rectangle area returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_2 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∃ r, construct_rectangle area = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∃ r, construct_rectangle area = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_3 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, both entries are positive: r[0] >= 1 and r[1] >= 1.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_4 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        1 ≤ entry r 0 ∧ 1 ≤ entry r 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          1 ≤ entry r 0 ∧ 1 ≤ entry r 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, the first entry is at least the second entry: r[0] >= r[1].
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_5 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        entry r 1 ≤ entry r 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          entry r 1 ≤ entry r 0) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, both entries are at most area: r[0] <= area and r[1] <= area.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_6 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        entry r 0 ≤ area.val ∧ entry r 1 ≤ area.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          entry r 0 ≤ area.val ∧ entry r 1 ≤ area.val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, the entries multiply exactly to area: r[0] * r[1] = area.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_7 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        entry r 0 * entry r 1 = area.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          entry r 0 * entry r 1 = area.val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, r[1] is a positive divisor of area, and for every positive divisor d of area satisfying d * d <= area, we have d <= r[1].
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_8 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        0 < entry r 1 ∧ entry r 1 ∣ area.val ∧
        ∀ d : Int, 0 < d → d ∣ area.val → d * d ≤ area.val → d ≤ entry r 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          0 < entry r 1 ∧ entry r 1 ∣ area.val ∧
          ∀ d : Int, 0 < d → d ∣ area.val → d * d ≤ area.val → d ≤ entry r 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, r[0] is a positive divisor of area, and for every positive divisor d of area satisfying d * d >= area, we have r[0] <= d.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_9 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        0 < entry r 0 ∧ entry r 0 ∣ area.val ∧
        ∀ d : Int, 0 < d → d ∣ area.val → area.val ≤ d * d → entry r 0 ≤ d := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          0 < entry r 0 ∧ entry r 0 ∣ area.val ∧
          ∀ d : Int, 0 < d → d ∣ area.val → area.val ≤ d * d → entry r 0 ≤ d) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, for every pair of positive integers (L', W') with L' * W' = area and L' >= W', we have r[0] + r[1] <= L' + W'.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_10 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
          entry r 0 + entry r 1 ≤ L' + W' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
            entry r 0 + entry r 1 ≤ L' + W') := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, if area is not a perfect square, then r[0] > r[1].
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_11 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        ¬ IsSquare area.val → entry r 1 < entry r 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          ¬ IsSquare area.val → entry r 1 < entry r 0) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, if area = k * k for some positive integer k, then r[0] = k and r[1] = k.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_12 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        ∀ k : Int, 0 < k → area.val = k * k → entry r 0 = k ∧ entry r 1 = k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          ∀ k : Int, 0 < k → area.val = k * k → entry r 0 = k ∧ entry r 1 = k) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, if area is prime, then r[0] = area and r[1] = 1.
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_13 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        IsPrime area.val → entry r 0 = area.val ∧ entry r 1 = 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          IsPrime area.val → entry r 0 = area.val ∧ entry r 1 = 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, if (L', W') is any pair of positive integers such that L' * W' = area, L' >= W', and L' - W' = r[0] - r[1], then L' = r[0] and W' = r[1].
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_14 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
          L' - W' = entry r 0 - entry r 1 → L' = entry r 0 ∧ W' = entry r 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          ∀ L' W' : Int, 0 < L' → 0 < W' → L' * W' = area.val → W' ≤ L' →
            L' - W' = entry r 0 - entry r 1 → L' = entry r 0 ∧ W' = entry r 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, the width-squared and length-squared bound the area: r[1] * r[1] <= area <= r[0] * r[0].
    Preconditions: area is an integer with 1 <= area <= 10000000. -/
  theorem spec_15 (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000) :
      ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
        entry r 1 * entry r 1 ≤ area.val ∧ area.val ≤ entry r 0 * entry r 0 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (area : I64) (hlo : 1 ≤ area.val) (hhi : area.val ≤ 10000000), ∀ r, construct_rectangle area = ok r → r.val.length = 2 →
          entry r 1 * entry r 1 ≤ area.val ∧ area.val ≤ entry r 0 * entry r 0) := by
    sorry

  end AegisSpec.ConstructRectangle
