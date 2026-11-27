import Aegis.DistanceTraveled.Code.Funs

/-!
# Specifications of `Aegis.DistanceTraveled.distance_traveled`

LeetCode problem `total-distance-traveled`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DistanceTraveled

  namespace AegisSpec.DistanceTraveled

  /-- Whenever the function returns a result r, let q be the unique integer such that 0 <= q and 4*q <= mainTank - 1 < 4*q + 4. Then r = 10 * (mainTank + min(additionalTank, q)).
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. (The official constraint says additionalTank >= 1; the provided examples also include additionalTank = 0, and all statements remain true under the stricter bound.) -/
  theorem spec_1 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ (r : Std.I64) (q : Int),
        distance_traveled mainTank additionalTank = ok r →
        0 ≤ q → 4 * q ≤ mainTank.val - 1 → mainTank.val - 1 < 4 * q + 4 →
        r.val = 10 * (mainTank.val + min additionalTank.val q) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ (r : Std.I64) (q : Int),
          distance_traveled mainTank additionalTank = ok r →
          0 ≤ q → 4 * q ≤ mainTank.val - 1 → mainTank.val - 1 < 4 * q + 4 →
          r.val = 10 * (mainTank.val + min additionalTank.val q)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_2 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∃ r : Std.I64, distance_traveled mainTank additionalTank = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∃ r : Std.I64, distance_traveled mainTank additionalTank = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 10 * mainTank <= r <= 10 * (mainTank + additionalTank).
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_3 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        10 * mainTank.val ≤ r.val ∧ r.val ≤ 10 * (mainTank.val + additionalTank.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          10 * mainTank.val ≤ r.val ∧ r.val ≤ 10 * (mainTank.val + additionalTank.val)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer L such that r = 10 * L.
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_4 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        ∃ L : Int, r.val = 10 * L := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          ∃ L : Int, r.val = 10 * L) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer t such that r = 10 * (mainTank + t) and 0 <= t <= additionalTank.
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_5 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        ∃ t : Int, r.val = 10 * (mainTank.val + t) ∧ 0 ≤ t ∧ t ≤ additionalTank.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          ∃ t : Int, r.val = 10 * (mainTank.val + t) ∧ 0 ≤ t ∧ t ≤ additionalTank.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer t such that r = 10 * (mainTank + t) and t is the largest integer satisfying 0 <= t <= additionalTank and 4*t <= mainTank - 1.
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_6 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        ∃ t : Int,
          r.val = 10 * (mainTank.val + t) ∧
          0 ≤ t ∧ t ≤ additionalTank.val ∧ 4 * t ≤ mainTank.val - 1 ∧
          ∀ t' : Int,
            0 ≤ t' → t' ≤ additionalTank.val → 4 * t' ≤ mainTank.val - 1 → t' ≤ t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          ∃ t : Int,
            r.val = 10 * (mainTank.val + t) ∧
            0 ≤ t ∧ t ≤ additionalTank.val ∧ 4 * t ≤ mainTank.val - 1 ∧
            ∀ t' : Int,
              0 ≤ t' → t' ≤ additionalTank.val → 4 * t' ≤ mainTank.val - 1 → t' ≤ t) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k <= additionalTank and 4*k <= mainTank - 1, we have r >= 10 * (mainTank + k).
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_7 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        ∀ k : Int,
          0 ≤ k → k ≤ additionalTank.val → 4 * k ≤ mainTank.val - 1 →
          10 * (mainTank.val + k) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          ∀ k : Int,
            0 ≤ k → k ≤ additionalTank.val → 4 * k ≤ mainTank.val - 1 →
            10 * (mainTank.val + k) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with k > additionalTank or 4*k > mainTank - 1, we have r < 10 * (mainTank + k).
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_8 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        ∀ k : Int,
          k > additionalTank.val ∨ 4 * k > mainTank.val - 1 →
          r.val < 10 * (mainTank.val + k) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          ∀ k : Int,
            k > additionalTank.val ∨ 4 * k > mainTank.val - 1 →
            r.val < 10 * (mainTank.val + k)) := by
    sorry

  /-- Whenever the function returns a result r, r = 10 * (mainTank + floor((mainTank - 1)/4)).
    Preconditions: 1 <= mainTank <= 100, 0 <= additionalTank <= 100, and additionalTank >= floor((mainTank - 1)/4). -/
  theorem spec_9 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100)
      (h_add_ge : (mainTank.val - 1) / 4 ≤ additionalTank.val) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        r.val = 10 * (mainTank.val + (mainTank.val - 1) / 4) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100)
        (h_add_ge : (mainTank.val - 1) / 4 ≤ additionalTank.val), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          r.val = 10 * (mainTank.val + (mainTank.val - 1) / 4)) := by
    sorry

  /-- Whenever the function returns a result r, r = 10 * (mainTank + additionalTank).
    Preconditions: 1 <= mainTank <= 100, 0 <= additionalTank <= 100, and additionalTank <= floor((mainTank - 1)/4). -/
  theorem spec_10 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100)
      (h_add_le : additionalTank.val ≤ (mainTank.val - 1) / 4) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        r.val = 10 * (mainTank.val + additionalTank.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100)
        (h_add_le : additionalTank.val ≤ (mainTank.val - 1) / 4), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          r.val = 10 * (mainTank.val + additionalTank.val)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 10 * (mainTank + floor((mainTank - 1)/4)).
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_11 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        r.val ≤ 10 * (mainTank.val + (mainTank.val - 1) / 4) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          r.val ≤ 10 * (mainTank.val + (mainTank.val - 1) / 4)) := by
    sorry

  /-- Whenever the function returns a result r, 10 <= r <= 1240.
    Preconditions: 1 <= mainTank <= 100 and 0 <= additionalTank <= 100. -/
  theorem spec_12 (mainTank additionalTank : Std.I64)
      (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
      (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100) :
      ∀ r : Std.I64,
        distance_traveled mainTank additionalTank = ok r →
        10 ≤ r.val ∧ r.val ≤ 1240 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mainTank additionalTank : Std.I64)
        (h_main_lo : 1 ≤ mainTank.val) (h_main_hi : mainTank.val ≤ 100)
        (h_add_lo : 0 ≤ additionalTank.val) (h_add_hi : additionalTank.val ≤ 100), ∀ r : Std.I64,
          distance_traveled mainTank additionalTank = ok r →
          10 ≤ r.val ∧ r.val ≤ 1240) := by
    sorry

  end AegisSpec.DistanceTraveled
