import Aegis.CanMeasureWater.Code.Funs

/-!
# Specifications of `Aegis.CanMeasureWater.can_measure_water`

LeetCode problem `water-and-jug-problem`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanMeasureWater

namespace AegisSpec.CanMeasureWater

abbrev JugState : Type := Int × Int

def pourXtoY (_cx cy : Int) (s : JugState) : JugState :=
  let amt := min s.1 (cy - s.2)
  (s.1 - amt, s.2 + amt)

def pourYtoX (cx _cy : Int) (s : JugState) : JugState :=
  let amt := min s.2 (cx - s.1)
  (s.1 + amt, s.2 - amt)

inductive JugStep (cx cy : Int) : JugState → JugState → Prop where
  | fillX (a b : Int) (h : a ≤ cx) : JugStep cx cy (a, b) (cx, b)
  | fillY (a b : Int) (h : b ≤ cy) : JugStep cx cy (a, b) (a, cy)
  | emptyX (a b : Int) : JugStep cx cy (a, b) (0, b)
  | emptyY (a b : Int) : JugStep cx cy (a, b) (a, 0)
  | pourXY (a b : Int) : JugStep cx cy (a, b) (pourXtoY cx cy (a, b))
  | pourYX (a b : Int) : JugStep cx cy (a, b) (pourYtoX cx cy (a, b))

def Reachable (cx cy : Int) (s : JugState) : Prop :=
  Relation.ReflTransGen (JugStep cx cy) (0, 0) s

def CanReachTotal (cx cy target : Int) : Prop :=
  ∃ s : JugState, Reachable cx cy s ∧ s.1 + s.2 = target

/-- The function returns a result r (it does not fail), and r = true if and only if target <= x + y and gcd(x, y) divides target, where gcd(x, y) is the greatest positive integer dividing both x and y.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_1 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∃ r : Bool,
      can_measure_water x y target = ok r ∧
        (r = true ↔
          (target.val ≤ x.val + y.val ∧ (Int.gcd x.val y.val : Int) ∣ target.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∃ r : Bool,
      can_measure_water x y target = ok r ∧
        (r = true ↔
          (target.val ≤ x.val + y.val ∧ (Int.gcd x.val y.val : Int) ∣ target.val))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_2 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∃ r : Bool, can_measure_water x y target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∃ r : Bool, can_measure_water x y target = ok r) := by
  sorry

/-- Whenever the function returns a result r, if target > x + y, then r = false.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_3 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r : Bool, can_measure_water x y target = ok r →
      x.val + y.val < target.val → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r : Bool, can_measure_water x y target = ok r →
      x.val + y.val < target.val → r = false) := by
  sorry

/-- Whenever the function returns a result r, if gcd(x, y) does not divide target, then r = false.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_4 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r : Bool, can_measure_water x y target = ok r →
      ¬ ((Int.gcd x.val y.val : Int) ∣ target.val) → r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r : Bool, can_measure_water x y target = ok r →
      ¬ ((Int.gcd x.val y.val : Int) ∣ target.val) → r = false) := by
  sorry

/-- Whenever the function returns a result r, if target <= x + y and gcd(x, y) divides target, then r = true.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_5 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r : Bool, can_measure_water x y target = ok r →
      target.val ≤ x.val + y.val → (Int.gcd x.val y.val : Int) ∣ target.val →
        r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r : Bool, can_measure_water x y target = ok r →
      target.val ≤ x.val + y.val → (Int.gcd x.val y.val : Int) ∣ target.val →
        r = true) := by
  sorry

/-- Whenever the function returns a result r on input (x, y, target) and a result r' on input (y, x, target), we have r = r'.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_6 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r r' : Bool, can_measure_water x y target = ok r →
      can_measure_water y x target = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r r' : Bool, can_measure_water x y target = ok r →
      can_measure_water y x target = ok r' → r = r') := by
  sorry

/-- For every positive integer c such that 1 <= c*x, c*y, c*target <= 1000, whenever the function returns a result r on input (x, y, target) and a result r' on input (c*x, c*y, c*target), we have r = r'.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_7 (x y target : Std.I64) (c : Int)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000)
    (hc_pos : 0 < c)
    (hcx_pos : 1 ≤ c * x.val) (hcx_le : c * x.val ≤ 1000)
    (hcy_pos : 1 ≤ c * y.val) (hcy_le : c * y.val ≤ 1000)
    (hct_pos : 1 ≤ c * target.val) (hct_le : c * target.val ≤ 1000) :
    ∀ (x' y' t' : Std.I64),
      x'.val = c * x.val → y'.val = c * y.val → t'.val = c * target.val →
        ∀ r r' : Bool, can_measure_water x y target = ok r →
          can_measure_water x' y' t' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (x y target : Std.I64) (c : Int)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000)
    (hc_pos : 0 < c)
    (hcx_pos : 1 ≤ c * x.val) (hcx_le : c * x.val ≤ 1000)
    (hcy_pos : 1 ≤ c * y.val) (hcy_le : c * y.val ≤ 1000)
    (hct_pos : 1 ≤ c * target.val) (hct_le : c * target.val ≤ 1000), ∀ (x' y' t' : Std.I64),
      x'.val = c * x.val → y'.val = c * y.val → t'.val = c * target.val →
        ∀ r r' : Bool, can_measure_water x y target = ok r →
          can_measure_water x' y' t' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, if r = true, then there exists a finite sequence of operations of the following kinds, starting from the state in which both jugs are empty and never exceeding the jug capacities x and y: fill either jug completely, empty either jug completely, or pour from one jug into the other until the receiving jug is full or the pouring jug is empty; the final state has total water content exactly target liters.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_8 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r : Bool, can_measure_water x y target = ok r → r = true →
      CanReachTotal x.val y.val target.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r : Bool, can_measure_water x y target = ok r → r = true →
      CanReachTotal x.val y.val target.val) := by
  sorry

/-- Whenever the function returns a result r, if r = false, then no finite sequence of the allowed jug operations starting from both jugs empty has final total water content exactly target liters.
  Preconditions: x, y, and target are 64-bit integers with 1 <= x, y, target <= 1000. -/
theorem spec_9 (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000) :
    ∀ r : Bool, can_measure_water x y target = ok r → r = false →
      ¬ CanReachTotal x.val y.val target.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y target : Std.I64)
    (hx_pos : 1 ≤ x.val) (hx_le : x.val ≤ 1000)
    (hy_pos : 1 ≤ y.val) (hy_le : y.val ≤ 1000)
    (ht_pos : 1 ≤ target.val) (ht_le : target.val ≤ 1000), ∀ r : Bool, can_measure_water x y target = ok r → r = false →
      ¬ CanReachTotal x.val y.val target.val) := by
  sorry

end AegisSpec.CanMeasureWater
