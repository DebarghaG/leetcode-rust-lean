import Aegis.NumOfBurgers.Code.Funs

/-!
# Specifications of `Aegis.NumOfBurgers.num_of_burgers`

LeetCode problem `number-of-burgers-with-no-waste-of-ingredients`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfBurgers

  def vecVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  def IsBurgersSolution (tomatoSlices cheeseSlices j s : ℤ) : Prop :=
    0 ≤ j ∧ 0 ≤ s ∧ 4 * j + 2 * s = tomatoSlices ∧ j + s = cheeseSlices

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, exactly one of the following holds: (a) len(r)=2, and if j = r[0] and s = r[1], then j and s are nonnegative integers with 4*j + 2*s = tomatoSlices and j + s = cheeseSlices; or (b) len(r)=0 and there do not exist integers j and s with 0 <= j, 0 <= s, 4*j + 2*s = tomatoSlices, and j + s = cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_1 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      (r.val.length = 2 ∧
          IsBurgersSolution tomatoSlices.val cheeseSlices.val (vecVals r)[0]! (vecVals r)[1]!) ∨
        (r.val.length = 0 ∧
          ¬ ∃ j s : ℤ, IsBurgersSolution tomatoSlices.val cheeseSlices.val j s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), (r.val.length = 2 ∧
            IsBurgersSolution tomatoSlices.val cheeseSlices.val (vecVals r)[0]! (vecVals r)[1]!) ∨
          (r.val.length = 0 ∧
            ¬ ∃ j s : ℤ, IsBurgersSolution tomatoSlices.val cheeseSlices.val j s)) := by
    sorry

  /-- num_of_burgers tomatoSlices cheeseSlices returns a result r; it does not fail.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_2 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, len(r)=0 or len(r)=2.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_3 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 0 ∨ r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 0 ∨ r.val.length = 2) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, len(r)=2 if and only if there exists an integer k such that tomatoSlices = 2*k, and 2*cheeseSlices <= tomatoSlices, and tomatoSlices <= 4*cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_4 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      (r.val.length = 2 ↔
        ∃ k : ℤ, tomatoSlices.val = 2 * k ∧
          2 * cheeseSlices.val ≤ tomatoSlices.val ∧
            tomatoSlices.val ≤ 4 * cheeseSlices.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), (r.val.length = 2 ↔
          ∃ k : ℤ, tomatoSlices.val = 2 * k ∧
            2 * cheeseSlices.val ≤ tomatoSlices.val ∧
              tomatoSlices.val ≤ 4 * cheeseSlices.val)) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if len(r)=2 then 0 <= r[0] <= cheeseSlices and 0 <= r[1] <= cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_5 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 →
        0 ≤ (vecVals r)[0]! ∧ (vecVals r)[0]! ≤ cheeseSlices.val ∧
          0 ≤ (vecVals r)[1]! ∧ (vecVals r)[1]! ≤ cheeseSlices.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 →
          0 ≤ (vecVals r)[0]! ∧ (vecVals r)[0]! ≤ cheeseSlices.val ∧
            0 ≤ (vecVals r)[1]! ∧ (vecVals r)[1]! ≤ cheeseSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if len(r)=2 then 4*r[0] + 2*r[1] = tomatoSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_6 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 →
        4 * (vecVals r)[0]! + 2 * (vecVals r)[1]! = tomatoSlices.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 →
          4 * (vecVals r)[0]! + 2 * (vecVals r)[1]! = tomatoSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if len(r)=2 then r[0] + r[1] = cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_7 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 → (vecVals r)[0]! + (vecVals r)[1]! = cheeseSlices.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 → (vecVals r)[0]! + (vecVals r)[1]! = cheeseSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if len(r)=2 then 2*r[0] = tomatoSlices - 2*cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_8 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 →
        2 * (vecVals r)[0]! = tomatoSlices.val - 2 * cheeseSlices.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 →
          2 * (vecVals r)[0]! = tomatoSlices.val - 2 * cheeseSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if len(r)=2 then 2*r[1] = 4*cheeseSlices - tomatoSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_9 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 →
        2 * (vecVals r)[1]! = 4 * cheeseSlices.val - tomatoSlices.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 →
          2 * (vecVals r)[1]! = 4 * cheeseSlices.val - tomatoSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r with len(r)=2, for every pair of integers j and s such that 0 <= j, 0 <= s, 4*j + 2*s = tomatoSlices, and j + s = cheeseSlices, it holds that r[0] = j and r[1] = s.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_10 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      r.val.length = 2 →
        ∀ j s : ℤ, IsBurgersSolution tomatoSlices.val cheeseSlices.val j s →
          (vecVals r)[0]! = j ∧ (vecVals r)[1]! = s := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), r.val.length = 2 →
          ∀ j s : ℤ, IsBurgersSolution tomatoSlices.val cheeseSlices.val j s →
            (vecVals r)[0]! = j ∧ (vecVals r)[1]! = s) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if tomatoSlices = 2*cheeseSlices, then len(r)=2, r[0]=0, and r[1]=cheeseSlices.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_11 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      tomatoSlices.val = 2 * cheeseSlices.val →
        r.val.length = 2 ∧ (vecVals r)[0]! = 0 ∧
          (vecVals r)[1]! = cheeseSlices.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), tomatoSlices.val = 2 * cheeseSlices.val →
          r.val.length = 2 ∧ (vecVals r)[0]! = 0 ∧
            (vecVals r)[1]! = cheeseSlices.val) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if tomatoSlices = 4*cheeseSlices, then len(r)=2, r[0]=cheeseSlices, and r[1]=0.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_12 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      tomatoSlices.val = 4 * cheeseSlices.val →
        r.val.length = 2 ∧ (vecVals r)[0]! = cheeseSlices.val ∧
          (vecVals r)[1]! = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), tomatoSlices.val = 4 * cheeseSlices.val →
          r.val.length = 2 ∧ (vecVals r)[0]! = cheeseSlices.val ∧
            (vecVals r)[1]! = 0) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if cheeseSlices = 0 and tomatoSlices > 0, then len(r)=0.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_13 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      cheeseSlices.val = 0 ∧ 0 < tomatoSlices.val → r.val.length = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), cheeseSlices.val = 0 ∧ 0 < tomatoSlices.val → r.val.length = 0) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if cheeseSlices = 0 and tomatoSlices = 0, then len(r)=2, r[0]=0, and r[1]=0.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_14 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      cheeseSlices.val = 0 ∧ tomatoSlices.val = 0 →
        r.val.length = 2 ∧ (vecVals r)[0]! = 0 ∧ (vecVals r)[1]! = 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), cheeseSlices.val = 0 ∧ tomatoSlices.val = 0 →
          r.val.length = 2 ∧ (vecVals r)[0]! = 0 ∧ (vecVals r)[1]! = 0) := by
    sorry

  /-- Whenever num_of_burgers tomatoSlices cheeseSlices returns a result r, if tomatoSlices = 0 and cheeseSlices > 0, then len(r)=0.
    Preconditions: 0 <= tomatoSlices <= 10000000 and 0 <= cheeseSlices <= 10000000. -/
  theorem spec_15 (tomatoSlices cheeseSlices : Std.I64)
      (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
      (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r) :
      tomatoSlices.val = 0 ∧ 0 < cheeseSlices.val → r.val.length = 0 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (tomatoSlices cheeseSlices : Std.I64)
        (h_tomatoSlices : 0 ≤ tomatoSlices.val ∧ tomatoSlices.val ≤ 10000000)
        (h_cheeseSlices : 0 ≤ cheeseSlices.val ∧ cheeseSlices.val ≤ 10000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.NumOfBurgers.num_of_burgers tomatoSlices cheeseSlices = ok r), tomatoSlices.val = 0 ∧ 0 < cheeseSlices.val → r.val.length = 0) := by
    sorry

  end AegisSpec.NumOfBurgers
