import Aegis.CountOperations.Code.Funs

/-!
# Specifications of `Aegis.CountOperations.count_operations`

LeetCode problem `count-operations-to-obtain-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountOperations

  namespace AegisSpec.CountOperations

  def opStep (x y : ℤ) : ℤ × ℤ :=
    if x ≥ y then (x - y, y) else (x, y - x)

  def opRun (n : ℕ) (p : ℤ × ℤ) : ℤ × ℤ := (fun q : ℤ × ℤ => opStep q.1 q.2)^[n] p

  def HasZeroComponent (p : ℤ × ℤ) : Prop := p.1 = 0 ∨ p.2 = 0

  def IsLeastOpCount (a b : ℤ) (k : ℤ) : Prop :=
    ∃ n : ℕ, (n : ℤ) = k ∧ HasZeroComponent (opRun n (a, b)) ∧
      ∀ j : ℕ, j < n → ¬ HasZeroComponent (opRun j (a, b))

  def EndsInGcd (a b : ℤ) (n : ℕ) : Prop :=
    ((opRun n (a, b)).1 = 0 ∧ (opRun n (a, b)).2 = (Int.gcd a b : ℤ)) ∨
      ((opRun n (a, b)).2 = 0 ∧ (opRun n (a, b)).1 = (Int.gcd a b : ℤ))

  def toI64 (x : ℤ) : Aeneas.Std.I64 := Aeneas.Std.IScalar.mk (BitVec.ofInt 64 x)

  /-- Let T be the operation map on pairs of nonnegative integers: T(x,y) = (x - y, y) if x >= y, and T(x,y) = (x, y - x) otherwise. Let N(a,b) be the least integer k >= 0 such that the first or second component of T^k(a,b) is 0. Then the function returns a result r and r = N(num1,num2).
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_1 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧ IsLeastOpCount num1.val num2.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧ IsLeastOpCount num1.val num2.val r.val) := by
    sorry

  /-- For every num1,num2 satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_2 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000), ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r) := by
    sorry

  /-- If num1 = 0 or num2 = 0, then the function returns a result r and r = 0.
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_3 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hz : num1.val = 0 ∨ num2.val = 0) :
      ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hz : num1.val = 0 ∨ num2.val = 0), ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r ∧ r.val = 0) := by
    sorry

  /-- If num1 > 0 and num2 > 0, then the function returns a result r and r >= 1.
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_4 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val) :
      ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val), ∃ r : Aeneas.Std.I64, count_operations num1 num2 = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if num1 = num2 and num1 > 0.
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_5 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧ (r.val = 1 ↔ num1.val = num2.val ∧ 0 < num1.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧ (r.val = 1 ↔ num1.val = num2.val ∧ 0 < num1.val)) := by
    sorry

  /-- For every such a,b, the function returns a result r on input (a,b) and the same result r on input (b,a).
    Preconditions: 0 <= a <= 100000 and 0 <= b <= 100000. -/
  theorem spec_6 (a b : Aeneas.Std.I64)
      (halo : 0 ≤ a.val) (hahi : a.val ≤ 100000)
      (hblo : 0 ≤ b.val) (hbhi : b.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64, count_operations a b = ok r ∧ count_operations b a = ok r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b : Aeneas.Std.I64)
        (halo : 0 ≤ a.val) (hahi : a.val ≤ 100000)
        (hblo : 0 ≤ b.val) (hbhi : b.val ≤ 100000), ∃ r : Aeneas.Std.I64, count_operations a b = ok r ∧ count_operations b a = ok r) := by
    sorry

  /-- The function returns a result r for input (a,b) and the same result r for input (d*a,d*b).
    Preconditions: d, a, b are integers with d >= 1, 0 <= a <= 100000, 0 <= b <= 100000, d*a <= 100000, and d*b <= 100000. -/
  theorem spec_7 (d : ℤ) (a b : Aeneas.Std.I64)
      (hd : 1 ≤ d)
      (halo : 0 ≤ a.val) (hahi : a.val ≤ 100000)
      (hblo : 0 ≤ b.val) (hbhi : b.val ≤ 100000)
      (hda : d * a.val ≤ 100000) (hdb : d * b.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        count_operations a b = ok r ∧
          count_operations (toI64 (d * a.val)) (toI64 (d * b.val)) = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (d : ℤ) (a b : Aeneas.Std.I64)
        (hd : 1 ≤ d)
        (halo : 0 ≤ a.val) (hahi : a.val ≤ 100000)
        (hblo : 0 ≤ b.val) (hbhi : b.val ≤ 100000)
        (hda : d * a.val ≤ 100000) (hdb : d * b.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          count_operations a b = ok r ∧
            count_operations (toI64 (d * a.val)) (toI64 (d * b.val)) = ok r) := by
    sorry

  /-- The function returns a result r and r = max(num1,num2) / min(num1,num2), where the division is exact integer division.
    Preconditions: 0 <= num1 <= 100000, 0 <= num2 <= 100000, num1 > 0, num2 > 0, and (num1 divides num2 or num2 divides num1). -/
  theorem spec_8 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val)
      (hdiv : num1.val ∣ num2.val ∨ num2.val ∣ num1.val) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧
          r.val = max num1.val num2.val / min num1.val num2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val)
        (hdiv : num1.val ∣ num2.val ∨ num2.val ∣ num1.val), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧
            r.val = max num1.val num2.val / min num1.val num2.val) := by
    sorry

  /-- The function returns a result r and r = max(num1,num2).
    Preconditions: 0 <= num1 <= 100000, 0 <= num2 <= 100000, num1 > 0, num2 > 0, and |num1 - num2| = 1. -/
  theorem spec_9 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val)
      (hnear : (num1.val - num2.val).natAbs = 1) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧ r.val = max num1.val num2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val)
        (hnear : (num1.val - num2.val).natAbs = 1), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧ r.val = max num1.val num2.val) := by
    sorry

  /-- The function returns a result r and r <= max(num1,num2).
    Preconditions: 0 <= num1 <= 100000 and 0 <= num2 <= 100000. -/
  theorem spec_10 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧ r.val ≤ max num1.val num2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧ r.val ≤ max num1.val num2.val) := by
    sorry

  /-- The function returns a result r and r >= max(num1,num2) / min(num1,num2), where the quotient is integer floor division.
    Preconditions: 0 <= num1 <= 100000, 0 <= num2 <= 100000, num1 > 0, and num2 > 0. -/
  theorem spec_11 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧
          max num1.val num2.val / min num1.val num2.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧
            max num1.val num2.val / min num1.val num2.val ≤ r.val) := by
    sorry

  /-- Let (a,b) = (num1 - num2, num2) if num1 > num2, and (a,b) = (num1, num2 - num1) if num2 > num1. Then the function returns a result r for input (num1,num2), a result r' for input (a,b), and r = r' + 1.
    Preconditions: 0 <= num1 <= 100000, 0 <= num2 <= 100000, num1 > 0, num2 > 0, and num1 <> num2. -/
  theorem spec_12 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val) (hne : num1.val ≠ num2.val) :
      ∃ r r' : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧
          count_operations
            (toI64 (if num1.val > num2.val then num1.val - num2.val else num1.val))
            (toI64 (if num1.val > num2.val then num2.val else num2.val - num1.val)) = ok r' ∧
          r.val = r'.val + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val) (hne : num1.val ≠ num2.val), ∃ r r' : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧
            count_operations
              (toI64 (if num1.val > num2.val then num1.val - num2.val else num1.val))
              (toI64 (if num1.val > num2.val then num2.val else num2.val - num1.val)) = ok r' ∧
            r.val = r'.val + 1) := by
    sorry

  /-- The function returns a result r, and applying the operation (replace (x,y) by (x-y,y) if x >= y, otherwise by (x,y-x)) exactly r times to (num1,num2) gives a pair with one component equal to 0 and the other component equal to gcd(num1,num2).
    Preconditions: 0 <= num1 <= 100000, 0 <= num2 <= 100000, num1 > 0, and num2 > 0. -/
  theorem spec_13 (num1 num2 : Aeneas.Std.I64)
      (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
      (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
      (hp1 : 0 < num1.val) (hp2 : 0 < num2.val) :
      ∃ r : Aeneas.Std.I64,
        count_operations num1 num2 = ok r ∧
          ∃ n : ℕ, (n : ℤ) = r.val ∧ EndsInGcd num1.val num2.val n := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.I64)
        (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 100000)
        (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 100000)
        (hp1 : 0 < num1.val) (hp2 : 0 < num2.val), ∃ r : Aeneas.Std.I64,
          count_operations num1 num2 = ok r ∧
            ∃ n : ℕ, (n : ℤ) = r.val ∧ EndsInGcd num1.val num2.val n) := by
    sorry

  end AegisSpec.CountOperations
