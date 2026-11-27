import Aegis.ReachingPoints.Code.Funs

/-!
# Specifications of `Aegis.ReachingPoints.reaching_points`

LeetCode problem `reaching-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.ReachingPoints (reaching_points)

  namespace AegisSpec.ReachingPoints

  def InRange (x : I64) : Prop := 1 ≤ x.val ∧ x.val ≤ 10 ^ 9

  def mkI64 (n : ℤ) (h : -(2 ^ 63) ≤ n ∧ n ≤ 2 ^ 63 - 1) : I64 :=
    I64.ofInt n (by
      obtain ⟨h1, h2⟩ := h
      simp only [Aeneas.Std.IScalar.cMin, Aeneas.Std.IScalar.cMax, Aeneas.Std.IScalar.rMin,
        Aeneas.Std.IScalar.rMax, Aeneas.Std.I64.rMin, Aeneas.Std.I64.rMax]
      constructor <;> omega)

  def Step (p q : ℤ × ℤ) : Prop :=
    q = (p.1, p.1 + p.2) ∨ q = (p.1 + p.2, p.2)

  def Reachable (p q : ℤ × ℤ) : Prop :=
    ∃ n : ℕ, ∃ f : Fin (n + 1) → ℤ × ℤ,
      f 0 = p ∧ f ⟨n, Nat.lt_succ_self n⟩ = q ∧ ∀ i : Fin n, Step (f i.castSucc) (f i.succ)

  /-- The function returns a result r (so it does not fail), and r = true if and only if there exists an integer n >= 0 and a finite sequence of ordered pairs of integers (x_0, y_0), ..., (x_n, y_n) such that (x_0, y_0) = (sx, sy), (x_n, y_n) = (tx, ty), and for every i with 0 <= i < n, either (x_{i+1}, y_{i+1}) = (x_i, x_i + y_i) or (x_{i+1}, y_{i+1}) = (x_i + y_i, y_i). Equivalently, r = false exactly when no such sequence exists.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_1 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) :
      ∃ r : Bool, reaching_points sx sy tx ty = ok r ∧
        (r = true ↔ Reachable (sx.val, sy.val) (tx.val, ty.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty), ∃ r : Bool, reaching_points sx sy tx ty = ok r ∧
          (r = true ↔ Reachable (sx.val, sy.val) (tx.val, ty.val))) := by
    sorry

  /-- For every input satisfying the preconditions, reaching_points(sx, sy, tx, ty) returns a result r and does not fail: there is no arithmetic overflow, division by zero, out-of-bounds access, or panic.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_2 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) :
      ∃ r : Bool, reaching_points sx sy tx ty = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty), ∃ r : Bool, reaching_points sx sy tx ty = ok r) := by
    sorry

  /-- If tx < sx or ty < sy, then the function returns false.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_3 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (h : tx.val < sx.val ∨ ty.val < sy.val) :
      reaching_points sx sy tx ty = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (h : tx.val < sx.val ∨ ty.val < sy.val), reaching_points sx sy tx ty = ok false) := by
    sorry

  /-- If gcd(sx, sy) != gcd(tx, ty), then the function returns false, where gcd denotes the greatest common divisor of two positive integers.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_4 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (h : Int.gcd sx.val sy.val ≠ Int.gcd tx.val ty.val) :
      reaching_points sx sy tx ty = ok false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (h : Int.gcd sx.val sy.val ≠ Int.gcd tx.val ty.val), reaching_points sx sy tx ty = ok false) := by
    sorry

  /-- If (tx, ty) != (sx, sy) and tx + ty <= sx + sy, then the function returns false.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_5 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (hne : (tx.val, ty.val) ≠ (sx.val, sy.val))
      (hsum : tx.val + ty.val ≤ sx.val + sy.val) :
      reaching_points sx sy tx ty = ok false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (hne : (tx.val, ty.val) ≠ (sx.val, sy.val))
        (hsum : tx.val + ty.val ≤ sx.val + sy.val), reaching_points sx sy tx ty = ok false) := by
    sorry

  /-- If tx = sx and ty = sy, then the function returns true.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_6 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (hx : tx.val = sx.val) (hy : ty.val = sy.val) :
      reaching_points sx sy tx ty = ok true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (hx : tx.val = sx.val) (hy : ty.val = sy.val), reaching_points sx sy tx ty = ok true) := by
    sorry

  /-- If tx = sx, then the function returns true if and only if ty >= sy and there exists an integer k >= 0 such that ty = sy + k * sx; otherwise it returns false.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_7 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (hx : tx.val = sx.val) :
      (reaching_points sx sy tx ty = ok true ↔
          sy.val ≤ ty.val ∧ ∃ k : ℕ, ty.val = sy.val + (k : ℤ) * sx.val) ∧
        (reaching_points sx sy tx ty = ok false ↔
          ¬ (sy.val ≤ ty.val ∧ ∃ k : ℕ, ty.val = sy.val + (k : ℤ) * sx.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (hx : tx.val = sx.val), (reaching_points sx sy tx ty = ok true ↔
            sy.val ≤ ty.val ∧ ∃ k : ℕ, ty.val = sy.val + (k : ℤ) * sx.val) ∧
          (reaching_points sx sy tx ty = ok false ↔
            ¬ (sy.val ≤ ty.val ∧ ∃ k : ℕ, ty.val = sy.val + (k : ℤ) * sx.val))) := by
    sorry

  /-- If ty = sy, then the function returns true if and only if tx >= sx and there exists an integer k >= 0 such that tx = sx + k * sy; otherwise it returns false.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_8 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (hy : ty.val = sy.val) :
      (reaching_points sx sy tx ty = ok true ↔
          sx.val ≤ tx.val ∧ ∃ k : ℕ, tx.val = sx.val + (k : ℤ) * sy.val) ∧
        (reaching_points sx sy tx ty = ok false ↔
          ¬ (sx.val ≤ tx.val ∧ ∃ k : ℕ, tx.val = sx.val + (k : ℤ) * sy.val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (hy : ty.val = sy.val), (reaching_points sx sy tx ty = ok true ↔
            sx.val ≤ tx.val ∧ ∃ k : ℕ, tx.val = sx.val + (k : ℤ) * sy.val) ∧
          (reaching_points sx sy tx ty = ok false ↔
            ¬ (sx.val ≤ tx.val ∧ ∃ k : ℕ, tx.val = sx.val + (k : ℤ) * sy.val))) := by
    sorry

  /-- If sx = sy, then the function returns true if and only if gcd(tx, ty) = sx; otherwise it returns false.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_9 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (h : sx.val = sy.val) :
      (reaching_points sx sy tx ty = ok true ↔ (Int.gcd tx.val ty.val : ℤ) = sx.val) ∧
        (reaching_points sx sy tx ty = ok false ↔ (Int.gcd tx.val ty.val : ℤ) ≠ sx.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (h : sx.val = sy.val), (reaching_points sx sy tx ty = ok true ↔ (Int.gcd tx.val ty.val : ℤ) = sx.val) ∧
          (reaching_points sx sy tx ty = ok false ↔ (Int.gcd tx.val ty.val : ℤ) ≠ sx.val)) := by
    sorry

  /-- The function returns the same Boolean value on (sx, sy, tx, ty) as on (sy, sx, ty, tx): if r1 is the result on the first quadruple and r2 is the result on the second, then r1 = r2.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9. -/
  theorem spec_10 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) :
      ∃ r1 r2 : Bool, reaching_points sx sy tx ty = ok r1 ∧
        reaching_points sy sx ty tx = ok r2 ∧ r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty), ∃ r1 r2 : Bool, reaching_points sx sy tx ty = ok r1 ∧
          reaching_points sy sx ty tx = ok r2 ∧ r1 = r2) := by
    sorry

  /-- The function returns the same Boolean value on (sx, sy, tx, ty) as on (c*sx, c*sy, c*tx, c*ty).
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9; c is a positive integer such that c*sx, c*sy, c*tx, c*ty are all at most 10^9. -/
  theorem spec_11 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (c : ℤ) (hc : 1 ≤ c)
      (hcsx : c * sx.val ≤ 10 ^ 9) (hcsy : c * sy.val ≤ 10 ^ 9) (hctx : c * tx.val ≤ 10 ^ 9)
      (hcty : c * ty.val ≤ 10 ^ 9) :
      ∃ r1 r2 : Bool, reaching_points sx sy tx ty = ok r1 ∧
        reaching_points
            (mkI64 (c * sx.val) (by
              have h1 := hsx.1
              constructor <;> nlinarith))
            (mkI64 (c * sy.val) (by
              have h1 := hsy.1
              constructor <;> nlinarith))
            (mkI64 (c * tx.val) (by
              have h1 := htx.1
              constructor <;> nlinarith))
            (mkI64 (c * ty.val) (by
              have h1 := hty.1
              constructor <;> nlinarith)) = ok r2 ∧
        r1 = r2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (c : ℤ) (hc : 1 ≤ c)
        (hcsx : c * sx.val ≤ 10 ^ 9) (hcsy : c * sy.val ≤ 10 ^ 9) (hctx : c * tx.val ≤ 10 ^ 9)
        (hcty : c * ty.val ≤ 10 ^ 9), ∃ r1 r2 : Bool, reaching_points sx sy tx ty = ok r1 ∧
          reaching_points
              (mkI64 (c * sx.val) (by
                have h1 := hsx.1
                constructor <;> nlinarith))
              (mkI64 (c * sy.val) (by
                have h1 := hsy.1
                constructor <;> nlinarith))
              (mkI64 (c * tx.val) (by
                have h1 := htx.1
                constructor <;> nlinarith))
              (mkI64 (c * ty.val) (by
                have h1 := hty.1
                constructor <;> nlinarith)) = ok r2 ∧
          r1 = r2) := by
    sorry

  /-- If reaching_points(sx, sy, mx, my) returns true and reaching_points(mx, my, tx, ty) returns true, then reaching_points(sx, sy, tx, ty) returns true.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9; mx and my are integers with 1 <= mx <= 10^9 and 1 <= my <= 10^9. -/
  theorem spec_12 (sx sy tx ty mx my : I64) (hsx : InRange sx) (hsy : InRange sy)
      (htx : InRange tx) (hty : InRange ty) (hmx : InRange mx) (hmy : InRange my)
      (h1 : reaching_points sx sy mx my = ok true) (h2 : reaching_points mx my tx ty = ok true) :
      reaching_points sx sy tx ty = ok true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (sx sy tx ty mx my : I64) (hsx : InRange sx) (hsy : InRange sy)
        (htx : InRange tx) (hty : InRange ty) (hmx : InRange mx) (hmy : InRange my)
        (h1 : reaching_points sx sy mx my = ok true) (h2 : reaching_points mx my tx ty = ok true), reaching_points sx sy tx ty = ok true) := by
    sorry

  /-- If tx > ty, then reaching_points(sx, sy, tx, ty) returns true if and only if reaching_points(sx, sy, tx - ty, ty) returns true; if ty > tx, then it returns true if and only if reaching_points(sx, sy, tx, ty - tx) returns true.
    Preconditions: 1 <= sx, sy, tx, ty <= 10^9 and (tx, ty) != (sx, sy). -/
  theorem spec_13 (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
      (hty : InRange ty) (hne : (tx.val, ty.val) ≠ (sx.val, sy.val)) :
      (ty.val < tx.val →
          (reaching_points sx sy tx ty = ok true ↔
            reaching_points sx sy
              (mkI64 (tx.val - ty.val) (by
                have h1 := htx.1
                have h2 := htx.2
                have h3 := hty.1
                have h4 := hty.2
                omega)) ty = ok true)) ∧
        (tx.val < ty.val →
          (reaching_points sx sy tx ty = ok true ↔
            reaching_points sx sy tx
              (mkI64 (ty.val - tx.val) (by
                have h1 := htx.1
                have h2 := hty.2
                have h3 := hty.1
                have h4 := htx.2
                omega)) = ok true)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (sx sy tx ty : I64) (hsx : InRange sx) (hsy : InRange sy) (htx : InRange tx)
        (hty : InRange ty) (hne : (tx.val, ty.val) ≠ (sx.val, sy.val)), (ty.val < tx.val →
            (reaching_points sx sy tx ty = ok true ↔
              reaching_points sx sy
                (mkI64 (tx.val - ty.val) (by
                  have h1 := htx.1
                  have h2 := htx.2
                  have h3 := hty.1
                  have h4 := hty.2
                  omega)) ty = ok true)) ∧
          (tx.val < ty.val →
            (reaching_points sx sy tx ty = ok true ↔
              reaching_points sx sy tx
                (mkI64 (ty.val - tx.val) (by
                  have h1 := htx.1
                  have h2 := hty.2
                  have h3 := hty.1
                  have h4 := htx.2
                  omega)) = ok true))) := by
    sorry

  end AegisSpec.ReachingPoints
