import Aegis.MinKnightMoves.Code.Funs

/-!
# Specifications of `Aegis.MinKnightMoves.min_knight_moves`

LeetCode problem `minimum-knight-moves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinKnightMoves

  namespace AegisSpec.MinKnightMoves

  def IsKnightMove (dx dy : ℤ) : Prop :=
    (|dx| = 1 ∧ |dy| = 2) ∨ (|dx| = 2 ∧ |dy| = 1)

  def IsKnightSeq (l : List (ℤ × ℤ)) : Prop :=
    ∀ p ∈ l, IsKnightMove p.1 p.2

  def KnightSeqSum (l : List (ℤ × ℤ)) (x y : ℤ) : Prop :=
    (l.map (fun p => p.1)).sum = x ∧ (l.map (fun p => p.2)).sum = y

  def KnightReach (n : ℕ) (x y : ℤ) : Prop :=
    ∃ l : List (ℤ × ℤ), l.length = n ∧ IsKnightSeq l ∧ KnightSeqSum l x y

  def absI64 (x : Std.I64) (h : |x.val| ≤ 300) : Std.I64 :=
    Std.I64.ofInt |x.val| (by
      have h0 : (0 : ℤ) ≤ |x.val| := abs_nonneg _
      rw [IScalar.cMin_I64_eq, IScalar.cMax_I64_eq]
      omega)

  /-- Whenever the function returns a result r, r is the smallest non-negative integer n such that there exists a sequence of n knight moves from (0,0) to (x,y). A knight move is a pair (dx,dy) of integers with {|dx|,|dy|} = {1,2}. A sequence of n knight moves (dx_1,dy_1),...,(dx_n,dy_n) goes from (0,0) to (x,y) if sum_{i=1}^n dx_i = x and sum_{i=1}^n dy_i = y.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_1 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r →
        0 ≤ r.val ∧ KnightReach r.val.toNat x.val y.val ∧
          ∀ n : ℕ, (n : ℤ) < r.val → ¬ KnightReach n x.val y.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r →
          0 ≤ r.val ∧ KnightReach r.val.toNat x.val y.val ∧
            ∀ n : ℕ, (n : ℤ) < r.val → ¬ KnightReach n x.val y.val) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic).
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_2 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∃ r : Std.I64, min_knight_moves x y = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∃ r : Std.I64, min_knight_moves x y = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists a sequence of r knight moves from (0,0) to (x,y), where a knight move is a pair (dx,dy) of integers with {|dx|,|dy|} = {1,2}, and the sequence sums to (x,y).
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_3 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → KnightReach r.val.toNat x.val y.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → KnightReach r.val.toNat x.val y.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer n with 0 <= n < r, there does not exist a sequence of n knight moves from (0,0) to (x,y), where a knight move is a pair (dx,dy) of integers with {|dx|,|dy|} = {1,2}.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_4 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r →
        ∀ n : ℕ, (n : ℤ) < r.val → ¬ KnightReach n x.val y.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r →
          ∀ n : ℕ, (n : ℤ) < r.val → ¬ KnightReach n x.val y.val) := by
    sorry

  /-- Whenever the function returns a result r, 2*r >= |x| and 2*r >= |y|.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_5 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r →
        |x.val| ≤ 2 * r.val ∧ |y.val| ≤ 2 * r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r →
          |x.val| ≤ 2 * r.val ∧ |y.val| ≤ 2 * r.val) := by
    sorry

  /-- Whenever the function returns a result r, 3*r >= |x| + |y|.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_6 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| ≤ 3 * r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| ≤ 3 * r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= |x| + |y| + 2.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_7 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → r.val ≤ |x.val| + |y.val| + 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → r.val ≤ |x.val| + |y.val| + 2) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if x = 0 and y = 0.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_8 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → (r.val = 0 ↔ x.val = 0 ∧ y.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → (r.val = 0 ↔ x.val = 0 ∧ y.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if |x| + |y| = 1, then r = 3.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_9 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| = 1 → r.val = 3 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| = 1 → r.val = 3) := by
    sorry

  /-- Whenever the function returns a result r, if |x| + |y| = 2, then r = 2.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_10 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| = 2 → r.val = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| + |y.val| = 2 → r.val = 2) := by
    sorry

  /-- Whenever the function returns a result r, if |x| = 2 and |y| = 2, then r = 4.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_11 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| = 2 → |y.val| = 2 → r.val = 4 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → |x.val| = 2 → |y.val| = 2 → r.val = 4) := by
    sorry

  /-- Whenever the function returns a result r, r and x + y have the same parity, i.e., 2 divides (r - (x + y)).
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_12 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → (2 : ℤ) ∣ r.val - (x.val + y.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → (2 : ℤ) ∣ r.val - (x.val + y.val)) := by
    sorry

  /-- For every x, y satisfying the preconditions, the value returned for (x,y) equals the value returned for (|x|,|y|) and equals the value returned for (y,x).
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_13 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      min_knight_moves x y
          = min_knight_moves (absI64 x (by
              have h0 : (0 : ℤ) ≤ |y.val| := abs_nonneg _
              omega))
            (absI64 y (by
              have h0 : (0 : ℤ) ≤ |x.val| := abs_nonneg _
              omega)) ∧
        min_knight_moves x y = min_knight_moves y x := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), min_knight_moves x y
            = min_knight_moves (absI64 x (by
                have h0 : (0 : ℤ) ≤ |y.val| := abs_nonneg _
                omega))
              (absI64 y (by
                have h0 : (0 : ℤ) ≤ |x.val| := abs_nonneg _
                omega)) ∧
          min_knight_moves x y = min_knight_moves y x) := by
    sorry

  /-- Whenever the function returns a result r, r <= 151.
    Preconditions: -300 <= x <= 300, -300 <= y <= 300, and |x| + |y| <= 300. -/
  theorem spec_14 (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
      (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300) :
      ∀ r : Std.I64, min_knight_moves x y = ok r → r.val ≤ 151 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (x y : Std.I64) (hx_lo : -300 ≤ x.val) (hx_hi : x.val ≤ 300)
        (hy_lo : -300 ≤ y.val) (hy_hi : y.val ≤ 300) (hxy : |x.val| + |y.val| ≤ 300), ∀ r : Std.I64, min_knight_moves x y = ok r → r.val ≤ 151) := by
    sorry

  end AegisSpec.MinKnightMoves
