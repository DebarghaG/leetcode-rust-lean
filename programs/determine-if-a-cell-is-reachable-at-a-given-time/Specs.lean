import Aegis.IsReachableAtTime.Code.Funs

/-!
# Specifications of `Aegis.IsReachableAtTime.is_reachable_at_time`

LeetCode problem `determine-if-a-cell-is-reachable-at-a-given-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsReachableAtTime

  open Aegis.IsReachableAtTime

  def iabs (x : ℤ) : ℤ := if x < 0 then -x else x

  def chebyshevDist (sx sy fx fy : ℤ) : ℤ := max (iabs (fx - sx)) (iabs (fy - sy))

  def sameCell (sx sy fx fy : ℤ) : Prop := sx = fx ∧ sy = fy

  def kingAdjacent (x1 y1 x2 y2 : ℤ) : Prop :=
    iabs (x2 - x1) ≤ 1 ∧ iabs (y2 - y1) ≤ 1 ∧ (x2 ≠ x1 ∨ y2 ≠ y1)

  def kingPath (sx sy fx fy : ℤ) (n : ℕ) : Prop :=
    ∃ p : ℕ → ℤ × ℤ,
      p 0 = (sx, sy) ∧ p n = (fx, fy) ∧
        ∀ i, i < n → kingAdjacent (p i).1 (p i).2 (p (i + 1)).1 (p (i + 1)).2

  def shiftI64 (x : Std.I64) (k : ℤ) (hlo : 1 ≤ x.val + k) (hhi : x.val + k ≤ 1000000000) :
      Std.I64 :=
    Aeneas.Std.IScalar.ofInt (ty := Aeneas.Std.IScalarTy.I64) (x.val + k) (hInBounds := by
      simp only [Aeneas.Std.IScalar.cMin, Aeneas.Std.IScalar.cMax, Aeneas.Std.IScalar.rMin,
        Aeneas.Std.IScalar.rMax, Aeneas.Std.I64.rMin, Aeneas.Std.I64.rMax]
      omega)

  theorem shiftI64_val (x : Std.I64) (k : ℤ) (h1 : 1 ≤ x.val + k) (h2 : x.val + k ≤ 1000000000) :
      (shiftI64 x k h1 h2).val = x.val + k := by
    simp only [shiftI64, Aeneas.Std.IScalar.ofInt]
    exact Aeneas.Std.IScalar.ofInt_val_eq _

  /-- Let d = max(|fx - sx|, |fy - sy|) and let same mean (sx = fx and sy = fy). The function returns Result.ok b for a Boolean b, and b = true if and only if d <= t and it is not the case that (same holds and t = 1). Equivalently, b = true iff either (same holds and (t = 0 or t >= 2)), or (not same and d <= t).
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_1 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
        (b = true ↔
          chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val ∧
            ¬ (sameCell sx.val sy.val fx.val fy.val ∧ t.val = 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
          (b = true ↔
            chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val ∧
              ¬ (sameCell sx.val sy.val fx.val fy.val ∧ t.val = 1))) := by
    sorry

  /-- The function returns Result.ok b for some Boolean b; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_2 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b) := by
    sorry

  /-- Let d = max(|fx - sx|, |fy - sy|). Whenever the function returns Result.ok b with b = true, we have d <= t.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_3 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      ∀ b : Bool, is_reachable_at_time sx sy fx fy t = ok b → b = true →
        chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), ∀ b : Bool, is_reachable_at_time sx sy fx fy t = ok b → b = true →
          chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val) := by
    sorry

  /-- Let d = max(|fx - sx|, |fy - sy|). The function returns Result.ok b for a Boolean b, and b = true if and only if d <= t.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, 0 <= t <= 1000000000, and not (sx = fx and sy = fy). -/
  theorem spec_4 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
      (hne : ¬ sameCell sx.val sy.val fx.val fy.val) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
        (b = true ↔ chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
        (hne : ¬ sameCell sx.val sy.val fx.val fy.val), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
          (b = true ↔ chebyshevDist sx.val sy.val fx.val fy.val ≤ t.val)) := by
    sorry

  /-- The function returns Result.ok b for a Boolean b, and b = true if and only if t != 1 (that is, t = 0 or t >= 2).
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, 0 <= t <= 1000000000, and sx = fx and sy = fy. -/
  theorem spec_5 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
      (hsame : sameCell sx.val sy.val fx.val fy.val) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
        (b = true ↔ t.val ≠ 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
        (hsame : sameCell sx.val sy.val fx.val fy.val), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
          (b = true ↔ t.val ≠ 1)) := by
    sorry

  /-- The function returns Result.ok b for a Boolean b, and b = true if and only if sx = fx and sy = fy.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and t = 0. -/
  theorem spec_6 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht : t.val = 0) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
        (b = true ↔ sameCell sx.val sy.val fx.val fy.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht : t.val = 0), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
          (b = true ↔ sameCell sx.val sy.val fx.val fy.val)) := by
    sorry

  /-- Let d = max(|fx - sx|, |fy - sy|). The function returns Result.ok b for a Boolean b, and b = true if and only if d = 1.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and t = 1. -/
  theorem spec_7 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht : t.val = 1) :
      ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
        (b = true ↔ chebyshevDist sx.val sy.val fx.val fy.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht : t.val = 1), ∃ b : Bool, is_reachable_at_time sx sy fx fy t = ok b ∧
          (b = true ↔ chebyshevDist sx.val sy.val fx.val fy.val = 1)) := by
    sorry

  /-- If is_reachable_at_time(sx, sy, fx, fy, t1) returns Result.ok true, then is_reachable_at_time(sx, sy, fx, fy, t2) returns Result.ok true.
    Preconditions: Fix sx, sy, fx, fy with 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and not (sx = fx and sy = fy). Let t1 and t2 be integers with 0 <= t1 <= t2 <= 1000000000. -/
  theorem spec_8 (sx sy fx fy t1 t2 : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (hne : ¬ sameCell sx.val sy.val fx.val fy.val)
      (ht1_lo : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ 1000000000) :
      is_reachable_at_time sx sy fx fy t1 = ok true →
        is_reachable_at_time sx sy fx fy t2 = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (sx sy fx fy t1 t2 : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (hne : ¬ sameCell sx.val sy.val fx.val fy.val)
        (ht1_lo : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ 1000000000), is_reachable_at_time sx sy fx fy t1 = ok true →
          is_reachable_at_time sx sy fx fy t2 = ok true) := by
    sorry

  /-- For every Boolean b, is_reachable_at_time(sx, sy, fx, fy, t) returns Result.ok b if and only if is_reachable_at_time(fx, fy, sx, sy, t) returns Result.ok b.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_9 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      ∀ b : Bool,
        (is_reachable_at_time sx sy fx fy t = ok b ↔
          is_reachable_at_time fx fy sx sy t = ok b) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), ∀ b : Bool,
          (is_reachable_at_time sx sy fx fy t = ok b ↔
            is_reachable_at_time fx fy sx sy t = ok b)) := by
    sorry

  /-- For every Boolean b, is_reachable_at_time(sx, sy, fx, fy, t) returns Result.ok b if and only if is_reachable_at_time(sy, sx, fy, fx, t) returns Result.ok b.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_10 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      ∀ b : Bool,
        (is_reachable_at_time sx sy fx fy t = ok b ↔
          is_reachable_at_time sy sx fy fx t = ok b) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), ∀ b : Bool,
          (is_reachable_at_time sx sy fx fy t = ok b ↔
            is_reachable_at_time sy sx fy fx t = ok b)) := by
    sorry

  /-- For every Boolean b, is_reachable_at_time(sx, sy, fx, fy, t) returns Result.ok b if and only if is_reachable_at_time(sx+K, sy+L, fx+K, fy+L, t) returns Result.ok b.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, 0 <= t <= 1000000000, and K and L are integers such that 1 <= sx+K <= 1000000000, 1 <= sy+L <= 1000000000, 1 <= fx+K <= 1000000000, and 1 <= fy+L <= 1000000000. -/
  theorem spec_11 (sx sy fx fy t : Std.I64) (K L : ℤ)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
      (hK_sx_lo : 1 ≤ sx.val + K) (hK_sx_hi : sx.val + K ≤ 1000000000)
      (hL_sy_lo : 1 ≤ sy.val + L) (hL_sy_hi : sy.val + L ≤ 1000000000)
      (hK_fx_lo : 1 ≤ fx.val + K) (hK_fx_hi : fx.val + K ≤ 1000000000)
      (hL_fy_lo : 1 ≤ fy.val + L) (hL_fy_hi : fy.val + L ≤ 1000000000) :
      ∀ b : Bool,
        (is_reachable_at_time sx sy fx fy t = ok b ↔
          is_reachable_at_time (shiftI64 sx K hK_sx_lo hK_sx_hi)
            (shiftI64 sy L hL_sy_lo hL_sy_hi) (shiftI64 fx K hK_fx_lo hK_fx_hi)
            (shiftI64 fy L hL_fy_lo hL_fy_hi) t = ok b) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64) (K L : ℤ)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000)
        (hK_sx_lo : 1 ≤ sx.val + K) (hK_sx_hi : sx.val + K ≤ 1000000000)
        (hL_sy_lo : 1 ≤ sy.val + L) (hL_sy_hi : sy.val + L ≤ 1000000000)
        (hK_fx_lo : 1 ≤ fx.val + K) (hK_fx_hi : fx.val + K ≤ 1000000000)
        (hL_fy_lo : 1 ≤ fy.val + L) (hL_fy_hi : fy.val + L ≤ 1000000000), ∀ b : Bool,
          (is_reachable_at_time sx sy fx fy t = ok b ↔
            is_reachable_at_time (shiftI64 sx K hK_sx_lo hK_sx_hi)
              (shiftI64 sy L hL_sy_lo hL_sy_hi) (shiftI64 fx K hK_fx_lo hK_fx_hi)
              (shiftI64 fy L hL_fy_lo hL_fy_hi) t = ok b)) := by
    sorry

  /-- Whenever is_reachable_at_time(sx, sy, fx, fy, t) returns Result.ok true, there exists a sequence of exactly t moves, each moving from the current cell to one of its 8 adjacent cells (cells sharing at least one corner), that starts at (sx, sy) and ends at (fx, fy); cells may be revisited.
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_12 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      is_reachable_at_time sx sy fx fy t = ok true →
        kingPath sx.val sy.val fx.val fy.val t.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), is_reachable_at_time sx sy fx fy t = ok true →
          kingPath sx.val sy.val fx.val fy.val t.val.toNat) := by
    sorry

  /-- Whenever is_reachable_at_time(sx, sy, fx, fy, t) returns Result.ok false, there is no sequence of exactly t moves, each moving from the current cell to one of its 8 adjacent cells (cells sharing at least one corner), that starts at (sx, sy) and ends at (fx, fy).
    Preconditions: 1 <= sx <= 1000000000, 1 <= sy <= 1000000000, 1 <= fx <= 1000000000, 1 <= fy <= 1000000000, and 0 <= t <= 1000000000. -/
  theorem spec_13 (sx sy fx fy t : Std.I64)
      (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
      (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
      (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
      (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
      (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000) :
      is_reachable_at_time sx sy fx fy t = ok false →
        ¬ kingPath sx.val sy.val fx.val fy.val t.val.toNat := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (sx sy fx fy t : Std.I64)
        (hsx_lo : 1 ≤ sx.val) (hsx_hi : sx.val ≤ 1000000000)
        (hsy_lo : 1 ≤ sy.val) (hsy_hi : sy.val ≤ 1000000000)
        (hfx_lo : 1 ≤ fx.val) (hfx_hi : fx.val ≤ 1000000000)
        (hfy_lo : 1 ≤ fy.val) (hfy_hi : fy.val ≤ 1000000000)
        (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ 1000000000), is_reachable_at_time sx sy fx fy t = ok false →
          ¬ kingPath sx.val sy.val fx.val fy.val t.val.toNat) := by
    sorry

  end AegisSpec.IsReachableAtTime
