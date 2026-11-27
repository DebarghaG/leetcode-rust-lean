import Aegis.ComputeArea.Code.Funs

/-!
# Specifications of `Aegis.ComputeArea.compute_area`

LeetCode problem `rectangle-area`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ComputeArea

def InI64 (x : ℤ) : Prop := Aeneas.Std.I64.min ≤ x ∧ x ≤ Aeneas.Std.I64.max

/-- The function returns a result r and r = areaA + areaB - W * H, where areaA = (ax2 - ax1) * (ay2 - ay1), areaB = (bx2 - bx1) * (by2 - by1), W = max(0, min(ax2, bx2) - max(ax1, bx1)), and H = max(0, min(ay2, by2) - max(ay1, by1)). Here max and min are the usual integer maximum and minimum.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_1 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∃ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r ∧
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val)
            - max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
              * max 0 (min ay2.val by2.val - max ay1.val by1.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∃ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r ∧
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val)
            - max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
              * max 0 (min ay2.val by2.val - max ay1.val by1.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or report overflow. All arithmetic needed to form the sides (ax2-ax1), (ay2-ay1), (bx2-bx1), (by2-by1), their products, and the final union area stays within the signed 64-bit range.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_2 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∃ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r ∧

      InI64 (ax2.val - ax1.val) ∧ InI64 (ay2.val - ay1.val) ∧
      InI64 (bx2.val - bx1.val) ∧ InI64 (by2.val - by1.val) ∧

      InI64 ((ax2.val - ax1.val) * (ay2.val - ay1.val)) ∧
      InI64 ((bx2.val - bx1.val) * (by2.val - by1.val)) ∧

      InI64 (max 0 (min ax2.val bx2.val - max ax1.val bx1.val)) ∧
      InI64 (max 0 (min ay2.val by2.val - max ay1.val by1.val)) ∧
      InI64 (max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
        * max 0 (min ay2.val by2.val - max ay1.val by1.val)) ∧

      InI64 ((ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val)) ∧
      InI64 r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∃ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r ∧

      InI64 (ax2.val - ax1.val) ∧ InI64 (ay2.val - ay1.val) ∧
      InI64 (bx2.val - bx1.val) ∧ InI64 (by2.val - by1.val) ∧

      InI64 ((ax2.val - ax1.val) * (ay2.val - ay1.val)) ∧
      InI64 ((bx2.val - bx1.val) * (by2.val - by1.val)) ∧

      InI64 (max 0 (min ax2.val bx2.val - max ax1.val bx1.val)) ∧
      InI64 (max 0 (min ay2.val by2.val - max ay1.val by1.val)) ∧
      InI64 (max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
        * max 0 (min ay2.val by2.val - max ay1.val by1.val)) ∧

      InI64 ((ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val)) ∧
      InI64 r.val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= (max(ax2, bx2) - min(ax1, bx1)) * (max(ay2, by2) - min(ay1, by1)) <= 400000000, where max and min are the usual integer maximum and minimum.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_3 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      0 ≤ r.val ∧
      r.val ≤ (max ax2.val bx2.val - min ax1.val bx1.val)
        * (max ay2.val by2.val - min ay1.val by1.val) ∧
      (max ax2.val bx2.val - min ax1.val bx1.val)
        * (max ay2.val by2.val - min ay1.val by1.val) ≤ 400000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      0 ≤ r.val ∧
      r.val ≤ (max ax2.val bx2.val - min ax1.val bx1.val)
        * (max ay2.val by2.val - min ay1.val by1.val) ∧
      (max ax2.val bx2.val - min ax1.val bx1.val)
        * (max ay2.val by2.val - min ay1.val by1.val) ≤ 400000000) := by
  sorry

/-- Whenever the function returns a result r, r >= (ax2 - ax1) * (ay2 - ay1) and r >= (bx2 - bx1) * (by2 - by1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_4 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax2.val - ax1.val) * (ay2.val - ay1.val) ≤ r.val ∧
      (bx2.val - bx1.val) * (by2.val - by1.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax2.val - ax1.val) * (ay2.val - ay1.val) ≤ r.val ∧
      (bx2.val - bx1.val) * (by2.val - by1.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (ax2 - ax1) * (ay2 - ay1) + (bx2 - bx1) * (by2 - by1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_5 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      r.val ≤ (ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      r.val ≤ (ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val)) := by
  sorry

/-- Whenever the function returns a result r, if ax2 <= bx1 or bx2 <= ax1 or ay2 <= by1 or by2 <= ay1, then r = (ax2 - ax1) * (ay2 - ay1) + (bx2 - bx1) * (by2 - by1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_6 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax2.val ≤ bx1.val ∨ bx2.val ≤ ax1.val ∨ ay2.val ≤ by1.val ∨ by2.val ≤ ay1.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax2.val ≤ bx1.val ∨ bx2.val ≤ ax1.val ∨ ay2.val ≤ by1.val ∨ by2.val ≤ ay1.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
        + (bx2.val - bx1.val) * (by2.val - by1.val)) := by
  sorry

/-- Whenever the function returns a result r, if bx1 <= ax1 and by1 <= ay1 and ax2 <= bx2 and ay2 <= by2, then r = (bx2 - bx1) * (by2 - by1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_7 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (bx1.val ≤ ax1.val ∧ by1.val ≤ ay1.val ∧ ax2.val ≤ bx2.val ∧ ay2.val ≤ by2.val) →
      r.val = (bx2.val - bx1.val) * (by2.val - by1.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (bx1.val ≤ ax1.val ∧ by1.val ≤ ay1.val ∧ ax2.val ≤ bx2.val ∧ ay2.val ≤ by2.val) →
      r.val = (bx2.val - bx1.val) * (by2.val - by1.val)) := by
  sorry

/-- Whenever the function returns a result r, if ax1 <= bx1 and ay1 <= by1 and bx2 <= ax2 and by2 <= ay2, then r = (ax2 - ax1) * (ay2 - ay1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_8 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax1.val ≤ bx1.val ∧ ay1.val ≤ by1.val ∧ bx2.val ≤ ax2.val ∧ by2.val ≤ ay2.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax1.val ≤ bx1.val ∧ ay1.val ≤ by1.val ∧ bx2.val ≤ ax2.val ∧ by2.val ≤ ay2.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)) := by
  sorry

/-- Whenever the function returns a result r, if ax1 = ax2 or ay1 = ay2, then r = (bx2 - bx1) * (by2 - by1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_9 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax1.val = ax2.val ∨ ay1.val = ay2.val) →
      r.val = (bx2.val - bx1.val) * (by2.val - by1.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (ax1.val = ax2.val ∨ ay1.val = ay2.val) →
      r.val = (bx2.val - bx1.val) * (by2.val - by1.val)) := by
  sorry

/-- Whenever the function returns a result r, if bx1 = bx2 or by1 = by2, then r = (ax2 - ax1) * (ay2 - ay1).
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_10 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (bx1.val = bx2.val ∨ by1.val = by2.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (bx1.val = bx2.val ∨ by1.val = by2.val) →
      r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)) := by
  sorry

/-- Let r be the result of compute_area(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2). Then the result of compute_area(bx1, by1, bx2, by2, ax1, ay1, ax2, ay2) is also r; that is, exchanging the two rectangles does not change the answer.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_11 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r r', Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      Aegis.ComputeArea.compute_area bx1 by1 bx2 by2 ax1 ay1 ax2 ay2 = ok r' →
      r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r r', Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      Aegis.ComputeArea.compute_area bx1 by1 bx2 by2 ax1 ay1 ax2 ay2 = ok r' →
      r = r') := by
  sorry

/-- For every such dx and dy, if r is the result for the original input and r' is the result for the shifted input, then r = r'.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. Also dx and dy are integers such that the shifted tuple (ax1+dx, ay1+dy, ax2+dx, ay2+dy, bx1+dx, by1+dy, bx2+dx, by2+dy) also satisfies the same constraints: -10000 <= ax1+dx <= ax2+dx <= 10000, -10000 <= ay1+dy <= ay2+dy <= 10000, -10000 <= bx1+dx <= bx2+dx <= 10000, and -10000 <= by1+dy <= by2+dy <= 10000. -/
theorem spec_12 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000)
    (dx dy : ℤ) (ax1s ay1s ax2s ay2s bx1s by1s bx2s by2s : Std.I64)
    (hsax1 : ax1s.val = ax1.val + dx) (hsay1 : ay1s.val = ay1.val + dy)
    (hsax2 : ax2s.val = ax2.val + dx) (hsay2 : ay2s.val = ay2.val + dy)
    (hsbx1 : bx1s.val = bx1.val + dx) (hsby1 : by1s.val = by1.val + dy)
    (hsbx2 : bx2s.val = bx2.val + dx) (hsby2 : by2s.val = by2.val + dy)
    (hshax1 : -10000 ≤ ax1s.val) (hshax12 : ax1s.val ≤ ax2s.val) (hshax2 : ax2s.val ≤ 10000)
    (hshay1 : -10000 ≤ ay1s.val) (hshay12 : ay1s.val ≤ ay2s.val) (hshay2 : ay2s.val ≤ 10000)
    (hshbx1 : -10000 ≤ bx1s.val) (hshbx12 : bx1s.val ≤ bx2s.val) (hshbx2 : bx2s.val ≤ 10000)
    (hshby1 : -10000 ≤ by1s.val) (hshby12 : by1s.val ≤ by2s.val) (hshby2 : by2s.val ≤ 10000) :
    ∀ r r', Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      Aegis.ComputeArea.compute_area ax1s ay1s ax2s ay2s bx1s by1s bx2s by2s = ok r' →
      r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000)
    (dx dy : ℤ) (ax1s ay1s ax2s ay2s bx1s by1s bx2s by2s : Std.I64)
    (hsax1 : ax1s.val = ax1.val + dx) (hsay1 : ay1s.val = ay1.val + dy)
    (hsax2 : ax2s.val = ax2.val + dx) (hsay2 : ay2s.val = ay2.val + dy)
    (hsbx1 : bx1s.val = bx1.val + dx) (hsby1 : by1s.val = by1.val + dy)
    (hsbx2 : bx2s.val = bx2.val + dx) (hsby2 : by2s.val = by2.val + dy)
    (hshax1 : -10000 ≤ ax1s.val) (hshax12 : ax1s.val ≤ ax2s.val) (hshax2 : ax2s.val ≤ 10000)
    (hshay1 : -10000 ≤ ay1s.val) (hshay12 : ay1s.val ≤ ay2s.val) (hshay2 : ay2s.val ≤ 10000)
    (hshbx1 : -10000 ≤ bx1s.val) (hshbx12 : bx1s.val ≤ bx2s.val) (hshbx2 : bx2s.val ≤ 10000)
    (hshby1 : -10000 ≤ by1s.val) (hshby12 : by1s.val ≤ by2s.val) (hshby2 : by2s.val ≤ 10000), ∀ r r', Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      Aegis.ComputeArea.compute_area ax1s ay1s ax2s ay2s bx1s by1s bx2s by2s = ok r' →
      r = r') := by
  sorry

/-- Whenever the function returns a result r, let I = (ax2 - ax1) * (ay2 - ay1) + (bx2 - bx1) * (by2 - by1) - r. Then 0 <= I <= min((ax2 - ax1) * (ay2 - ay1), (bx2 - bx1) * (by2 - by1)), where min is the usual integer minimum.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_13 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      0 ≤ (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val) - r.val ∧
      (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val) - r.val ≤
        min ((ax2.val - ax1.val) * (ay2.val - ay1.val))
          ((bx2.val - bx1.val) * (by2.val - by1.val)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      0 ≤ (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val) - r.val ∧
      (ax2.val - ax1.val) * (ay2.val - ay1.val)
            + (bx2.val - bx1.val) * (by2.val - by1.val) - r.val ≤
        min ((ax2.val - ax1.val) * (ay2.val - ay1.val))
          ((bx2.val - bx1.val) * (by2.val - by1.val))) := by
  sorry

/-- Whenever the function returns a result r, r = (ax2 - ax1) * (ay2 - ay1) + (bx2 - bx1) * (by2 - by1) if and only if max(0, min(ax2, bx2) - max(ax1, bx1)) * max(0, min(ay2, by2) - max(ay1, by1)) = 0. Here max and min are the usual integer maximum and minimum.
  Preconditions: ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 are integers satisfying -10000 <= ax1 <= ax2 <= 10000, -10000 <= ay1 <= ay2 <= 10000, -10000 <= bx1 <= bx2 <= 10000, and -10000 <= by1 <= by2 <= 10000. -/
theorem spec_14 (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000) :
    ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
          + (bx2.val - bx1.val) * (by2.val - by1.val) ↔
        max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
          * max 0 (min ay2.val by2.val - max ay1.val by1.val) = 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : Std.I64)
    (hax1 : -10000 ≤ ax1.val) (hax12 : ax1.val ≤ ax2.val) (hax2 : ax2.val ≤ 10000)
    (hay1 : -10000 ≤ ay1.val) (hay12 : ay1.val ≤ ay2.val) (hay2 : ay2.val ≤ 10000)
    (hbx1 : -10000 ≤ bx1.val) (hbx12 : bx1.val ≤ bx2.val) (hbx2 : bx2.val ≤ 10000)
    (hby1 : -10000 ≤ by1.val) (hby12 : by1.val ≤ by2.val) (hby2 : by2.val ≤ 10000), ∀ r, Aegis.ComputeArea.compute_area ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 = ok r →
      (r.val = (ax2.val - ax1.val) * (ay2.val - ay1.val)
          + (bx2.val - bx1.val) * (by2.val - by1.val) ↔
        max 0 (min ax2.val bx2.val - max ax1.val bx1.val)
          * max 0 (min ay2.val by2.val - max ay1.val by1.val) = 0)) := by
  sorry

end AegisSpec.ComputeArea
