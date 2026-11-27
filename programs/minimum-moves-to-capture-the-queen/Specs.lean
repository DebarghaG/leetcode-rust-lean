import Aegis.MinMovesToCaptureTheQueen.Code.Funs

/-!
# Specifications of `Aegis.MinMovesToCaptureTheQueen.min_moves_to_capture_the_queen`

LeetCode problem `minimum-moves-to-capture-the-queen`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinMovesToCaptureTheQueen

namespace AegisSpec.MinMovesToCaptureTheQueen

def rookBlocked (a b c d e f : I64) : Prop :=
  (a.val = e.val ∧ c.val = a.val ∧
      ((b.val < d.val ∧ d.val < f.val) ∨ (f.val < d.val ∧ d.val < b.val))) ∨
    (b.val = f.val ∧ d.val = b.val ∧
      ((a.val < c.val ∧ c.val < e.val) ∨ (e.val < c.val ∧ c.val < a.val)))

def rookCan (a b c d e f : I64) : Prop :=
  (a.val = e.val ∨ b.val = f.val) ∧ ¬ rookBlocked a b c d e f

def bishopBlocked (a b c d e f : I64) : Prop :=
  |a.val - c.val| = |b.val - d.val| ∧
    min c.val e.val < a.val ∧ a.val < max c.val e.val ∧
      min d.val f.val < b.val ∧ b.val < max d.val f.val

def bishopCan (a b c d e f : I64) : Prop :=
  |c.val - e.val| = |d.val - f.val| ∧ ¬ bishopBlocked a b c d e f

def reflect (x : I64) (h₁ : 1 ≤ x.val) (h₂ : x.val ≤ 8) : I64 :=
  I64.ofInt (9 - x.val) (by scalar_tac)

@[simp]
theorem reflect_val (x : I64) (h₁ : 1 ≤ x.val) (h₂ : x.val ≤ 8) :
    (reflect x h₁ h₂).val = 9 - x.val := by
  unfold reflect
  scalar_tac

theorem reflect_bounds (x : I64) (h₁ : 1 ≤ x.val) (h₂ : x.val ≤ 8) :
    1 ≤ (reflect x h₁ h₂).val ∧ (reflect x h₁ h₂).val ≤ 8 := by
  rw [reflect_val]
  omega

/-- The function returns a result r such that r = 1 if and only if either (A) (a = e or b = f) and not ((a = e and c = a and ((b < d and d < f) or (f < d and d < b))) or (b = f and d = b and ((a < c and c < e) or (e < c and c < a))) ), or (B) |c - e| = |d - f| and not ( |a - c| = |b - d| and min(c,e) < a < max(c,e) and min(d,f) < b < max(d,f) ). Otherwise, r = 2.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_1 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)) :
    ∃ r : I64,
      min_moves_to_capture_the_queen a b c d e f = ok r ∧
        (r.val = 1 ↔ rookCan a b c d e f ∨ bishopCan a b c d e f) ∧
          (r.val = 2 ↔ ¬ (rookCan a b c d e f ∨ bishopCan a b c d e f)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)), ∃ r : I64,
      min_moves_to_capture_the_queen a b c d e f = ok r ∧
        (r.val = 1 ↔ rookCan a b c d e f ∨ bishopCan a b c d e f) ∧
          (r.val = 2 ↔ ¬ (rookCan a b c d e f ∨ bishopCan a b c d e f))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail) for every input satisfying the preconditions.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_2 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)) :
    ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)), ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r) := by
  sorry

/-- The function returns a result r with r ≥ 1.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_3 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)) :
    ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)), ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r with r ≤ 2.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_4 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)) :
    ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r ∧ r.val ≤ 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val)), ∃ r : I64, min_moves_to_capture_the_queen a b c d e f = ok r ∧ r.val ≤ 2) := by
  sorry

/-- For any valid input (a,b,c,d,e,f), let a' = 9 - a, b' = 9 - b, c' = 9 - c, d' = 9 - d, e' = 9 - e, f' = 9 - f. If the function returns r on (a,b,c,d,e,f) and r' on (a',b',c',d',e',f'), then r = r'.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_5 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val))
    (r r' : I64)
    (hr : min_moves_to_capture_the_queen a b c d e f = ok r)
    (hr' : min_moves_to_capture_the_queen
        (reflect a ha1 ha2) (reflect b hb1 hb2) (reflect c hc1 hc2)
        (reflect d hd1 hd2) (reflect e he1 he2) (reflect f hf1 hf2) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val))
    (r r' : I64)
    (hr : min_moves_to_capture_the_queen a b c d e f = ok r)
    (hr' : min_moves_to_capture_the_queen
        (reflect a ha1 ha2) (reflect b hb1 hb2) (reflect c hc1 hc2)
        (reflect d hd1 hd2) (reflect e he1 he2) (reflect f hf1 hf2) = ok r'), r.val = r'.val) := by
  sorry

/-- For any valid input (a,b,c,d,e,f), let a' = a, b' = 9 - b, c' = c, d' = 9 - d, e' = e, f' = 9 - f. If the function returns r on (a,b,c,d,e,f) and r' on (a',b',c',d',e',f'), then r = r'.
  Preconditions: 1 ≤ a, b, c, d, e, f ≤ 8; (a,b) ≠ (c,d); (a,b) ≠ (e,f); (c,d) ≠ (e,f). -/
theorem spec_6 (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val))
    (r r' : I64)
    (hr : min_moves_to_capture_the_queen a b c d e f = ok r)
    (hr' : min_moves_to_capture_the_queen a (reflect b hb1 hb2) c
        (reflect d hd1 hd2) e (reflect f hf1 hf2) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b c d e f : I64)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 8)
    (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 8)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 8)
    (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 8)
    (he1 : 1 ≤ e.val) (he2 : e.val ≤ 8)
    (hf1 : 1 ≤ f.val) (hf2 : f.val ≤ 8)
    (h_ab_ne_cd : ¬ (a.val = c.val ∧ b.val = d.val))
    (h_ab_ne_ef : ¬ (a.val = e.val ∧ b.val = f.val))
    (h_cd_ne_ef : ¬ (c.val = e.val ∧ d.val = f.val))
    (r r' : I64)
    (hr : min_moves_to_capture_the_queen a b c d e f = ok r)
    (hr' : min_moves_to_capture_the_queen a (reflect b hb1 hb2) c
        (reflect d hd1 hd2) e (reflect f hf1 hf2) = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.MinMovesToCaptureTheQueen
