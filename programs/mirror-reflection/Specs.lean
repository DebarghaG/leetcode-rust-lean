import Aegis.MirrorReflection.Code.Funs

/-!
# Specifications of `Aegis.MirrorReflection.mirror_reflection`

LeetCode problem `mirror-reflection`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MirrorReflection

def v2 (n : Int) : Nat := Nat.findGreatest (fun k => 2 ^ k ∣ n.natAbs) n.natAbs

def i64OfInt (n : Int) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

def receptorCorner (p : Int) (r : Nat) : Int × Int :=
  match r with
  | 0 => (p, 0)
  | 1 => (p, p)
  | 2 => (0, p)
  | _ => (0, 0)

/-- Whenever mirror_reflection(p,q) returns a result r, r is exactly the following value: r = 2 if v2(p) > v2(q); r = 1 if v2(p) = v2(q); and r = 0 if v2(p) < v2(q).
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000. The receptors are numbered as in the problem: receptor 0 is the southeast corner (p,0), receptor 1 is the northeast corner (p,p), and receptor 2 is the northwest corner (0,p). For a positive integer n, v2(n) denotes the exponent of 2 in n, i.e. the largest k >= 0 such that 2^k divides n. -/
theorem spec_1 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      r.val = (if v2 p.val > v2 q.val then (2 : Int)
               else if v2 p.val = v2 q.val then (1 : Int) else (0 : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      r.val = (if v2 p.val > v2 q.val then (2 : Int)
               else if v2 p.val = v2 q.val then (1 : Int) else (0 : Int))) := by
  sorry

/-- For every such p and q, mirror_reflection(p,q) returns a result; it does not fail, panic, or overflow.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000. -/
theorem spec_2 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000), ∃ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, r is one of 0, 1, or 2.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000. -/
theorem spec_3 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      r.val = 0 ∨ r.val = 1 ∨ r.val = 2) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, r = 1.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000 and q = p. -/
theorem spec_4 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_q_eq_p : q.val = p.val) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_q_eq_p : q.val = p.val), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 1) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, r = 2.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000, p is even, and q is odd. -/
theorem spec_5 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_even : Even p.val) (h_q_odd : Odd q.val) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_even : Even p.val) (h_q_odd : Odd q.val), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 2) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, r = 0.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000, p is odd, and q is even. -/
theorem spec_6 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_odd : Odd p.val) (h_q_even : Even q.val) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_odd : Odd p.val) (h_q_even : Even q.val), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r → r.val = 0) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, mirror_reflection(p/2,q/2) also returns r; equivalently, the two calls return the same receptor number.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000, and both p and q are even. -/
theorem spec_7 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_even : Even p.val) (h_q_even : Even q.val) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      Aegis.MirrorReflection.mirror_reflection (i64OfInt (p.val / 2)) (i64OfInt (q.val / 2))
        = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (h_p_even : Even p.val) (h_q_even : Even q.val), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      Aegis.MirrorReflection.mirror_reflection (i64OfInt (p.val / 2)) (i64OfInt (q.val / 2))
        = ok r) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, mirror_reflection(k*p,k*q) also returns r.
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000, k is a positive integer, and k*p <= 1000. -/
theorem spec_8 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (k : Nat) (h_k_pos : 0 < k) (h_kp_le : (k : Int) * p.val ≤ 1000) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      Aegis.MirrorReflection.mirror_reflection (i64OfInt ((k : Int) * p.val))
        (i64OfInt ((k : Int) * q.val)) = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) (k : Nat) (h_k_pos : 0 < k) (h_kp_le : (k : Int) * p.val ≤ 1000), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      Aegis.MirrorReflection.mirror_reflection (i64OfInt ((k : Int) * p.val))
        (i64OfInt ((k : Int) * q.val)) = ok r) := by
  sorry

/-- mirror_reflection(3,1) returns 1, mirror_reflection(4,2) returns 2, and mirror_reflection(10,4) returns 0. Hence every receptor number in {0,1,2} is attainable by some allowed input.
  Preconditions: The following inputs satisfy 1 <= q <= p <= 1000: (p,q) = (3,1), (4,2), and (10,4). -/
theorem spec_9 :
    Aegis.MirrorReflection.mirror_reflection 3#i64 1#i64 = ok 1#i64 ∧
    Aegis.MirrorReflection.mirror_reflection 4#i64 2#i64 = ok 2#i64 ∧
    Aegis.MirrorReflection.mirror_reflection 10#i64 4#i64 = ok 0#i64 ∧
    (∀ n : Int, (n = 0 ∨ n = 1 ∨ n = 2) →
      ∃ p q r : Std.I64, 1 ≤ q.val ∧ q.val ≤ p.val ∧ p.val ≤ 1000 ∧
        Aegis.MirrorReflection.mirror_reflection p q = ok r ∧ r.val = n) := by
  sorry

theorem spec_9_neg :
    ¬ (Aegis.MirrorReflection.mirror_reflection 3#i64 1#i64 = ok 1#i64 ∧
    Aegis.MirrorReflection.mirror_reflection 4#i64 2#i64 = ok 2#i64 ∧
    Aegis.MirrorReflection.mirror_reflection 10#i64 4#i64 = ok 0#i64 ∧
    (∀ n : Int, (n = 0 ∨ n = 1 ∨ n = 2) →
      ∃ p q r : Std.I64, 1 ≤ q.val ∧ q.val ≤ p.val ∧ p.val ≤ 1000 ∧
        Aegis.MirrorReflection.mirror_reflection p q = ok r ∧ r.val = n)) := by
  sorry

/-- Whenever mirror_reflection(p,q) returns a result r, the receptor numbered r is located as follows: receptor 0 is at the southeast corner (p,0), receptor 1 is at the northeast corner (p,p), and receptor 2 is at the northwest corner (0,p).
  Preconditions: p and q are 64-bit integers satisfying 1 <= q <= p <= 1000, and receptors are numbered as in the problem statement. -/
theorem spec_10 (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000) :
    ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      (r.val = 0 ∧ receptorCorner p.val r.val.toNat = (p.val, 0)) ∨
      (r.val = 1 ∧ receptorCorner p.val r.val.toNat = (p.val, p.val)) ∨
      (r.val = 2 ∧ receptorCorner p.val r.val.toNat = (0, p.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (p q : Std.I64) (h_q_pos : 1 ≤ q.val) (h_q_le_p : q.val ≤ p.val)
    (h_p_le : p.val ≤ 1000), ∀ r : Std.I64, Aegis.MirrorReflection.mirror_reflection p q = ok r →
      (r.val = 0 ∧ receptorCorner p.val r.val.toNat = (p.val, 0)) ∨
      (r.val = 1 ∧ receptorCorner p.val r.val.toNat = (p.val, p.val)) ∨
      (r.val = 2 ∧ receptorCorner p.val r.val.toNat = (0, p.val))) := by
  sorry

end AegisSpec.MirrorReflection
