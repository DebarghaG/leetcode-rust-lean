import Aegis.MinimumJumps.Code.Funs

/-!
# Specifications of `Aegis.MinimumJumps.minimum_jumps`

LeetCode problem `minimum-jumps-to-reach-home`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumJumps

set_option autoImplicit false

namespace AegisSpec.MinimumJumps

def forbiddenVals (forbidden : Slice Std.I64) : List ℤ :=
  forbidden.val.map fun v => v.val

def StepOK (a b : ℤ) (F : List ℤ) (u v : ℤ) : Prop :=
  (v = u + a ∨ v = u - b) ∧ 0 ≤ v ∧ v ∉ F

def IsJumpSeq (F : List ℤ) (a b y : ℤ) (p : List ℤ) : Prop :=
  p.head? = some 0 ∧
  p.getLast? = some y ∧
  (∀ (i : ℕ) (u v : ℤ), p[i]? = some u → p[i + 1]? = some v → StepOK a b F u v) ∧
  (∀ (i : ℕ) (u v w : ℤ), p[i]? = some u → p[i + 1]? = some v → p[i + 2]? = some w →
    ¬ (v = u - b ∧ w = v - b))

def HasJumpSeq (F : List ℤ) (a b y : ℤ) : Prop :=
  ∃ p : List ℤ, IsJumpSeq F a b y p

def JumpLen (p : List ℤ) : ℤ :=
  (p.length : ℤ) - 1

def HasJumpSeqOfLen (F : List ℤ) (a b y : ℤ) (r : ℤ) : Prop :=
  ∃ p : List ℤ, IsJumpSeq F a b y p ∧ JumpLen p = r

def stepsOf (p : List ℤ) : List ℤ :=
  (p.zip p.tail).map fun uv => uv.2 - uv.1

def NumForward (a : ℤ) (p : List ℤ) : ℕ :=
  (stepsOf p).countP fun s => s == a

def NumBackward (b : ℤ) (p : List ℤ) : ℕ :=
  (stepsOf p).countP fun s => s == -b

/-- The function returns a result r and does not fail. A valid jump sequence from 0 to y is a finite sequence p_0, ..., p_n with n >= 0 such that p_0 = 0, p_n = y, for every i with 0 <= i < n either p_{i+1} = p_i + a or p_{i+1} = p_i - b, every p_i is nonnegative, every p_i with 1 <= i <= n is not equal to forbidden[j] for any j with 0 <= j < len(forbidden), and there is no i with 0 <= i < n-1 such that p_{i+1} = p_i - b and p_{i+2} = p_{i+1} - b. Then: if there exists a valid jump sequence from 0 to x, r >= 0, there is a valid jump sequence from 0 to x of length r, and every valid jump sequence from 0 to x has length at least r; if no valid jump sequence from 0 to x exists, r = -1.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_1 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧
      (HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val →
        (0 ≤ r.val ∧
          HasJumpSeqOfLen (forbiddenVals forbidden) a.val b.val x.val r.val ∧
          ∀ q : List ℤ, IsJumpSeq (forbiddenVals forbidden) a.val b.val x.val q →
            r.val ≤ JumpLen q)) ∧
      (¬ HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧
      (HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val →
        (0 ≤ r.val ∧
          HasJumpSeqOfLen (forbiddenVals forbidden) a.val b.val x.val r.val ∧
          ∀ q : List ℤ, IsJumpSeq (forbiddenVals forbidden) a.val b.val x.val q →
            r.val ≤ JumpLen q)) ∧
      (¬ HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val → r.val = -1)) := by
  sorry

/-- The function never fails: for some integer r it returns .ok r (and never .err); in particular it does not overflow, panic, or access out of bounds.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_2 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_3 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → r.val = -1 ∨ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → r.val = -1 ∨ 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists a valid jump sequence from 0 to x of length exactly r. Here a valid jump sequence is a finite sequence p_0, ..., p_n with p_0 = 0, p_n = x, each step either +a or -b, all positions nonnegative, all landing positions not forbidden, and no two consecutive -b steps.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_4 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val →
      HasJumpSeqOfLen (forbiddenVals forbidden) a.val b.val x.val r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val →
      HasJumpSeqOfLen (forbiddenVals forbidden) a.val b.val x.val r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, every valid jump sequence from 0 to x has length at least r. Here a valid jump sequence is a finite sequence p_0, ..., p_n with p_0 = 0, p_n = x, each step either +a or -b, all positions nonnegative, all landing positions not forbidden, and no two consecutive -b steps.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_5 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val →
      ∀ q : List ℤ, IsJumpSeq (forbiddenVals forbidden) a.val b.val x.val q →
        r.val ≤ JumpLen q := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val →
      ∀ q : List ℤ, IsJumpSeq (forbiddenVals forbidden) a.val b.val x.val q →
        r.val ≤ JumpLen q) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no valid jump sequence from 0 to x. Here a valid jump sequence is a finite sequence p_0, ..., p_n with p_0 = 0, p_n = x, each step either +a or -b, all positions nonnegative, all landing positions not forbidden, and no two consecutive -b steps.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_6 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r →
      (r.val = -1 ↔ ¬ HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r →
      (r.val = -1 ↔ ¬ HasJumpSeq (forbiddenVals forbidden) a.val b.val x.val)) := by
  sorry

/-- If x = 0, then the function returns r = 0.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_7 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hx0 : x.val = 0) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hx0 : x.val = 0), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if x = a.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_8 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → (r.val = 1 ↔ x.val = a.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → (r.val = 1 ↔ x.val = a.val)) := by
  sorry

/-- If x = a - b, x > 0, and a is not equal to forbidden[j] for every j with 0 <= j < len(forbidden), then the function returns r = 2.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_9 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hxab : x.val = a.val - b.val) (hxpos : 0 < x.val)
    (ha_not_forbidden : a.val ∉ forbiddenVals forbidden) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hxab : x.val = a.val - b.val) (hxpos : 0 < x.val)
    (ha_not_forbidden : a.val ∉ forbiddenVals forbidden), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 2) := by
  sorry

/-- If x > 0 and there exists j with 0 <= j < len(forbidden) and forbidden[j] = a, then the function returns r = -1.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_10 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hxpos : 0 < x.val)
    (ha_forbidden : a.val ∈ forbiddenVals forbidden) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hxpos : 0 < x.val)
    (ha_forbidden : a.val ∈ forbiddenVals forbidden), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = -1) := by
  sorry

/-- If there is an integer k with k >= 2, x = k*a, and for every t with 1 <= t <= k the position t*a is not equal to forbidden[j] for any j with 0 <= j < len(forbidden), then the function returns r = k.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_11 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ k : ℤ, 2 ≤ k → x.val = k * a.val →
      (∀ t : ℤ, 1 ≤ t → t ≤ k → t * a.val ∉ forbiddenVals forbidden) →
      ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ k : ℤ, 2 ≤ k → x.val = k * a.val →
      (∀ t : ℤ, 1 ≤ t → t ≤ k → t * a.val ∉ forbiddenVals forbidden) →
      ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = k) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, r <= 12001.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_12 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden) :
    ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val → r.val ≤ 12001 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden), ∀ r : Std.I64, minimum_jumps forbidden a b x = ok r → 0 ≤ r.val → r.val ≤ 12001) := by
  sorry

/-- If x = 2*a - b, x > 0, a != b, and neither a nor 2*a is equal to forbidden[j] for any j with 0 <= j < len(forbidden), then the function returns r = 3.
  Preconditions: len(forbidden) >= 0, len(forbidden) <= 1000, for every i with 0 <= i < len(forbidden): 1 <= forbidden[i] <= 2000, all elements of forbidden are pairwise distinct, 1 <= a <= 2000, 1 <= b <= 2000, 0 <= x <= 2000, and for every i with 0 <= i < len(forbidden), forbidden[i] != x. -/
theorem spec_13 (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hx2ab : x.val = 2 * a.val - b.val) (hxpos : 0 < x.val) (hab : a.val ≠ b.val)
    (ha_not_forbidden : a.val ∉ forbiddenVals forbidden)
    (h2a_not_forbidden : 2 * a.val ∉ forbiddenVals forbidden) :
    ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 3 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (forbidden : Slice Std.I64) (a b x : Std.I64)
    (hlen0 : 0 ≤ forbidden.val.length) (hlen : forbidden.val.length ≤ 1000)
    (hrange : ∀ y ∈ forbiddenVals forbidden, 1 ≤ y ∧ y ≤ 2000)
    (hnodup : (forbiddenVals forbidden).Nodup)
    (ha : 1 ≤ a.val ∧ a.val ≤ 2000) (hb : 1 ≤ b.val ∧ b.val ≤ 2000)
    (hx : 0 ≤ x.val ∧ x.val ≤ 2000)
    (hxnot : x.val ∉ forbiddenVals forbidden)
    (hx2ab : x.val = 2 * a.val - b.val) (hxpos : 0 < x.val) (hab : a.val ≠ b.val)
    (ha_not_forbidden : a.val ∉ forbiddenVals forbidden)
    (h2a_not_forbidden : 2 * a.val ∉ forbiddenVals forbidden), ∃ r : Std.I64, minimum_jumps forbidden a b x = ok r ∧ r.val = 3) := by
  sorry

end AegisSpec.MinimumJumps
