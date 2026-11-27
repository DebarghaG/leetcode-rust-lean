import Aegis.TheMaximumAchievableX.Code.Funs

/-!
# Specifications of `Aegis.TheMaximumAchievableX.the_maximum_achievable_x`

LeetCode problem `find-the-maximum-achievable-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TheMaximumAchievableX

  def IsOp (p : ℤ × ℤ) : Prop := (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)

  def applyOps : List (ℤ × ℤ) → ℤ → ℤ → ℤ × ℤ
    | [], a, b => (a, b)
    | p :: ops, a, b => applyOps ops (a + p.1) (b + p.2)

  def Achievable (num t x : ℤ) : Prop :=
    ∃ s : ℕ, (s : ℤ) ≤ t ∧ ∃ ops : List (ℤ × ℤ),
      ops.length = s ∧ (∀ p ∈ ops, IsOp p) ∧
        (applyOps ops x num).1 = (applyOps ops x num).2

  def downUpOps (t : ℕ) : List (ℤ × ℤ) := List.replicate t ((-1, 1))

  /-- The function returns a result r, and value(r) is the maximum integer x for which there exist a nonnegative integer s <= value(t) and a sequence of s operations, each replacing a pair (a,b) by (a+e,b+d) with e,d in {+1,-1}, such that starting from (x,value(num)) and applying the sequence ends with the two components equal. Equivalently, x can become equal to the evolving value of num within at most value(t) operations, and no larger integer can.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_1 (num t : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50) :
      ∃ r : Std.I64, Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r ∧
        Achievable num.val t.val r.val ∧ ∀ x : ℤ, Achievable num.val t.val x → x ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num t : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50), ∃ r : Std.I64, Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r ∧
          Achievable num.val t.val r.val ∧ ∀ x : ℤ, Achievable num.val t.val x → x ≤ r.val) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_2 (num t : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50) :
      ∃ r : Std.I64, Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num t : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50), ∃ r : Std.I64, Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, value(r) = value(num) + 2*value(t).
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_3 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      r.val = num.val + 2 * t.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), r.val = num.val + 2 * t.val) := by
    sorry

  /-- Whenever the function returns a result r, value(r) >= 3.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_4 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      3 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), 3 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, value(r) <= 150.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_5 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      r.val ≤ 150 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), r.val ≤ 150) := by
    sorry

  /-- Whenever the function returns a result r, value(r) >= value(num) + 2.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_6 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      num.val + 2 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), num.val + 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, value(r) <= value(num) + 100.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_7 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      r.val ≤ num.val + 100 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), r.val ≤ num.val + 100) := by
    sorry

  /-- Whenever the function returns a result r, value(r) - value(num) is even.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_8 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      Even (r.val - num.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), Even (r.val - num.val)) := by
    sorry

  /-- Whenever the function returns a result r, the value value(r) is achievable: start with x = value(r) and num0 = value(num), perform value(t) operations that each decrease x by 1 and increase num0 by 1; afterwards both values equal value(num) + value(t).
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_9 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      (applyOps (downUpOps t.val.toNat) r.val num.val).1 = num.val + t.val ∧
        (applyOps (downUpOps t.val.toNat) r.val num.val).2 = num.val + t.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), (applyOps (downUpOps t.val.toNat) r.val num.val).1 = num.val + t.val ∧
          (applyOps (downUpOps t.val.toNat) r.val num.val).2 = num.val + t.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x with x > value(r) and every sequence of at most value(t) operations starting from (x, value(num)), where each operation replaces a pair (a,b) by (a+e,b+d) with e,d in {+1,-1}, the final two components are not equal.
    Preconditions: The machine integers num and t satisfy 1 <= value(num) <= 50 and 1 <= value(t) <= 50. -/
  theorem spec_10 (num t r : Std.I64)
      (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
      (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
      (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r) :
      ∀ x : ℤ, r.val < x → ∀ ops : List (ℤ × ℤ), (ops.length : ℤ) ≤ t.val →
        (∀ p ∈ ops, IsOp p) → (applyOps ops x num.val).1 ≠ (applyOps ops x num.val).2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num t r : Std.I64)
        (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 50)
        (ht_lo : 1 ≤ t.val) (ht_hi : t.val ≤ 50)
        (hres : Aegis.TheMaximumAchievableX.the_maximum_achievable_x num t = Result.ok r), ∀ x : ℤ, r.val < x → ∀ ops : List (ℤ × ℤ), (ops.length : ℤ) ≤ t.val →
          (∀ p ∈ ops, IsOp p) → (applyOps ops x num.val).1 ≠ (applyOps ops x num.val).2) := by
    sorry

  end AegisSpec.TheMaximumAchievableX
