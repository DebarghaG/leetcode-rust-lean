import Aegis.NonSpecialCount.Code.Funs

/-!
# Specifications of `Aegis.NonSpecialCount.non_special_count`

LeetCode problem `find-the-count-of-numbers-which-are-not-special`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NonSpecialCount

def IsSpecial (x : Int) : Prop := ∃ p : Nat, p.Prime ∧ x = (p : Int) * (p : Int)

def primeSquaresIn (l r : Int) : Finset Nat :=
  (Finset.range (r.toNat + 1)).filter
    (fun p => p.Prime ∧ l ≤ (p : Int) * (p : Int) ∧ (p : Int) * (p : Int) ≤ r)

def intSqrt (x : Int) : Int := (Nat.sqrt x.toNat : Int)

/-- The function returns a result res, and the integer value resv of res equals (rv - lv + 1) - |{ p : p is prime and lv <= p*p <= rv }|. Equivalently, resv is the number of integers x with lv <= x <= rv that are not special, i.e. for which there is no prime p with x = p*p.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. Here a prime is a positive integer greater than 1 with exactly two positive divisors (1 and itself), and a positive integer x is special if it has exactly two positive proper divisors, i.e. exactly two positive divisors other than x; equivalently, x = p*p for some prime p. -/
theorem spec_1 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      res.val = (r.val - l.val + 1) - ((primeSquaresIn l.val r.val).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      res.val = (r.val - l.val + 1) - ((primeSquaresIn l.val r.val).card : Int)) := by
  sorry

/-- For every l and r satisfying the preconditions, the function returns a result res; it does not fail, panic, or overflow.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_2 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res) := by
  sorry

/-- The function returns a result res whose integer value resv satisfies 0 <= resv <= rv - lv + 1.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_3 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      0 ≤ res.val ∧ res.val ≤ r.val - l.val + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      0 ≤ res.val ∧ res.val ≤ r.val - l.val + 1) := by
  sorry

/-- The function returns a result res, and for its integer value resv we have resv < rv - lv + 1 if and only if there exists a prime p such that lv <= p*p <= rv.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. Here x is special if it has exactly two positive proper divisors; for positive x this is equivalent to x = p*p for some prime p. -/
theorem spec_4 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (res.val < r.val - l.val + 1 ↔
        ∃ p : Nat, p.Prime ∧ l.val ≤ (p : Int) * (p : Int) ∧ (p : Int) * (p : Int) ≤ r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (res.val < r.val - l.val + 1 ↔
        ∃ p : Nat, p.Prime ∧ l.val ≤ (p : Int) * (p : Int) ∧ (p : Int) * (p : Int) ≤ r.val)) := by
  sorry

/-- If rv <= 3, then the function returns a result res whose integer value is resv = rv - lv + 1.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_5 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) (hr3 : r.val ≤ 3) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      res.val = r.val - l.val + 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) (hr3 : r.val ≤ 3), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      res.val = r.val - l.val + 1) := by
  sorry

/-- If lv = rv, then the function returns a result res whose integer value is 0 when lv is special and 1 otherwise.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. Here x is special if x = p*p for some prime p. -/
theorem spec_6 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) (heq : l.val = r.val) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (IsSpecial l.val → res.val = 0) ∧ (¬ IsSpecial l.val → res.val = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) (heq : l.val = r.val), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (IsSpecial l.val → res.val = 0) ∧ (¬ IsSpecial l.val → res.val = 1)) := by
  sorry

/-- For every integer m with lv <= m < rv, let res, res1, and res2 be the integer values returned by non_special_count on (lv, rv), (lv, m), and (m+1, rv) respectively. Then res = res1 + res2.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_7 (l r m m1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hm : l.val ≤ m.val) (hmr : m.val < r.val) (hm1 : m1.val = m.val + 1) :
    ∃ res res1 res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l m = Aeneas.Std.Result.ok res1 ∧
      Aegis.NonSpecialCount.non_special_count m1 r = Aeneas.Std.Result.ok res2 ∧
      res.val = res1.val + res2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (l r m m1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hm : l.val ≤ m.val) (hmr : m.val < r.val) (hm1 : m1.val = m.val + 1), ∃ res res1 res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l m = Aeneas.Std.Result.ok res1 ∧
      Aegis.NonSpecialCount.non_special_count m1 r = Aeneas.Std.Result.ok res2 ∧
      res.val = res1.val + res2.val) := by
  sorry

/-- If lv > 1, let res, resR, and resL be the integer values returned by non_special_count on (lv, rv), (1, rv), and (1, lv-1) respectively. Then res = resR - resL.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_8 (l r l1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hl1 : 1 < l.val) (hl1v : l1.val = l.val - 1) :
    ∃ res resR resL,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count 1#i64 r = Aeneas.Std.Result.ok resR ∧
      Aegis.NonSpecialCount.non_special_count 1#i64 l1 = Aeneas.Std.Result.ok resL ∧
      res.val = resR.val - resL.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (l r l1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hl1 : 1 < l.val) (hl1v : l1.val = l.val - 1), ∃ res resR resL,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count 1#i64 r = Aeneas.Std.Result.ok resR ∧
      Aegis.NonSpecialCount.non_special_count 1#i64 l1 = Aeneas.Std.Result.ok resL ∧
      res.val = resR.val - resL.val) := by
  sorry

/-- If lv < rv, let res and resPrev be the integer values returned by non_special_count on (lv, rv) and (lv, rv-1) respectively. If rv is special, then res = resPrev; otherwise res = resPrev + 1.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. Here x is special if x = p*p for some prime p. -/
theorem spec_9 (l r r1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hlt : l.val < r.val) (hr1 : r1.val = r.val - 1) :
    ∃ res resPrev,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l r1 = Aeneas.Std.Result.ok resPrev ∧
      (IsSpecial r.val → res.val = resPrev.val) ∧
      (¬ IsSpecial r.val → res.val = resPrev.val + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (l r r1 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hlt : l.val < r.val) (hr1 : r1.val = r.val - 1), ∃ res resPrev,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l r1 = Aeneas.Std.Result.ok resPrev ∧
      (IsSpecial r.val → res.val = resPrev.val) ∧
      (¬ IsSpecial r.val → res.val = resPrev.val + 1)) := by
  sorry

/-- For every integer r2 with rv <= r2 <= 1000000000, let res and res2 be the integer values returned by non_special_count on (lv, rv) and (lv, r2) respectively. Then res <= res2.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_10 (l r r2 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hr2l : r.val ≤ r2.val) (hr2r : r2.val ≤ 1000000000) :
    ∃ res res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l r2 = Aeneas.Std.Result.ok res2 ∧
      res.val ≤ res2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (l r r2 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hr2l : r.val ≤ r2.val) (hr2r : r2.val ≤ 1000000000), ∃ res res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l r2 = Aeneas.Std.Result.ok res2 ∧
      res.val ≤ res2.val) := by
  sorry

/-- For every integer l2 with lv <= l2 <= rv, let res and res2 be the integer values returned by non_special_count on (lv, rv) and (l2, rv) respectively. Then res2 <= res.
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. -/
theorem spec_11 (l r l2 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hl2l : l.val ≤ l2.val) (hl2r : l2.val ≤ r.val) :
    ∃ res res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l2 r = Aeneas.Std.Result.ok res2 ∧
      res2.val ≤ res.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (l r l2 : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000)
    (hl2l : l.val ≤ l2.val) (hl2r : l2.val ≤ r.val), ∃ res res2,
      Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      Aegis.NonSpecialCount.non_special_count l2 r = Aeneas.Std.Result.ok res2 ∧
      res2.val ≤ res.val) := by
  sorry

/-- The function returns a result res whose integer value resv satisfies resv >= (rv - lv + 1) - (s - 1).
  Preconditions: Let lv and rv be the integer values of l and r. Assume 1 <= lv <= rv <= 1000000000. Let s be the largest integer with s*s <= rv. -/
theorem spec_12 (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000) :
    ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (r.val - l.val + 1) - (intSqrt r.val - 1) ≤ res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (l r : Aeneas.Std.I64)
    (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ 1000000000), ∃ res, Aegis.NonSpecialCount.non_special_count l r = Aeneas.Std.Result.ok res ∧
      (r.val - l.val + 1) - (intSqrt r.val - 1) ≤ res.val) := by
  sorry

end AegisSpec.NonSpecialCount
