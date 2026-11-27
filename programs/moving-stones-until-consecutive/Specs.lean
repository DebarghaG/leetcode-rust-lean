import Aegis.NumMovesStones.Code.Funs

/-!
# Specifications of `Aegis.NumMovesStones.num_moves_stones`

LeetCode problem `moving-stones-until-consecutive`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumMovesStones

open Aegis.NumMovesStones

def min3 (a b c : ℤ) : ℤ := min a (min b c)

def max3 (a b c : ℤ) : ℤ := max a (max b c)

def mid3 (a b c : ℤ) : ℤ := a + b + c - min3 a b c - max3 a b c

def gap1 (a b c : ℤ) : ℤ := mid3 a b c - min3 a b c

def gap2 (a b c : ℤ) : ℤ := max3 a b c - mid3 a b c

def spread (a b c : ℤ) : ℤ := max3 a b c - min3 a b c

def tripleSet (a b c : ℤ) : Finset ℤ := {a, b, c}

def getInt (v : alloc.vec.Vec Std.I64) (i : Nat) : Option ℤ := (v.val[i]?).map (fun x => x.val)

/-- Let x = min(a,b,c), z = max(a,b,c), and let y be the element of {a,b,c} different from x and z (so x < y < z). Put g1 = y - x and g2 = z - y. The function returns a result r with len(r) = 2, r[0] = (if g1 = 1 and g2 = 1 then 0 else if g1 <= 2 or g2 <= 2 then 1 else 2), and r[1] = z - x - 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_1 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      r.val.length = 2 ∧
      getInt r 0 = some
        (if gap1 a.val b.val c.val = 1 ∧ gap2 a.val b.val c.val = 1 then 0
         else if gap1 a.val b.val c.val ≤ 2 ∨ gap2 a.val b.val c.val ≤ 2 then 1
         else 2) ∧
      getInt r 1 = some (spread a.val b.val c.val - 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      r.val.length = 2 ∧
      getInt r 0 = some
        (if gap1 a.val b.val c.val = 1 ∧ gap2 a.val b.val c.val = 1 then 0
         else if gap1 a.val b.val c.val ≤ 2 ∨ gap2 a.val b.val c.val ≤ 2 then 1
         else 2) ∧
      getInt r 1 = some (spread a.val b.val c.val - 2)) := by
  sorry

/-- The function returns a result r and len(r) = 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_2 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧ r.val.length = 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧ r.val.length = 2) := by
  sorry

/-- The function returns a result r (it does not panic, overflow, or fail).
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_3 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r) := by
  sorry

/-- The function returns a result r and r[0] is one of the integers 0, 1, or 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_4 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 0 ∨ getInt r 0 = some 1 ∨ getInt r 0 = some 2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 0 ∨ getInt r 0 = some 1 ∨ getInt r 0 = some 2)) := by
  sorry

/-- The function returns a result r and 0 <= r[1] <= 97.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_5 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      ∃ m : ℤ, getInt r 1 = some m ∧ 0 ≤ m ∧ m ≤ 97 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      ∃ m : ℤ, getInt r 1 = some m ∧ 0 ≤ m ∧ m ≤ 97) := by
  sorry

/-- The function returns a result r and r[1] = max(a,b,c) - min(a,b,c) - 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_6 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      getInt r 1 = some (spread a.val b.val c.val - 2) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      getInt r 1 = some (spread a.val b.val c.val - 2)) := by
  sorry

/-- The function returns a result r and r[1] = 0 if and only if max(a,b,c) - min(a,b,c) = 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_7 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 1 = some 0 ↔ spread a.val b.val c.val = 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 1 = some 0 ↔ spread a.val b.val c.val = 2)) := by
  sorry

/-- The function returns a result r and r[0] = 0 if and only if max(a,b,c) - min(a,b,c) = 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_8 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 0 ↔ spread a.val b.val c.val = 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 0 ↔ spread a.val b.val c.val = 2)) := by
  sorry

/-- The function returns a result r and r[0] = 1 if and only if max(a,b,c) - min(a,b,c) > 2 and there exist two distinct elements u and v of {a,b,c} with |u - v| <= 2.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_9 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 1 ↔
        spread a.val b.val c.val > 2 ∧
          ∃ u v : ℤ, u ∈ tripleSet a.val b.val c.val ∧ v ∈ tripleSet a.val b.val c.val ∧
            u ≠ v ∧ |u - v| ≤ 2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 1 ↔
        spread a.val b.val c.val > 2 ∧
          ∃ u v : ℤ, u ∈ tripleSet a.val b.val c.val ∧ v ∈ tripleSet a.val b.val c.val ∧
            u ≠ v ∧ |u - v| ≤ 2)) := by
  sorry

/-- The function returns a result r and r[0] = 2 if and only if for every two distinct elements u and v of {a,b,c}, |u - v| >= 3.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_10 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 2 ↔
        ∀ u v : ℤ, u ∈ tripleSet a.val b.val c.val → v ∈ tripleSet a.val b.val c.val →
          u ≠ v → 3 ≤ |u - v|) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 2 ↔
        ∀ u v : ℤ, u ∈ tripleSet a.val b.val c.val → v ∈ tripleSet a.val b.val c.val →
          u ≠ v → 3 ≤ |u - v|)) := by
  sorry

/-- The function returns a result r and r[0] <= r[1].
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_11 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      ∃ m0 m1 : ℤ, getInt r 0 = some m0 ∧ getInt r 1 = some m1 ∧ m0 ≤ m1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      ∃ m0 m1 : ℤ, getInt r 0 = some m0 ∧ getInt r 1 = some m1 ∧ m0 ≤ m1) := by
  sorry

/-- The function returns a result r and, if r[0] = 2, then r[1] >= 4.
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_12 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 2 → ∃ m1 : ℤ, getInt r 1 = some m1 ∧ 4 ≤ m1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∃ r, num_moves_stones a b c = ok r ∧
      (getInt r 0 = some 2 → ∃ m1 : ℤ, getInt r 1 = some m1 ∧ 4 ≤ m1)) := by
  sorry

/-- Let r be the result returned for (a,b,c). For every permutation (a', b', c') of (a, b, c), the result r' returned for (a', b', c') satisfies r'[0] = r[0] and r'[1] = r[1].
  Preconditions: 1 <= a, b, c <= 100 and a, b, c are pairwise distinct. -/
theorem spec_13 (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    ∀ r, num_moves_stones a b c = ok r →
      ∀ (a' b' c' : Std.I64), [a', b', c'].Perm [a, b, c] →
        ∀ r', num_moves_stones a' b' c' = ok r' →
          getInt r' 0 = getInt r 0 ∧ getInt r' 1 = getInt r 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha1 : 1 ≤ a.val) (ha100 : a.val ≤ 100)
    (hb1 : 1 ≤ b.val) (hb100 : b.val ≤ 100)
    (hc1 : 1 ≤ c.val) (hc100 : c.val ≤ 100)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val), ∀ r, num_moves_stones a b c = ok r →
      ∀ (a' b' c' : Std.I64), [a', b', c'].Perm [a, b, c] →
        ∀ r', num_moves_stones a' b' c' = ok r' →
          getInt r' 0 = getInt r 0 ∧ getInt r' 1 = getInt r 1) := by
  sorry

end AegisSpec.NumMovesStones
