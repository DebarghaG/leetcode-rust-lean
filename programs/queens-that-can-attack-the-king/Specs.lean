import Aegis.QueensAttacktheKing.Code.Funs

/-!
# Specifications of `Aegis.QueensAttacktheKing.queens_attackthe_king`

LeetCode problem `queens-that-can-attack-the-king`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.QueensAttacktheKing

set_option autoImplicit false

namespace AegisSpec.QueensAttacktheKing

def coordX (v : alloc.vec.Vec Std.I64) : ℤ := ((v.val[0]?).map (fun c => c.val)).getD 0

def coordY (v : alloc.vec.Vec Std.I64) : ℤ := ((v.val[1]?).map (fun c => c.val)).getD 0

def coord (v : alloc.vec.Vec Std.I64) : ℤ × ℤ := (coordX v, coordY v)

def kingX (king : Slice Std.I64) : ℤ := ((king.val[0]?).map (fun c => c.val)).getD 0

def kingY (king : Slice Std.I64) : ℤ := ((king.val[1]?).map (fun c => c.val)).getD 0

def kingCoord (king : Slice Std.I64) : ℤ × ℤ := (kingX king, kingY king)

def queenCoord (queens : Slice (alloc.vec.Vec Std.I64)) (i : Fin queens.val.length) : ℤ × ℤ :=
  coord (queens.val.get i)

def queenCoords (queens : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
  List.ofFn (fun i : Fin queens.val.length => queenCoord queens i)

def Aligned (q K : ℤ × ℤ) : Prop :=
  q.1 = K.1 ∨ q.2 = K.2 ∨ |q.1 - K.1| = |q.2 - K.2|

def StrictlyBetween (p a b : ℤ × ℤ) : Prop :=
  ∃ u : ℚ, 0 < u ∧ u < 1 ∧
    (p.1 : ℚ) = (a.1 : ℚ) + u * ((b.1 : ℚ) - (a.1 : ℚ)) ∧
    (p.2 : ℚ) = (a.2 : ℚ) + u * ((b.2 : ℚ) - (a.2 : ℚ))

def PositiveMultiple (q1 q2 K : ℤ × ℤ) : Prop :=
  ∃ u : ℚ, 0 < u ∧
    ((q1.1 : ℚ) - (K.1 : ℚ)) = u * ((q2.1 : ℚ) - (K.1 : ℚ)) ∧
    ((q1.2 : ℚ) - (K.2 : ℚ)) = u * ((q2.2 : ℚ) - (K.2 : ℚ))

def Attacks (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (i : Fin queens.val.length) : Prop :=
  queenCoord queens i ≠ kingCoord king ∧
  Aligned (queenCoord queens i) (kingCoord king) ∧
  ∀ j : Fin queens.val.length, j ≠ i →
    ¬ StrictlyBetween (queenCoord queens j) (queenCoord queens i) (kingCoord king)

def Occurs (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (p : ℤ × ℤ) : Prop :=
  ∃ t : Fin r.val.length, (r.val.get t).val.length = 2 ∧ coord (r.val.get t) = p

def ValidInput (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64) : Prop :=
  1 ≤ queens.val.length ∧
  queens.val.length < 64 ∧
  king.val.length = 2 ∧
  (∀ i : Fin queens.val.length, (queens.val.get i).val.length = 2) ∧
  (∀ i : Fin queens.val.length,
    0 ≤ coordX (queens.val.get i) ∧ coordX (queens.val.get i) < 8 ∧
    0 ≤ coordY (queens.val.get i) ∧ coordY (queens.val.get i) < 8) ∧
  0 ≤ kingX king ∧ kingX king < 8 ∧ 0 ≤ kingY king ∧ kingY king < 8 ∧
  (∀ i j : Fin queens.val.length, i ≠ j → queenCoord queens i ≠ queenCoord queens j) ∧
  (∀ i : Fin queens.val.length, queenCoord queens i ≠ kingCoord king)

/-- Write Q_i = (queens[i][0], queens[i][1]) and K = (king[0], king[1]). The function returns a result r, and the entries of r are exactly the coordinates Q_i, for 0 <= i < len(queens), such that Q_i can directly attack K. Specifically, Q_i can directly attack K iff Q_i != K, Q_i is aligned with K (Q_i[0] = K[0], or Q_i[1] = K[1], or |Q_i[0]-K[0]| = |Q_i[1]-K[1]|), and no Q_j with 0 <= j < len(queens) and j != i lies strictly between Q_i and K on the line segment joining them. Thus every attacking Q_i occurs in r exactly once, no other coordinate occurs in r, every entry of r has length 2, and the order of entries of r is arbitrary.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_1 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∃ r, queens_attackthe_king queens king = ok r ∧
      (∀ i : Fin queens.val.length, Attacks queens king i → Occurs r (queenCoord queens i)) ∧
      (∀ p, Occurs r p →
        ∃ i : Fin queens.val.length, Attacks queens king i ∧ p = queenCoord queens i) ∧
      (∀ t : Fin r.val.length, (r.val.get t).val.length = 2) ∧
      (∀ t u : Fin r.val.length, t ≠ u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∃ r, queens_attackthe_king queens king = ok r ∧
      (∀ i : Fin queens.val.length, Attacks queens king i → Occurs r (queenCoord queens i)) ∧
      (∀ p, Occurs r p →
        ∃ i : Fin queens.val.length, Attacks queens king i ∧ p = queenCoord queens i) ∧
      (∀ t : Fin r.val.length, (r.val.get t).val.length = 2) ∧
      (∀ t u : Fin r.val.length, t ≠ u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_2 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∃ r, queens_attackthe_king queens king = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∃ r, queens_attackthe_king queens king = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < len(r) and len(r[t]) = 2, there exists i with 0 <= i < len(queens) such that (r[t][0], r[t][1]) = (queens[i][0], queens[i][1]).
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_3 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        ∃ i : Fin queens.val.length, coord (r.val.get t) = queenCoord queens i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        ∃ i : Fin queens.val.length, coord (r.val.get t) = queenCoord queens i) := by
  sorry

/-- Whenever the function returns a result r, every returned coordinate is aligned with the king: for every t with 0 <= t < len(r) and len(r[t]) = 2, either r[t][0] = king[0], or r[t][1] = king[1], or |r[t][0] - king[0]| = |r[t][1] - king[1]|.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_4 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        Aligned (coord (r.val.get t)) (kingCoord king) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        Aligned (coord (r.val.get t)) (kingCoord king)) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < len(r) and len(r[t]) = 2, writing q = (r[t][0], r[t][1]) and K = (king[0], king[1]), no input queen lies strictly between q and K: there is no j with 0 <= j < len(queens) such that Q_j = (queens[j][0], queens[j][1]) is different from q and Q_j = q + u*(K - q) for some real u with 0 < u < 1.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_5 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        ∀ j : Fin queens.val.length, queenCoord queens j ≠ coord (r.val.get t) →
          ¬ StrictlyBetween (queenCoord queens j) (coord (r.val.get t)) (kingCoord king) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        ∀ j : Fin queens.val.length, queenCoord queens j ≠ coord (r.val.get t) →
          ¬ StrictlyBetween (queenCoord queens j) (coord (r.val.get t)) (kingCoord king)) := by
  sorry

/-- Whenever the function returns a result r, every queen that can directly attack the king appears in r. Formally, for every i with 0 <= i < len(queens), writing Q_i = (queens[i][0], queens[i][1]) and K = (king[0], king[1]), if Q_i != K, Q_i is aligned with K (Q_i[0] = K[0], or Q_i[1] = K[1], or |Q_i[0]-K[0]| = |Q_i[1]-K[1]|), and no Q_j with 0 <= j < len(queens), j != i, lies strictly between Q_i and K, then there exists t with 0 <= t < len(r), len(r[t]) = 2, and (r[t][0], r[t][1]) = Q_i.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_6 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ i : Fin queens.val.length, Attacks queens king i → Occurs r (queenCoord queens i) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ i : Fin queens.val.length, Attacks queens king i → Occurs r (queenCoord queens i)) := by
  sorry

/-- Whenever the function returns a result r, no coordinate occurs more than once in r: for all t and u with 0 <= t < u < len(r), if len(r[t]) = 2 and len(r[u]) = 2, then (r[t][0], r[t][1]) != (r[u][0], r[u][1]).
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_7 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t u : Fin r.val.length, t < u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t u : Fin r.val.length, t < u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u)) := by
  sorry

/-- Whenever the function returns a result r, every entry of r has length exactly 2: for every t with 0 <= t < len(r), len(r[t]) = 2.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_8 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2) := by
  sorry

/-- Whenever the function returns a result r, every returned coordinate is a board square: for every t with 0 <= t < len(r) and len(r[t]) = 2, 0 <= r[t][0] < 8 and 0 <= r[t][1] < 8.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_9 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        0 ≤ coordX (r.val.get t) ∧ coordX (r.val.get t) < 8 ∧
        0 ≤ coordY (r.val.get t) ∧ coordY (r.val.get t) < 8 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        0 ≤ coordX (r.val.get t) ∧ coordX (r.val.get t) < 8 ∧
        0 ≤ coordY (r.val.get t) ∧ coordY (r.val.get t) < 8) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= len(queens).
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_10 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r → r.val.length ≤ queens.val.length := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r → r.val.length ≤ queens.val.length) := by
  sorry

/-- Whenever the function returns a result r, at most one returned queen lies in each of the eight directions from the king. Equivalently, for any two distinct returned coordinates q1 and q2 from entries of r having length 2, with K = (king[0], king[1]), the vectors q1 - K and q2 - K are not positive scalar multiples of one another.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_11 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t u : Fin r.val.length, t ≠ u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u) →
        ¬ PositiveMultiple (coord (r.val.get t)) (coord (r.val.get u)) (kingCoord king) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t u : Fin r.val.length, t ≠ u →
        (r.val.get t).val.length = 2 → (r.val.get u).val.length = 2 →
        coord (r.val.get t) ≠ coord (r.val.get u) →
        ¬ PositiveMultiple (coord (r.val.get t)) (coord (r.val.get u)) (kingCoord king)) := by
  sorry

/-- Whenever the function returns a result r, every aligned queen that is not returned is blocked by some other queen. Formally, for every i with 0 <= i < len(queens), writing Q_i = (queens[i][0], queens[i][1]) and K = (king[0], king[1]), if Q_i != K, Q_i is aligned with K, and Q_i does not occur in r (there is no t with 0 <= t < len(r), len(r[t]) = 2, and (r[t][0], r[t][1]) = Q_i), then there exists j with 0 <= j < len(queens), j != i, such that Q_j = Q_i + u*(K - Q_i) for some real u with 0 < u < 1.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_12 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ i : Fin queens.val.length,
        queenCoord queens i ≠ kingCoord king →
        Aligned (queenCoord queens i) (kingCoord king) →
        ¬ Occurs r (queenCoord queens i) →
        ∃ j : Fin queens.val.length,
          j ≠ i ∧ StrictlyBetween (queenCoord queens j) (queenCoord queens i) (kingCoord king) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ i : Fin queens.val.length,
        queenCoord queens i ≠ kingCoord king →
        Aligned (queenCoord queens i) (kingCoord king) →
        ¬ Occurs r (queenCoord queens i) →
        ∃ j : Fin queens.val.length,
          j ≠ i ∧ StrictlyBetween (queenCoord queens j) (queenCoord queens i) (kingCoord king)) := by
  sorry

/-- Whenever the function returns a result r for input (queens, king) and a result r' for input (queens', king), where queens' is any permutation of the list queens and the same king is used, the sets of coordinates occurring in r and r' are equal: for every pair (a,b), (a,b) occurs as an entry of length 2 in r if and only if (a,b) occurs as an entry of length 2 in r'.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_13 (queens queens' : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) (hperm : queens'.val.Perm queens.val) :
    ∀ r r', queens_attackthe_king queens king = ok r →
      queens_attackthe_king queens' king = ok r' →
      ∀ a b, Occurs r (a, b) ↔ Occurs r' (a, b) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (queens queens' : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) (hperm : queens'.val.Perm queens.val), ∀ r r', queens_attackthe_king queens king = ok r →
      queens_attackthe_king queens' king = ok r' →
      ∀ a b, Occurs r (a, b) ↔ Occurs r' (a, b)) := by
  sorry

/-- Whenever the function returns a result r for input (queens, king) and a result r' for input (queens^T, king^T), where for every i queens^T[i] = [queens[i][1], queens[i][0]] and king^T = [king[1], king[0]], the set of coordinates in r' is exactly the set of transposes of the coordinates in r: for every pair (a,b), (a,b) occurs as an entry of length 2 in r' if and only if (b,a) occurs as an entry of length 2 in r.
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_14 (queens queensT : Slice (alloc.vec.Vec Std.I64))
    (king kingT : Slice Std.I64)
    (hvalid : ValidInput queens king)
    (hT2 : ∀ i : Fin queensT.val.length, (queensT.val.get i).val.length = 2)
    (hTq : queenCoords queensT = (queenCoords queens).map (fun p => (p.2, p.1)))
    (hTk : kingCoord kingT = (kingY king, kingX king)) :
    ∀ r r', queens_attackthe_king queens king = ok r →
      queens_attackthe_king queensT kingT = ok r' →
      ∀ a b, Occurs r' (a, b) ↔ Occurs r (b, a) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (queens queensT : Slice (alloc.vec.Vec Std.I64))
    (king kingT : Slice Std.I64)
    (hvalid : ValidInput queens king)
    (hT2 : ∀ i : Fin queensT.val.length, (queensT.val.get i).val.length = 2)
    (hTq : queenCoords queensT = (queenCoords queens).map (fun p => (p.2, p.1)))
    (hTk : kingCoord kingT = (kingY king, kingX king)), ∀ r r', queens_attackthe_king queens king = ok r →
      queens_attackthe_king queensT kingT = ok r' →
      ∀ a b, Occurs r' (a, b) ↔ Occurs r (b, a)) := by
  sorry

/-- Whenever the function returns a result r, no returned coordinate is the king's square: for every t with 0 <= t < len(r) and len(r[t]) = 2, (r[t][0], r[t][1]) != (king[0], king[1]).
  Preconditions: len(queens) >= 1 and len(queens) < 64; len(king) = 2; for every i with 0 <= i < len(queens), len(queens[i]) = 2; for every i with 0 <= i < len(queens), 0 <= queens[i][0] < 8 and 0 <= queens[i][1] < 8; 0 <= king[0] < 8 and 0 <= king[1] < 8; the positions (queens[i][0], queens[i][1]) for 0 <= i < len(queens) are pairwise distinct, and none of them equals (king[0], king[1]). -/
theorem spec_15 (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king) :
    ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        coord (r.val.get t) ≠ kingCoord king := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (queens : Slice (alloc.vec.Vec Std.I64)) (king : Slice Std.I64)
    (hvalid : ValidInput queens king), ∀ r, queens_attackthe_king queens king = ok r →
      ∀ t : Fin r.val.length, (r.val.get t).val.length = 2 →
        coord (r.val.get t) ≠ kingCoord king) := by
  sorry

end AegisSpec.QueensAttacktheKing
