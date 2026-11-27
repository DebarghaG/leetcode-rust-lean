import Aegis.FurthestDistanceFromOrigin.Code.Funs

/-!
# Specifications of `Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin`

LeetCode problem `furthest-point-from-origin`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FurthestDistanceFromOrigin

def occurrenceCount (l : List Std.U8) (b : Std.U8) : Nat := l.count b

def countL (l : List Std.U8) : Nat := occurrenceCount l 76#u8

def countR (l : List Std.U8) : Nat := occurrenceCount l 82#u8

def countU (l : List Std.U8) : Nat := occurrenceCount l 95#u8

def iabs (x : ℤ) : ℤ := (x.natAbs : ℤ)

def closedForm (l : List Std.U8) : ℤ :=
  iabs ((countR l : ℤ) - (countL l : ℤ)) + (countU l : ℤ)

def closedFormMax (l : List Std.U8) : ℤ :=
  max (iabs ((countR l : ℤ) - (countL l : ℤ) - (countU l : ℤ)))
    (iabs ((countR l : ℤ) - (countL l : ℤ) + (countU l : ℤ)))

def swapByte (b : Std.U8) : Std.U8 :=
  if b = 76#u8 then 82#u8 else if b = 82#u8 then 76#u8 else b

def swapLR (l : List Std.U8) : List Std.U8 := l.map swapByte

def IsDirAssignment (l : List Std.U8) (d : Nat → ℤ) : Prop :=
  ∀ i, i < l.length →
    (l[i]? = some 76#u8 → d i = -1) ∧
      (l[i]? = some 82#u8 → d i = 1) ∧ (l[i]? = some 95#u8 → d i = 1 ∨ d i = -1)

def totalDisplacement (l : List Std.U8) (d : Nat → ℤ) : ℤ :=
  ((List.range l.length).map d).sum

/-- Let cL, cR, and cU be the numbers of indices i with 0 <= i < len(moves) for which moves[i] is 'L', 'R', and '_', respectively. Whenever the function returns a result r, r = |cR - cL| + cU.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_1 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val = closedForm moves.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val = closedForm moves.val) := by
  sorry

/-- The function returns a result r for every moves satisfying the preconditions; it does not fail, panic, access out of bounds, or overflow.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_2 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∃ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∃ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(moves).
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_3 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      0 ≤ r.val ∧ r.val ≤ (moves.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      0 ≤ r.val ∧ r.val ≤ (moves.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r and len(moves) have the same parity: r mod 2 = len(moves) mod 2.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_4 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val % 2 = (moves.val.length : ℤ) % 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val % 2 = (moves.val.length : ℤ) % 2) := by
  sorry

/-- For each index i with 0 <= i < len(moves), define a direction d_i by d_i = -1 when moves[i] is 'L', d_i = +1 when moves[i] is 'R', and for moves[i] = '_' choose d_i to be either -1 or +1. Whenever the function returns a result r, there exists such a choice of the d_i for all underscore positions for which |sum_{i=0}^{len(moves)-1} d_i| = r.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_5 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      ∃ d, IsDirAssignment moves.val d ∧ iabs (totalDisplacement moves.val d) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      ∃ d, IsDirAssignment moves.val d ∧ iabs (totalDisplacement moves.val d) = r.val) := by
  sorry

/-- For every choice of a direction d_i in {-1, +1} for each underscore position, with d_i = -1 for each 'L' and d_i = +1 for each 'R', let p = sum_{i=0}^{len(moves)-1} d_i. Whenever the function returns a result r, |p| <= r for every such choice.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_6 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      ∀ d, IsDirAssignment moves.val d →
        iabs (totalDisplacement moves.val d) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      ∀ d, IsDirAssignment moves.val d →
        iabs (totalDisplacement moves.val d) ≤ r.val) := by
  sorry

/-- Let cL, cR, and cU be the numbers of 'L', 'R', and '_' bytes in moves. Whenever the function returns a result r, r = max(|cR - cL - cU|, |cR - cL + cU|).
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_7 (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8) :
    ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val = closedFormMax moves.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (moves : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8), ∀ r, Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      r.val = closedFormMax moves.val) := by
  sorry

/-- Let sw be the slice obtained from moves by replacing every 'L' byte with 'R' and every 'R' byte with 'L', leaving '_' unchanged. Whenever the function returns r on moves and r' on sw, r = r'.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_8 (moves sw : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_sw : sw.val = swapLR moves.val) :
    ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin sw = ok r' →
        r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (moves sw : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_sw : sw.val = swapLR moves.val), ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin sw = ok r' →
        r.val = r'.val) := by
  sorry

/-- For every index k with 0 <= k < len(moves) such that moves[k] is 'L' or 'R', let moves' be the slice obtained from moves by changing only position k to '_' and leaving every other byte unchanged. Whenever the function returns r on moves and r' on moves', r' >= r.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_9 (moves moves' : Slice Std.U8) (k : Nat)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_k : k < moves.val.length)
    (h_k_byte : moves.val[k]? = some 76#u8 ∨ moves.val[k]? = some 82#u8)
    (h_moves' : moves'.val = moves.val.set k 95#u8) :
    ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves' = ok r' →
        r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (moves moves' : Slice Std.U8) (k : Nat)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_k : k < moves.val.length)
    (h_k_byte : moves.val[k]? = some 76#u8 ∨ moves.val[k]? = some 82#u8)
    (h_moves' : moves'.val = moves.val.set k 95#u8), ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves' = ok r' →
        r.val ≤ r'.val) := by
  sorry

/-- Let perm be any slice of the same length as moves such that the number of occurrences of each of the bytes 'L', 'R', and '_' in perm equals its number of occurrences in moves. Whenever the function returns r on moves and r' on perm, r = r'.
  Preconditions: len(moves) >= 1, len(moves) <= 50, and for every i with 0 <= i < len(moves), moves[i] is the ASCII byte for one of 'L', 'R', or '_'. -/
theorem spec_10 (moves perm : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_perm_len : perm.val.length = moves.val.length)
    (h_perm_L : countL perm.val = countL moves.val)
    (h_perm_R : countR perm.val = countR moves.val)
    (h_perm_U : countU perm.val = countU moves.val) :
    ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin perm = ok r' →
        r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (moves perm : Slice Std.U8)
    (h_len_pos : 1 ≤ moves.val.length) (h_len_le : moves.val.length ≤ 50)
    (h_bytes : ∀ i, i < moves.val.length →
      moves.val[i]? = some 76#u8 ∨ moves.val[i]? = some 82#u8 ∨
        moves.val[i]? = some 95#u8)
    (h_perm_len : perm.val.length = moves.val.length)
    (h_perm_L : countL perm.val = countL moves.val)
    (h_perm_R : countR perm.val = countR moves.val)
    (h_perm_U : countU perm.val = countU moves.val), ∀ r r', Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin moves = ok r →
      Aegis.FurthestDistanceFromOrigin.furthest_distance_from_origin perm = ok r' →
        r.val = r'.val) := by
  sorry

end AegisSpec.FurthestDistanceFromOrigin
