import Aegis.CheckTwoChessboards.Code.Funs

/-!
# Specifications of `Aegis.CheckTwoChessboards.check_two_chessboards`

LeetCode problem `check-if-two-chessboard-squares-have-the-same-color`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckTwoChessboards

open Aegis.CheckTwoChessboards
open Aeneas.Data.ListN

def byteAt (s : Slice U8) (i : Nat) : Nat :=
  ((s.val[i]?).map UScalar.val).getD 0

def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

private lemma two_le_usize_max : 2 ≤ Aeneas.Std.Usize.max := by
  have h : (2 : Nat) ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have h4 : (2 : Nat) ^ 2 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) h
  have h3 : (3 : Nat) ≤ 2 ^ System.Platform.numBits := by
    norm_num at h4
    omega
  simp only [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits, Aeneas.Std.UScalarTy.numBits]
    at h3 ⊢
  omega

def slice2 (b0 b1 : U8) : Slice U8 :=
  Slice.mk 2 (ListN.cons b0 (ListN.cons b1 ListN.nil)) two_le_usize_max

def shiftBoth (dc dr : Nat) (x : Slice U8) : Slice U8 :=
  slice2 (byte (byteAt x 0 + dc)) (byte (byteAt x 1 + dr))

def shiftCol (d : Nat) (x : Slice U8) : Slice U8 :=
  shiftBoth d 0 x

def shiftRow (d : Nat) (x : Slice U8) : Slice U8 :=
  shiftBoth 0 d x

def transpose (x : Slice U8) : Slice U8 :=
  slice2 (byte ('a'.toNat + (byteAt x 1 - '1'.toNat)))
    (byte ('1'.toNat + (byteAt x 0 - 'a'.toNat)))

def mirrorCol (x : Slice U8) : Slice U8 :=
  slice2 (byte ('a'.toNat + 'h'.toNat - byteAt x 0)) (byte (byteAt x 1))

def mirrorRow (x : Slice U8) : Slice U8 :=
  slice2 (byte (byteAt x 0)) (byte ('1'.toNat + '8'.toNat - byteAt x 1))

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r, r = true if and only if ((coordinate1[0] - 'a') + (coordinate1[1] - '1')) mod 2 = ((coordinate2[0] - 'a') + (coordinate2[1] - '1')) mod 2. Here coordinate[0] - 'a' is the 0-based column index and coordinate[1] - '1' is the 0-based row index; squares have the same color exactly when these parity values are equal.
  Preconditions: len(coordinate1) = 2 and len(coordinate2) = 2 and 'a' ≤ coordinate1[0] ≤ 'h' and '1' ≤ coordinate1[1] ≤ '8' and 'a' ≤ coordinate2[0] ≤ 'h' and '1' ≤ coordinate2[1] ≤ '8' (all comparisons on ASCII byte codes). -/
theorem spec_1
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r) :
    (r = true ↔
      ((byteAt coordinate1 0 - 'a'.toNat) + (byteAt coordinate1 1 - '1'.toNat)) % 2 =
        ((byteAt coordinate2 0 - 'a'.toNat) + (byteAt coordinate2 1 - '1'.toNat)) % 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r), (r = true ↔
      ((byteAt coordinate1 0 - 'a'.toNat) + (byteAt coordinate1 1 - '1'.toNat)) % 2 =
        ((byteAt coordinate2 0 - 'a'.toNat) + (byteAt coordinate2 1 - '1'.toNat)) % 2)) := by
  sorry

/-- There exists a Boolean r such that check_two_chessboards coordinate1 coordinate2 = Result.ok r. In particular, on these valid inputs the function does not fail, panic, overflow, or access out of bounds.
  Preconditions: len(coordinate1) = 2 and len(coordinate2) = 2 and 'a' ≤ coordinate1[0] ≤ 'h' and '1' ≤ coordinate1[1] ≤ '8' and 'a' ≤ coordinate2[0] ≤ 'h' and '1' ≤ coordinate2[1] ≤ '8' (all comparisons on ASCII byte codes). -/
theorem spec_2
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat) :
    ∃ r : Bool, check_two_chessboards coordinate1 coordinate2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat), ∃ r : Bool, check_two_chessboards coordinate1 coordinate2 = ok r) := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r1 and check_two_chessboards coordinate2 coordinate1 returns Result.ok r2, we have r1 = r2. Thus the answer is symmetric in its two arguments.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates: len(coordinate1) = len(coordinate2) = 2, 'a' ≤ coordinate1[0] ≤ 'h', '1' ≤ coordinate1[1] ≤ '8', 'a' ≤ coordinate2[0] ≤ 'h', and '1' ≤ coordinate2[1] ≤ '8' (ASCII byte codes). -/
theorem spec_3
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r1 r2 : Bool)
    (hr1 : check_two_chessboards coordinate1 coordinate2 = ok r1)
    (hr2 : check_two_chessboards coordinate2 coordinate1 = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r1 r2 : Bool)
    (hr1 : check_two_chessboards coordinate1 coordinate2 = ok r1)
    (hr2 : check_two_chessboards coordinate2 coordinate1 = ok r2), r1 = r2) := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r12, check_two_chessboards coordinate2 coordinate3 returns Result.ok r23, and check_two_chessboards coordinate1 coordinate3 returns Result.ok r13, if r12 = true and r23 = true then r13 = true. That is, the same-color relation computed by the function is transitive on valid squares.
  Preconditions: coordinate1, coordinate2, and coordinate3 are valid chessboard coordinates: each has length 2, its first byte is between 'a' and 'h', and its second byte is between '1' and '8' (ASCII byte codes). -/
theorem spec_4
    (coordinate1 coordinate2 coordinate3 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h3_len : coordinate3.val.length = 2)
    (h3_col_lo : 'a'.toNat ≤ byteAt coordinate3 0)
    (h3_col_hi : byteAt coordinate3 0 ≤ 'h'.toNat)
    (h3_row_lo : '1'.toNat ≤ byteAt coordinate3 1)
    (h3_row_hi : byteAt coordinate3 1 ≤ '8'.toNat)
    (r12 r23 r13 : Bool)
    (hr12 : check_two_chessboards coordinate1 coordinate2 = ok r12)
    (hr23 : check_two_chessboards coordinate2 coordinate3 = ok r23)
    (hr13 : check_two_chessboards coordinate1 coordinate3 = ok r13)
    (h12 : r12 = true) (h23 : r23 = true) :
    r13 = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coordinate1 coordinate2 coordinate3 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h3_len : coordinate3.val.length = 2)
    (h3_col_lo : 'a'.toNat ≤ byteAt coordinate3 0)
    (h3_col_hi : byteAt coordinate3 0 ≤ 'h'.toNat)
    (h3_row_lo : '1'.toNat ≤ byteAt coordinate3 1)
    (h3_row_hi : byteAt coordinate3 1 ≤ '8'.toNat)
    (r12 r23 r13 : Bool)
    (hr12 : check_two_chessboards coordinate1 coordinate2 = ok r12)
    (hr23 : check_two_chessboards coordinate2 coordinate3 = ok r23)
    (hr13 : check_two_chessboards coordinate1 coordinate3 = ok r13)
    (h12 : r12 = true) (h23 : r23 = true), r13 = true) := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1 coordinate2' returns Result.ok r', we have r' = not r. Thus moving exactly one column to the right reverses whether the two squares have the same color.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, and coordinate2[0] < 'h' (ASCII byte code). Let coordinate2' be the coordinate with coordinate2'[0] = coordinate2[0] + 1 and coordinate2'[1] = coordinate2[1]; this coordinate2' is also valid. -/
theorem spec_5
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftCol 1 coordinate2) = ok r') :
    r' = !r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftCol 1 coordinate2) = ok r'), r' = !r) := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1 coordinate2' returns Result.ok r', we have r' = not r. Thus moving exactly one row upward reverses whether the two squares have the same color.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, and coordinate2[1] < '8' (ASCII byte code). Let coordinate2' be the coordinate with coordinate2'[0] = coordinate2[0] and coordinate2'[1] = coordinate2[1] + 1; this coordinate2' is also valid. -/
theorem spec_6
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftRow 1 coordinate2) = ok r') :
    r' = !r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftRow 1 coordinate2) = ok r'), r' = !r) := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1 coordinate2' returns Result.ok r', we have r = r'. Thus moving one square of the pair exactly two columns right does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, and coordinate2[0] ≤ 'f' (ASCII byte code). Let coordinate2' be the coordinate with coordinate2'[0] = coordinate2[0] + 2 and coordinate2'[1] = coordinate2[1]; this coordinate2' is also valid. -/
theorem spec_7
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_le : byteAt coordinate2 0 ≤ 'f'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftCol 2 coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_le : byteAt coordinate2 0 ≤ 'f'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftCol 2 coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1 coordinate2' returns Result.ok r', we have r = r'. Thus moving one square of the pair exactly two rows up does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, and coordinate2[1] ≤ '6' (ASCII byte code). Let coordinate2' be the coordinate with coordinate2'[0] = coordinate2[0] and coordinate2'[1] = coordinate2[1] + 2; this coordinate2' is also valid. -/
theorem spec_8
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_row_le : byteAt coordinate2 1 ≤ '6'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftRow 2 coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_row_le : byteAt coordinate2 1 ≤ '6'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftRow 2 coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1' coordinate2' returns Result.ok r', we have r = r'. Thus translating both squares exactly one column right does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, coordinate1[0] < 'h', and coordinate2[0] < 'h' (ASCII byte codes). Let coordinate1' and coordinate2' be the coordinates obtained from coordinate1 and coordinate2 by adding 1 to their column letter and leaving their row digit unchanged; both are valid. -/
theorem spec_9
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h1_col_lt : byteAt coordinate1 0 < 'h'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (shiftCol 1 coordinate1) (shiftCol 1 coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h1_col_lt : byteAt coordinate1 0 < 'h'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (shiftCol 1 coordinate1) (shiftCol 1 coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1' coordinate2' returns Result.ok r', we have r = r'. Thus translating both squares exactly one row up does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, coordinate1[1] < '8', and coordinate2[1] < '8' (ASCII byte codes). Let coordinate1' and coordinate2' be the coordinates obtained from coordinate1 and coordinate2 by adding 1 to their row digit and leaving their column letter unchanged; both are valid. -/
theorem spec_10
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h1_row_lt : byteAt coordinate1 1 < '8'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (shiftRow 1 coordinate1) (shiftRow 1 coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h1_row_lt : byteAt coordinate1 1 < '8'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (shiftRow 1 coordinate1) (shiftRow 1 coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards coordinate1 coordinate2' returns Result.ok r', we have r = r'. Thus moving one square of the pair one step northeast (one column right and one row up) does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates, coordinate2[0] < 'h', and coordinate2[1] < '8' (ASCII byte codes). Let coordinate2' be the coordinate obtained from coordinate2 by adding 1 to its column letter and adding 1 to its row digit, leaving the other fields unchanged; coordinate2' is valid. -/
theorem spec_11
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftBoth 1 1 coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (h2_col_lt : byteAt coordinate2 0 < 'h'.toNat)
    (h2_row_lt : byteAt coordinate2 1 < '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards coordinate1 (shiftBoth 1 1 coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards transpose(coordinate1) transpose(coordinate2) returns Result.ok r', we have r = r'. Thus reflecting both squares across the main diagonal of the chessboard does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates. For a valid coordinate x, define transpose(x) to be the valid coordinate with transpose(x)[0] = 'a' + (x[1] - '1') and transpose(x)[1] = '1' + (x[0] - 'a'). -/
theorem spec_12
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (transpose coordinate1) (transpose coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (transpose coordinate1) (transpose coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards mirror_col(coordinate1) mirror_col(coordinate2) returns Result.ok r', we have r = r'. Thus reflecting both squares across the vertical middle of the board does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates. For a valid coordinate x, define mirror_col(x) to be the valid coordinate obtained by replacing x's column letter using a ↔ h, b ↔ g, c ↔ f, d ↔ e, e ↔ d, f ↔ c, g ↔ b, h ↔ a, and leaving the row digit unchanged. -/
theorem spec_13
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (mirrorCol coordinate1) (mirrorCol coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (mirrorCol coordinate1) (mirrorCol coordinate2) = ok r'), r = r') := by
  sorry

/-- Whenever check_two_chessboards coordinate1 coordinate2 returns Result.ok r and check_two_chessboards mirror_row(coordinate1) mirror_row(coordinate2) returns Result.ok r', we have r = r'. Thus reflecting both squares across the horizontal middle of the board does not change the answer.
  Preconditions: coordinate1 and coordinate2 are valid chessboard coordinates. For a valid coordinate x, define mirror_row(x) to be the valid coordinate obtained by replacing x's row digit using 1 ↔ 8, 2 ↔ 7, 3 ↔ 6, 4 ↔ 5, 5 ↔ 4, 6 ↔ 3, 7 ↔ 2, 8 ↔ 1, and leaving the column letter unchanged. -/
theorem spec_14
    (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (mirrorRow coordinate1) (mirrorRow coordinate2) = ok r') :
    r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (coordinate1 coordinate2 : Slice U8)
    (h1_len : coordinate1.val.length = 2)
    (h1_col_lo : 'a'.toNat ≤ byteAt coordinate1 0)
    (h1_col_hi : byteAt coordinate1 0 ≤ 'h'.toNat)
    (h1_row_lo : '1'.toNat ≤ byteAt coordinate1 1)
    (h1_row_hi : byteAt coordinate1 1 ≤ '8'.toNat)
    (h2_len : coordinate2.val.length = 2)
    (h2_col_lo : 'a'.toNat ≤ byteAt coordinate2 0)
    (h2_col_hi : byteAt coordinate2 0 ≤ 'h'.toNat)
    (h2_row_lo : '1'.toNat ≤ byteAt coordinate2 1)
    (h2_row_hi : byteAt coordinate2 1 ≤ '8'.toNat)
    (r r' : Bool)
    (hr : check_two_chessboards coordinate1 coordinate2 = ok r)
    (hr' : check_two_chessboards (mirrorRow coordinate1) (mirrorRow coordinate2) = ok r'), r = r') := by
  sorry

end AegisSpec.CheckTwoChessboards
