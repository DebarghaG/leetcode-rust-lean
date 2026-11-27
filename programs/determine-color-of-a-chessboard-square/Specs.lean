import Aegis.SquareIsWhite.Code.Funs

/-!
# Specifications of `Aegis.SquareIsWhite.square_is_white`

LeetCode problem `determine-color-of-a-chessboard-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SquareIsWhite

def byteAt (coordinates : Slice Std.U8) (i : Nat) : Nat :=
  (coordinates.val[i]!).val

def byteOfNat (n : Nat) : Std.U8 := ⟨n⟩

def byteAdd (b : Std.U8) (n : Nat) : Std.U8 :=
  byteOfNat (b.val + n)

def byteSub (b : Std.U8) (n : Nat) : Std.U8 :=
  byteOfNat (b.val - n)

def twoBytes (a b : Std.U8) : Slice Std.U8 where
  leng := 2
  list := Aeneas.Data.ListN.ListN.cons a
    (Aeneas.Data.ListN.ListN.cons b Aeneas.Data.ListN.ListN.nil)
  bound := by
    simp [Usize.max, Usize.numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num

def moveFileRight (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes (byteAdd coordinates.val[0]! 1) coordinates.val[1]!

def moveRankUp (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes coordinates.val[0]! (byteAdd coordinates.val[1]! 1)

def moveFileRightTwo (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes (byteAdd coordinates.val[0]! 2) coordinates.val[1]!

def moveRankUpTwo (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes coordinates.val[0]! (byteAdd coordinates.val[1]! 2)

def moveFileRightRankUp (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes (byteAdd coordinates.val[0]! 1) (byteAdd coordinates.val[1]! 1)

def moveFileRightRankDown (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes (byteAdd coordinates.val[0]! 1) (byteSub coordinates.val[1]! 1)

def swapFileRank (coordinates : Slice Std.U8) : Slice Std.U8 :=
  twoBytes (byteOfNat (97 + (byteAt coordinates 1 - 49)))
    (byteOfNat (49 + (byteAt coordinates 0 - 97)))

/-- The function returns a Boolean result r (i.e., square_is_white(coordinates) = Result.ok r) and r = true if and only if ((coordinates[0] - 97) + (coordinates[1] - 49)) % 2 = 1. Equivalently, letting file = coordinates[0] - 97 (with 'a'=0, ..., 'h'=7) and rank = coordinates[1] - 49 (with '1'=0, ..., '8'=7), the square is white exactly when file + rank is odd.
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 104, and 49 <= coordinates[1] <= 56. -/
theorem spec_1 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    ∃ r : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok r ∧
        (r = true ↔
          ((byteAt coordinates 0 - 97) + (byteAt coordinates 1 - 49)) % 2 = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), ∃ r : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok r ∧
        (r = true ↔
          ((byteAt coordinates 0 - 97) + (byteAt coordinates 1 - 49)) % 2 = 1)) := by
  sorry

/-- For every coordinates satisfying the preconditions, the function does not fail: there exists a Boolean b such that square_is_white(coordinates) = Result.ok b.
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 104, and 49 <= coordinates[1] <= 56. -/
theorem spec_2 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    ∃ b : Bool, Aegis.SquareIsWhite.square_is_white coordinates = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), ∃ b : Bool, Aegis.SquareIsWhite.square_is_white coordinates = ok b) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0]+1, coordinates[1]]. For any Boolean b, if square_is_white(coordinates) = Result.ok b, then square_is_white(coordinates') = Result.ok (not b). In words, moving one file to the right flips the color.
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 103 (so the file is not 'h'), and 49 <= coordinates[1] <= 56. -/
theorem spec_3 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    ∀ b : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok b →
        Aegis.SquareIsWhite.square_is_white (moveFileRight coordinates) = ok (!b) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), ∀ b : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok b →
        Aegis.SquareIsWhite.square_is_white (moveFileRight coordinates) = ok (!b)) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0], coordinates[1]+1]. For any Boolean b, if square_is_white(coordinates) = Result.ok b, then square_is_white(coordinates') = Result.ok (not b). In words, moving one rank up flips the color.
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 104, and 49 <= coordinates[1] <= 55 (so the rank is not '8'). -/
theorem spec_4 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 55) :
    ∀ b : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok b →
        Aegis.SquareIsWhite.square_is_white (moveRankUp coordinates) = ok (!b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 55), ∀ b : Bool,
      Aegis.SquareIsWhite.square_is_white coordinates = ok b →
        Aegis.SquareIsWhite.square_is_white (moveRankUp coordinates) = ok (!b)) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0]+2, coordinates[1]]. Then square_is_white(coordinates) = square_is_white(coordinates').
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 102 (so file+2 is a valid file), and 49 <= coordinates[1] <= 56. -/
theorem spec_5 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 102)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightTwo coordinates) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 102)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightTwo coordinates)) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0], coordinates[1]+2]. Then square_is_white(coordinates) = square_is_white(coordinates').
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 104, and 49 <= coordinates[1] <= 54 (so rank+2 is a valid rank). -/
theorem spec_6 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 54) :
    Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveRankUpTwo coordinates) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 54), Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveRankUpTwo coordinates)) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0]+1, coordinates[1]+1]. Then square_is_white(coordinates) = square_is_white(coordinates').
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 103, and 49 <= coordinates[1] <= 55. -/
theorem spec_7 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 55) :
    Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightRankUp coordinates) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 55), Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightRankUp coordinates)) := by
  sorry

/-- Let coordinates' be the two-element slice [coordinates[0]+1, coordinates[1]-1]. Then square_is_white(coordinates) = square_is_white(coordinates').
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 103, and 50 <= coordinates[1] <= 56. -/
theorem spec_8 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightRankDown coordinates) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 103)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (moveFileRightRankDown coordinates)) := by
  sorry

/-- Let f = coordinates[0] - 97 and r = coordinates[1] - 49. Let coordinates' be the two-element slice [97 + r, 49 + f]. Then square_is_white(coordinates) = square_is_white(coordinates').
  Preconditions: len(coordinates) = 2, 97 <= coordinates[0] <= 104, and 49 <= coordinates[1] <= 56. -/
theorem spec_9 (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56) :
    Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (swapFileRank coordinates) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coordinates : Slice Std.U8)
    (h_len : coordinates.val.length = 2)
    (h_file_lo : 97 ≤ byteAt coordinates 0)
    (h_file_hi : byteAt coordinates 0 ≤ 104)
    (h_rank_lo : 49 ≤ byteAt coordinates 1)
    (h_rank_hi : byteAt coordinates 1 ≤ 56), Aegis.SquareIsWhite.square_is_white coordinates
      = Aegis.SquareIsWhite.square_is_white (swapFileRank coordinates)) := by
  sorry

end AegisSpec.SquareIsWhite
