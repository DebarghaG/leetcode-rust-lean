import Aegis.JudgeCircle.Code.Funs

/-!
# Specifications of `Aegis.JudgeCircle.judge_circle`

LeetCode problem `robot-return-to-origin`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.JudgeCircle

abbrev codeU : Nat := 85

abbrev codeD : Nat := 68

abbrev codeL : Nat := 76

abbrev codeR : Nat := 82

def IsMoveByte (b : Aeneas.Std.U8) : Prop :=
  b.val = codeU ∨ b.val = codeD ∨ b.val = codeL ∨ b.val = codeR

def AllMoveBytes (s : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
  ∀ (i : Nat) (h : i < s.val.length), IsMoveByte (s.val.get ⟨i, h⟩)

def countByte (s : Aeneas.Std.Slice Aeneas.Std.U8) (c : Nat) : Nat :=
  (s.val.map fun b => b.val).countP fun v => v = c

def countU (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat := countByte s codeU

def countD (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat := countByte s codeD

def countL (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat := countByte s codeL

def countR (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat := countByte s codeR

theorem slice_val_length (s : Aeneas.Std.Slice Aeneas.Std.U8) : s.val.length = s.leng :=
  Aeneas.Data.ListN.ListN_length s.list

def byteSliceOfList (l : List Aeneas.Std.U8) (h : l.length ≤ Aeneas.Std.Usize.max) :
    Aeneas.Std.Slice Aeneas.Std.U8 :=
  { leng := l.length, list := Aeneas.Data.ListN.ListN.fromList l, bound := h }

def mapBytes (s : Aeneas.Std.Slice Aeneas.Std.U8) (f : Aeneas.Std.U8 → Aeneas.Std.U8) :
    Aeneas.Std.Slice Aeneas.Std.U8 :=
  byteSliceOfList (s.val.map f) (by
    rw [List.length_map, slice_val_length]
    exact s.bound)

def flipLRByte (b : Aeneas.Std.U8) : Aeneas.Std.U8 :=
  if b.val = codeL then 82#u8 else if b.val = codeR then 76#u8 else b

def flipUDByte (b : Aeneas.Std.U8) : Aeneas.Std.U8 :=
  if b.val = codeU then 68#u8 else if b.val = codeD then 85#u8 else b

def rotByte (b : Aeneas.Std.U8) : Aeneas.Std.U8 :=
  if b.val = codeU then 82#u8
  else if b.val = codeR then 68#u8
  else if b.val = codeD then 76#u8
  else if b.val = codeL then 85#u8
  else b

def flipLR (s : Aeneas.Std.Slice Aeneas.Std.U8) : Aeneas.Std.Slice Aeneas.Std.U8 :=
  mapBytes s flipLRByte

def flipUD (s : Aeneas.Std.Slice Aeneas.Std.U8) : Aeneas.Std.Slice Aeneas.Std.U8 :=
  mapBytes s flipUDByte

def rot (s : Aeneas.Std.Slice Aeneas.Std.U8) : Aeneas.Std.Slice Aeneas.Std.U8 :=
  mapBytes s rotByte

/-- Let U, D, L, R be the numbers of indices i with 0 <= i < len(moves) such that moves[i] = 85 ('U'), moves[i] = 68 ('D'), moves[i] = 76 ('L'), and moves[i] = 82 ('R'), respectively. The function does not fail: there exists a Boolean b such that judge_circle(moves) = Result.ok b. Moreover, b = true if and only if U = D and L = R; equivalently, b = true if and only if the final horizontal displacement R - L and the final vertical displacement U - D are both zero.
  Preconditions: moves is a nonempty byte slice with 1 <= len(moves) <= 20000, and for every i with 0 <= i < len(moves), moves[i] is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_1 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves) :
    ∃ b : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        (b = true ↔ countU moves = countD moves ∧ countL moves = countR moves) ∧
        (b = true ↔
          (countR moves : Int) - (countL moves : Int) = 0 ∧
            (countU moves : Int) - (countD moves : Int) = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves), ∃ b : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        (b = true ↔ countU moves = countD moves ∧ countL moves = countR moves) ∧
        (b = true ↔
          (countR moves : Int) - (countL moves : Int) = 0 ∧
            (countU moves : Int) - (countD moves : Int) = 0)) := by
  sorry

/-- For every input satisfying the preconditions, there exists a Boolean b such that judge_circle(moves) = Result.ok b; the function never returns an error and does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: moves is a nonempty byte slice with 1 <= len(moves) <= 20000, and for every i with 0 <= i < len(moves), moves[i] is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_2 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves) :
    ∃ b : Bool, Aegis.JudgeCircle.judge_circle moves = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves), ∃ b : Bool, Aegis.JudgeCircle.judge_circle moves = ok b) := by
  sorry

/-- For each sequence seq let U(seq), D(seq), L(seq), R(seq) be the numbers of indices i with 0 <= i < len(seq) for which seq[i] = 'U', seq[i] = 'D', seq[i] = 'L', and seq[i] = 'R', respectively. If U(moves) = U(moves'), D(moves) = D(moves'), L(moves) = L(moves'), and R(moves) = R(moves'), then judge_circle(moves) and judge_circle(moves') both return results and their Bool values are equal.
  Preconditions: moves and moves' are byte slices such that 1 <= len(moves), len(moves') <= 20000, and every byte of both slices is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_3 (moves moves' : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_ne' : 1 ≤ moves'.val.length)
    (h_le' : moves'.val.length ≤ 20000) (h_moves : AllMoveBytes moves)
    (h_moves' : AllMoveBytes moves') (hU : countU moves = countU moves')
    (hD : countD moves = countD moves') (hL : countL moves = countL moves')
    (hR : countR moves = countR moves') :
    ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle moves' = ok b' ∧ b = b' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (moves moves' : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_ne' : 1 ≤ moves'.val.length)
    (h_le' : moves'.val.length ≤ 20000) (h_moves : AllMoveBytes moves)
    (h_moves' : AllMoveBytes moves') (hU : countU moves = countU moves')
    (hD : countD moves = countD moves') (hL : countL moves = countL moves')
    (hR : countR moves = countR moves'), ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle moves' = ok b' ∧ b = b') := by
  sorry

/-- Define flipLR(moves) by flipLR(moves)[i] = 'R' when moves[i] = 'L', flipLR(moves)[i] = 'L' when moves[i] = 'R', and flipLR(moves)[i] = moves[i] otherwise. Then judge_circle(moves) and judge_circle(flipLR(moves)) both return results and the returned Bool values are equal.
  Preconditions: moves is a nonempty byte slice with 1 <= len(moves) <= 20000, and for every i with 0 <= i < len(moves), moves[i] is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_4 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves) :
    ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (flipLR moves) = ok b' ∧ b = b' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves), ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (flipLR moves) = ok b' ∧ b = b') := by
  sorry

/-- Define flipUD(moves) by flipUD(moves)[i] = 'D' when moves[i] = 'U', flipUD(moves)[i] = 'U' when moves[i] = 'D', and flipUD(moves)[i] = moves[i] otherwise. Then judge_circle(moves) and judge_circle(flipUD(moves)) both return results and the returned Bool values are equal.
  Preconditions: moves is a nonempty byte slice with 1 <= len(moves) <= 20000, and for every i with 0 <= i < len(moves), moves[i] is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_5 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves) :
    ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (flipUD moves) = ok b' ∧ b = b' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves), ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (flipUD moves) = ok b' ∧ b = b') := by
  sorry

/-- Define rot(moves) by replacing each 'U' with 'R', each 'R' with 'D', each 'D' with 'L', and each 'L' with 'U'. Then judge_circle(moves) and judge_circle(rot(moves)) both return results and the returned Bool values are equal.
  Preconditions: moves is a nonempty byte slice with 1 <= len(moves) <= 20000, and for every i with 0 <= i < len(moves), moves[i] is one of the ASCII bytes 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_6 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves) :
    ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (rot moves) = ok b' ∧ b = b' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_moves : AllMoveBytes moves), ∃ b b' : Bool,
      Aegis.JudgeCircle.judge_circle moves = ok b ∧
        Aegis.JudgeCircle.judge_circle (rot moves) = ok b' ∧ b = b') := by
  sorry

/-- The function does not fail; it returns Result.ok false.
  Preconditions: moves is a byte slice with 1 <= len(moves) <= 20000, len(moves) is odd, and every byte of moves is one of 85 ('U'), 68 ('D'), 76 ('L'), 82 ('R'). -/
theorem spec_7 (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_odd : moves.val.length % 2 = 1)
    (h_moves : AllMoveBytes moves) :
    Aegis.JudgeCircle.judge_circle moves = ok false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (moves : Aeneas.Std.Slice Aeneas.Std.U8) (h_ne : 1 ≤ moves.val.length)
    (h_le : moves.val.length ≤ 20000) (h_odd : moves.val.length % 2 = 1)
    (h_moves : AllMoveBytes moves), Aegis.JudgeCircle.judge_circle moves = ok false) := by
  sorry

end AegisSpec.JudgeCircle
