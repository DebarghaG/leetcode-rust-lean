import Aegis.FinalPositionOfSnake.Code.Funs

/-!
# Specifications of `Aegis.FinalPositionOfSnake.final_position_of_snake`

LeetCode problem `snake-in-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FinalPositionOfSnake

abbrev CmdVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

abbrev CmdSlice : Type := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)

def bytesOf (v : CmdVec) : List Nat := v.val.map (fun b => b.val)

def bytesUP : List Nat := [85, 80]

def bytesRIGHT : List Nat := [82, 73, 71, 72, 84]

def bytesDOWN : List Nat := [68, 79, 87, 78]

def bytesLEFT : List Nat := [76, 69, 70, 84]

def IsCmd (v : CmdVec) : Prop :=
  bytesOf v = bytesUP ∨ bytesOf v = bytesRIGHT ∨
    bytesOf v = bytesDOWN ∨ bytesOf v = bytesLEFT

def delta (v : CmdVec) : Int × Int :=
  if bytesOf v = bytesUP then (-1, 0)
  else if bytesOf v = bytesDOWN then (1, 0)
  else if bytesOf v = bytesLEFT then (0, -1)
  else if bytesOf v = bytesRIGHT then (0, 1)
  else (0, 0)

def stepPos (p : Int × Int) (v : CmdVec) : Int × Int :=
  (p.1 + (delta v).1, p.2 + (delta v).2)

def run (cmds : List CmdVec) : Int × Int := cmds.foldl stepPos (0, 0)

def posAfter (cmds : List CmdVec) (k : Nat) : Int × Int := run (cmds.take k)

def countOf (bytes : List Nat) (cmds : List CmdVec) : Nat :=
  (cmds.filter (fun v => bytesOf v = bytes)).length

def numDOWN (cmds : List CmdVec) : Nat := countOf bytesDOWN cmds

def numUP (cmds : List CmdVec) : Nat := countOf bytesUP cmds

def numRIGHT (cmds : List CmdVec) : Nat := countOf bytesRIGHT cmds

def numLEFT (cmds : List CmdVec) : Nat := countOf bytesLEFT cmds

def InBoard (n : Int) (cmds : List CmdVec) : Prop :=
  ∀ k, k ≤ cmds.length →
    0 ≤ (posAfter cmds k).1 ∧ (posAfter cmds k).1 < n ∧
      0 ≤ (posAfter cmds k).2 ∧ (posAfter cmds k).2 < n

/-- The function returns a result r and r = row*n + col, where (row, col) is obtained as follows. Start with row = 0 and col = 0. For i = 0, 1, ..., len(commands)-1 in order: if commands[i] is "UP", set row := row - 1; if commands[i] is "DOWN", set row := row + 1; if commands[i] is "LEFT", set col := col - 1; if commands[i] is "RIGHT", set col := col + 1. The arithmetic is ordinary integer arithmetic, with no modulo reduction and no boundary check.
  Preconditions: n is an integer with 2 <= n <= 10. commands is a slice of byte vectors with 1 <= len(commands) <= 100. For every i with 0 <= i < len(commands), commands[i] is exactly the ASCII byte string "UP", "RIGHT", "DOWN", or "LEFT". -/
theorem spec_1 (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i]) :
    ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val = (run commands.val).1 * n.val + (run commands.val).2 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i]), ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val = (run commands.val).1 * n.val + (run commands.val).2) := by
  sorry

/-- The function returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: n is an integer with 2 <= n <= 10. commands is a slice of byte vectors with 1 <= len(commands) <= 100. For every i with 0 <= i < len(commands), commands[i] is exactly the ASCII byte string "UP", "RIGHT", "DOWN", or "LEFT". -/
theorem spec_2 (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i]) :
    ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i]), ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r < n*n.
  Preconditions: n is an integer with 2 <= n <= 10. commands is a slice of byte vectors with 1 <= len(commands) <= 100. For every i with 0 <= i < len(commands), commands[i] is exactly the ASCII byte string "UP", "RIGHT", "DOWN", or "LEFT". Let (row_k, col_k) be the position after the first k commands, defined by starting at (0,0) and applying UP=(row-1), DOWN=(row+1), LEFT=(col-1), RIGHT=(col+1). The problem's boundary promise holds: for every k with 0 <= k <= len(commands), 0 <= row_k < n and 0 <= col_k < n. -/
theorem spec_3 (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val) :
    ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        0 ≤ r.val ∧ r.val < n.val * n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val), ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        0 ≤ r.val ∧ r.val < n.val * n.val) := by
  sorry

/-- Let D be the number of "DOWN" commands and U the number of "UP" commands. The function returns a result r and floor(r / n) = D - U, where / denotes integer division of the non-negative r by positive n.
  Preconditions: n is an integer with 2 <= n <= 10. commands is a slice of byte vectors with 1 <= len(commands) <= 100. For every i with 0 <= i < len(commands), commands[i] is exactly the ASCII byte string "UP", "RIGHT", "DOWN", or "LEFT". Let (row_k, col_k) be the position after the first k commands, defined by starting at (0,0) and applying UP=(row-1), DOWN=(row+1), LEFT=(col-1), RIGHT=(col+1). The problem's boundary promise holds: for every k with 0 <= k <= len(commands), 0 <= row_k < n and 0 <= col_k < n. -/
theorem spec_4 (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val) :
    ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val / n.val = (numDOWN commands.val : Int) - (numUP commands.val : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val), ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val / n.val = (numDOWN commands.val : Int) - (numUP commands.val : Int)) := by
  sorry

/-- Let R be the number of "RIGHT" commands and L the number of "LEFT" commands. The function returns a result r and r mod n = R - L, where r mod n is the unique integer in [0, n-1] congruent to r modulo n.
  Preconditions: n is an integer with 2 <= n <= 10. commands is a slice of byte vectors with 1 <= len(commands) <= 100. For every i with 0 <= i < len(commands), commands[i] is exactly the ASCII byte string "UP", "RIGHT", "DOWN", or "LEFT". Let (row_k, col_k) be the position after the first k commands, defined by starting at (0,0) and applying UP=(row-1), DOWN=(row+1), LEFT=(col-1), RIGHT=(col+1). The problem's boundary promise holds: for every k with 0 <= k <= len(commands), 0 <= row_k < n and 0 <= col_k < n. -/
theorem spec_5 (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val) :
    ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val % n.val = (numRIGHT commands.val : Int) - (numLEFT commands.val : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (commands : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_board : InBoard n.val commands.val), ∃ r : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        r.val % n.val = (numRIGHT commands.val : Int) - (numLEFT commands.val : Int)) := by
  sorry

/-- The function returns a result r for (n, commands) and a result r' for (n, commands'), and r = r'.
  Preconditions: n is an integer with 2 <= n <= 10. commands and commands' are slices of byte vectors, each with 1 <= length <= 100. Every element of both slices is exactly "UP", "RIGHT", "DOWN", or "LEFT". commands' is a permutation of commands, i.e. a reordering of the same multiset of commands. -/
theorem spec_6 (n : I64) (commands commands' : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_len'_lo : 1 ≤ commands'.val.length) (h_len'_hi : commands'.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_cmds' : ∀ (i : Nat) (hi : i < commands'.val.length), IsCmd commands'.val[i])
    (h_perm : List.Perm commands.val commands'.val) :
    ∃ r r' : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        Aegis.FinalPositionOfSnake.final_position_of_snake n commands' = ok r' ∧
          r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (commands commands' : CmdSlice)
    (h_n_lo : 2 ≤ n.val) (h_n_hi : n.val ≤ 10)
    (h_len_lo : 1 ≤ commands.val.length) (h_len_hi : commands.val.length ≤ 100)
    (h_len'_lo : 1 ≤ commands'.val.length) (h_len'_hi : commands'.val.length ≤ 100)
    (h_cmds : ∀ (i : Nat) (hi : i < commands.val.length), IsCmd commands.val[i])
    (h_cmds' : ∀ (i : Nat) (hi : i < commands'.val.length), IsCmd commands'.val[i])
    (h_perm : List.Perm commands.val commands'.val), ∃ r r' : I64,
      Aegis.FinalPositionOfSnake.final_position_of_snake n commands = ok r ∧
        Aegis.FinalPositionOfSnake.final_position_of_snake n commands' = ok r' ∧
          r.val = r'.val) := by
  sorry

end AegisSpec.FinalPositionOfSnake
