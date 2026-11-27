import Aegis.CalPoints.Code.Funs

/-!
# Specifications of `Aegis.CalPoints.cal_points`

LeetCode problem `baseball-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.CalPoints

set_option autoImplicit false

namespace AegisSpec.CalPoints

inductive Op where

  | push (x : ℤ)

  | cancel

  | dbl

  | plus
  deriving DecidableEq, Inhabited, Repr

def vecBytes (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def isDigitB (b : Nat) : Bool := 48 ≤ b && b ≤ 57

def digitVal (b : Nat) : Nat := b - 48

def digitsVal (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * 10 + digitVal d) 0

def allDigitsB (ds : List Nat) : Bool := ds.all isDigitB

def natToken? : List Nat → Option Nat
  | [] => none
  | d :: ds => if allDigitsB (d :: ds) then some (digitsVal (d :: ds)) else none

def parseOp : List Nat → Option Op
  | [67] => some Op.cancel
  | [68] => some Op.dbl
  | [43] => some Op.plus
  | 45 :: d :: ds => (natToken? (d :: ds)).map (fun n => Op.push (-(n : ℤ)))
  | bs => (natToken? bs).map (fun n => Op.push (n : ℤ))

def decodeOps (l : List (alloc.vec.Vec Std.U8)) : Option (List Op) :=
  l.mapM fun v => parseOp (vecBytes v)

def i32Min : ℤ := -((2 : ℤ) ^ 31)

def i32Max : ℤ := (2 : ℤ) ^ 31 - 1

def FitsI32 (x : ℤ) : Prop := i32Min ≤ x ∧ x ≤ i32Max

def lastScore (R : List ℤ) : ℤ := R.getLastD 0

def secondLastScore (R : List ℤ) : ℤ := (R.dropLast).getLastD 0

def stepScore (R : List ℤ) : Op → List ℤ
  | .push x => R ++ [x]
  | .cancel => R.dropLast
  | .dbl => if R.isEmpty then R else R ++ [2 * lastScore R]
  | .plus => if R.length < 2 then R else R ++ [lastScore R + secondLastScore R]

def finalRecord (ops : List Op) : List ℤ := ops.foldl stepScore []

def newScores (R : List ℤ) : Op → List ℤ
  | .push x => [x]
  | .cancel => []
  | .dbl => if R.isEmpty then [] else [2 * lastScore R]
  | .plus => if R.length < 2 then [] else [lastScore R + secondLastScore R]

def Enabled (R : List ℤ) : Op → Prop
  | .push _ => True
  | .cancel => R ≠ []
  | .dbl => R ≠ []
  | .plus => 2 ≤ R.length

def AllEnabled (R : List ℤ) : List Op → Prop
  | [] => True
  | op :: ops => Enabled R op ∧ AllEnabled (stepScore R op) ops

def NewScoresFitI32 (R : List ℤ) : List Op → Prop
  | [] => True
  | op :: ops => (∀ v ∈ newScores R op, FitsI32 v) ∧ NewScoresFitI32 (stepScore R op) ops

def tokenValues : List Op → List ℤ
  | [] => []
  | .push x :: ops => x :: tokenValues ops
  | _ :: ops => tokenValues ops

def Insertable (R : List ℤ) : Op → Prop
  | .push x => -30000 ≤ x ∧ x ≤ 30000
  | .cancel => False
  | .dbl => R ≠ []
  | .plus => 2 ≤ R.length

structure Constraints (ops : List Op) : Prop where

  token_bounds : ∀ x ∈ tokenValues ops, -30000 ≤ x ∧ x ≤ 30000

  enabled : AllEnabled [] ops

  new_scores : NewScoresFitI32 [] ops

  sum_bounds : FitsI32 (finalRecord ops).sum

/-- Let R_0 be the empty sequence of scores. For i = 0, ..., len(operations)-1, let R_i be the record before operation i and define R_{i+1} as follows: if operations[i] encodes the integer x, append x to R_i; if operations[i] is "C", delete the last element of R_i; if operations[i] is "D", append 2 * last(R_i); if operations[i] is "+", append last(R_i) + second_last(R_i). Let R = R_len(operations). Whenever cal_points(operations) returns a result r, r is the sum of all elements of R, with the empty sum equal to 0. Here last(R) is R[len(R)-1] and second_last(R) is R[len(R)-2], both 0-indexed.
  Preconditions: 1 <= len(operations) <= 1000. For every i with 0 <= i < len(operations), the byte sequence operations[i] is either the one-byte ASCII encoding of "C", "D", or "+", or the ASCII encoding of a decimal integer token (an optional '-' followed by one or more digits) whose value x_i satisfies -30000 <= x_i <= 30000. Processing operations left to right, every "C" or "D" has at least one previous score, and every "+" has at least two previous scores. Every newly recorded score produced by an operation and the final sum fit in a 32-bit signed integer, i.e. in [-2^31, 2^31-1]. -/
theorem spec_1
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops) :
    ∃ r, cal_points operations = ok r ∧ r.val = (finalRecord ops).sum := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops), ∃ r, cal_points operations = ok r ∧ r.val = (finalRecord ops).sum) := by
  sorry

/-- cal_points(operations) returns a result r. It does not fail, panic, or overflow on inputs satisfying the preconditions.
  Preconditions: The same constraints as in spec_1: 1 <= len(operations) <= 1000; each operation is an ASCII "C", "D", "+", or a decimal integer token in [-30000, 30000]; the operations are valid with respect to the record (enough previous scores for "C", "D", and "+"); every newly recorded score and the final sum fit in a 32-bit signed integer. -/
theorem spec_2
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops) :
    ∃ r, cal_points operations = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops), ∃ r, cal_points operations = ok r) := by
  sorry

/-- Whenever cal_points(operations) returns a result r, r satisfies -2^31 <= r <= 2^31-1.
  Preconditions: The same constraints as in spec_1, including that the final sum and every newly recorded score fit in [-2^31, 2^31-1]. -/
theorem spec_3
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (r : Std.I64) (h_r : cal_points operations = ok r) :
    FitsI32 r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (r : Std.I64) (h_r : cal_points operations = ok r), FitsI32 r.val) := by
  sorry

/-- If the final record R after processing all operations is empty, then whenever cal_points(operations) returns a result r, r = 0.
  Preconditions: The same constraints as in spec_1. -/
theorem spec_4
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_empty : finalRecord ops = [])
    (r : Std.I64) (h_r : cal_points operations = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_empty : finalRecord ops = [])
    (r : Std.I64) (h_r : cal_points operations = ok r), r.val = 0) := by
  sorry

/-- Whenever cal_points(operations) returns a result r, r = x_0 + x_1 + ... + x_{len(operations)-1}.
  Preconditions: 1 <= len(operations) <= 1000. Every operations[i] is the ASCII encoding of a decimal integer x_i with -30000 <= x_i <= 30000; no operation is "C", "D", or "+". -/
theorem spec_5
    (operations : Slice (alloc.vec.Vec Std.U8)) (xs : List ℤ)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some (xs.map Op.push))
    (h_tokens : ∀ x ∈ xs, -30000 ≤ x ∧ x ≤ 30000)
    (r : Std.I64) (h_r : cal_points operations = ok r) :
    r.val = xs.sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (xs : List ℤ)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some (xs.map Op.push))
    (h_tokens : ∀ x ∈ xs, -30000 ≤ x ∧ x ≤ 30000)
    (r : Std.I64) (h_r : cal_points operations = ok r), r.val = xs.sum) := by
  sorry

/-- Let rP be the result of cal_points(P), and let r be the result of cal_points(P followed by [s]). Whenever both calls return results, r = rP + x.
  Preconditions: P is a valid nonempty operation sequence with 1 <= len(P) <= 999. s is the ASCII encoding of a decimal integer x with -30000 <= x <= 30000. The concatenated sequence P followed by [s] satisfies the S1 constraints, including all 32-bit bound promises. Record evolution for P uses the standard rules: integer token appends its value, "D" appends twice the last score, "+" appends the sum of the last two scores, and "C" deletes the last score. -/
theorem spec_6
    (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (s : alloc.vec.Vec Std.U8) (x : ℤ) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_len_le : P.val.length ≤ 999)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_s : parseOp (vecBytes s) = some (Op.push x))
    (h_x : -30000 ≤ x ∧ x ≤ 30000)
    (h_Q_val : Q.val = P.val ++ [s])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.push x]))
    (h_Q_constraints : Constraints (Pops ++ [Op.push x]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r) :
    r.val = rP.val + x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (s : alloc.vec.Vec Std.U8) (x : ℤ) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_len_le : P.val.length ≤ 999)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_s : parseOp (vecBytes s) = some (Op.push x))
    (h_x : -30000 ≤ x ∧ x ≤ 30000)
    (h_Q_val : Q.val = P.val ++ [s])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.push x]))
    (h_Q_constraints : Constraints (Pops ++ [Op.push x]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r), r.val = rP.val + x) := by
  sorry

/-- Let rP be the result of cal_points(P) and let last be the last element of R(P). Whenever both cal_points(P) and cal_points(P followed by ["C"]) return results, the latter result r satisfies r = rP - last.
  Preconditions: P is a valid nonempty operation sequence, the final record R(P) after processing P is nonempty, and P followed by ["C"] satisfies the S1 constraints. Record evolution is the standard one. -/
theorem spec_7
    (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_nonempty : finalRecord Pops ≠ [])
    (c : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_c : parseOp (vecBytes c) = some Op.cancel)
    (h_Q_val : Q.val = P.val ++ [c])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.cancel]))
    (h_Q_constraints : Constraints (Pops ++ [Op.cancel]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r) :
    r.val = rP.val - lastScore (finalRecord Pops) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_nonempty : finalRecord Pops ≠ [])
    (c : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_c : parseOp (vecBytes c) = some Op.cancel)
    (h_Q_val : Q.val = P.val ++ [c])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.cancel]))
    (h_Q_constraints : Constraints (Pops ++ [Op.cancel]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r), r.val = rP.val - lastScore (finalRecord Pops)) := by
  sorry

/-- Let rP be the result of cal_points(P) and let last be the last element of R(P). Whenever both cal_points(P) and cal_points(P followed by ["D"]) return results, the latter result r satisfies r = rP + 2 * last.
  Preconditions: P is a valid nonempty operation sequence, the final record R(P) after processing P is nonempty, and P followed by ["D"] satisfies the S1 constraints. Record evolution is the standard one. -/
theorem spec_8
    (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_nonempty : finalRecord Pops ≠ [])
    (d : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_d : parseOp (vecBytes d) = some Op.dbl)
    (h_Q_val : Q.val = P.val ++ [d])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.dbl]))
    (h_Q_constraints : Constraints (Pops ++ [Op.dbl]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r) :
    r.val = rP.val + 2 * lastScore (finalRecord Pops) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_nonempty : finalRecord Pops ≠ [])
    (d : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_d : parseOp (vecBytes d) = some Op.dbl)
    (h_Q_val : Q.val = P.val ++ [d])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.dbl]))
    (h_Q_constraints : Constraints (Pops ++ [Op.dbl]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r), r.val = rP.val + 2 * lastScore (finalRecord Pops)) := by
  sorry

/-- Let rP be the result of cal_points(P), let last be the last element of R(P), and let second_last be the second-last element of R(P). Whenever both cal_points(P) and cal_points(P followed by ["+"]) return results, the latter result r satisfies r = rP + last + second_last.
  Preconditions: P is a valid nonempty operation sequence, the final record R(P) after processing P has at least two elements, and P followed by ["+"] satisfies the S1 constraints. Record evolution is the standard one. -/
theorem spec_9
    (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_two : 2 ≤ (finalRecord Pops).length)
    (p : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_p : parseOp (vecBytes p) = some Op.plus)
    (h_Q_val : Q.val = P.val ++ [p])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.plus]))
    (h_Q_constraints : Constraints (Pops ++ [Op.plus]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r) :
    r.val = rP.val + lastScore (finalRecord Pops) + secondLastScore (finalRecord Pops) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (h_P_two : 2 ≤ (finalRecord Pops).length)
    (p : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_p : parseOp (vecBytes p) = some Op.plus)
    (h_Q_val : Q.val = P.val ++ [p])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [Op.plus]))
    (h_Q_constraints : Constraints (Pops ++ [Op.plus]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r), r.val = rP.val + lastScore (finalRecord Pops) + secondLastScore (finalRecord Pops)) := by
  sorry

/-- Let rP be the result of cal_points(P), and let r be the result of cal_points(P followed by [op, "C"]). Whenever both calls return results, r = rP.
  Preconditions: P is a valid nonempty operation sequence. op is a valid score-inserting operation after P: either an integer token x in [-30000, 30000], or "D" when R(P) is nonempty, or "+" when R(P) has at least two elements. The sequence P followed by [op, "C"] satisfies the S1 constraints. Record evolution is the standard one. -/
theorem spec_10
    (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (op : Op) (h_op : Insertable (finalRecord Pops) op)
    (s c : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_s : parseOp (vecBytes s) = some op)
    (h_c : parseOp (vecBytes c) = some Op.cancel)
    (h_Q_val : Q.val = P.val ++ [s, c])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [op, Op.cancel]))
    (h_Q_constraints : Constraints (Pops ++ [op, Op.cancel]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r) :
    r.val = rP.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (P : Slice (alloc.vec.Vec Std.U8)) (Pops : List Op)
    (h_P_len_ge : 1 ≤ P.val.length)
    (h_P_decode : decodeOps P.val = some Pops)
    (h_P_constraints : Constraints Pops)
    (op : Op) (h_op : Insertable (finalRecord Pops) op)
    (s c : alloc.vec.Vec Std.U8) (Q : Slice (alloc.vec.Vec Std.U8))
    (h_s : parseOp (vecBytes s) = some op)
    (h_c : parseOp (vecBytes c) = some Op.cancel)
    (h_Q_val : Q.val = P.val ++ [s, c])
    (h_Q_decode : decodeOps Q.val = some (Pops ++ [op, Op.cancel]))
    (h_Q_constraints : Constraints (Pops ++ [op, Op.cancel]))
    (rP r : Std.I64)
    (h_rP : cal_points P = ok rP)
    (h_r : cal_points Q = ok r), r.val = rP.val) := by
  sorry

/-- Whenever cal_points(operations) returns a result r, r >= 0.
  Preconditions: The same constraints as in spec_1, plus the additional restriction that every integer token appearing in operations is nonnegative. -/
theorem spec_11
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_nonneg : ∀ x ∈ tokenValues ops, 0 ≤ x)
    (r : Std.I64) (h_r : cal_points operations = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_nonneg : ∀ x ∈ tokenValues ops, 0 ≤ x)
    (r : Std.I64) (h_r : cal_points operations = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever cal_points(operations) returns a result r, r <= 0.
  Preconditions: The same constraints as in spec_1, plus the additional restriction that every integer token appearing in operations is nonpositive. -/
theorem spec_12
    (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_nonpos : ∀ x ∈ tokenValues ops, x ≤ 0)
    (r : Std.I64) (h_r : cal_points operations = ok r) :
    r.val ≤ 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (operations : Slice (alloc.vec.Vec Std.U8)) (ops : List Op)
    (h_len_ge : 1 ≤ operations.val.length)
    (h_len_le : operations.val.length ≤ 1000)
    (h_decode : decodeOps operations.val = some ops)
    (h_constraints : Constraints ops)
    (h_nonpos : ∀ x ∈ tokenValues ops, x ≤ 0)
    (r : Std.I64) (h_r : cal_points operations = ok r), r.val ≤ 0) := by
  sorry

end AegisSpec.CalPoints
