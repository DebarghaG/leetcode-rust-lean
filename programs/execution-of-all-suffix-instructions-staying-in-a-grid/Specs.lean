import Aegis.ExecuteInstructions.Code.Funs

/-!
# Specifications of `Aegis.ExecuteInstructions.execute_instructions`

LeetCode problem `execution-of-all-suffix-instructions-staying-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ExecuteInstructions

def IsInstructionByte (b : Std.U8) : Prop :=
  b.val = 76 ∨ b.val = 82 ∨ b.val = 85 ∨ b.val = 68

def step (p : Int × Int) (b : Nat) : Int × Int :=
  if b = 76 then (p.1, p.2 - 1)
  else if b = 82 then (p.1, p.2 + 1)
  else if b = 85 then (p.1 - 1, p.2)
  else (p.1 + 1, p.2)

def cellAfter (p : Int × Int) (bs : List Nat) : Int × Int :=
  bs.foldl step p

def codeList (bs : List Std.U8) : List Nat :=
  bs.map fun b => b.val

def instrsFrom (s : Slice Std.U8) (i : Nat) : List Nat :=
  codeList (s.val.drop i)

def Inside (n : Int) (p : Int × Int) : Prop :=
  0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < n

def StaysInside (n : Int) (p : Int × Int) (bs : List Nat) : Prop :=
  ∀ k, k ≤ bs.length → Inside n (cellAfter p (bs.take k))

def startCell? (startPos : Slice Std.I64) : Option (Int × Int) :=
  match startPos.val with
  | a :: b :: _ => some (a.val, b.val)
  | _ => none

/-- Whenever the function returns a result r, len(r) = len(s), and for every i with 0 <= i < len(s), r[i] is the largest integer k with 0 <= k <= len(s)-i such that, if the robot starts at (startPos[0], startPos[1]) and executes s[i], s[i+1], ..., s[i+k-1] in order (L: column-1, R: column+1, U: row-1, D: row+1), then after each of these k instructions its cell (row, col) satisfies 0 <= row < n and 0 <= col < n. The case k=0 is vacuously true.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_1 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    r.val.length = s.val.length ∧
      ∀ i, i < s.val.length →
        ∃ (k : Std.I64) (kn : Nat),
          r.val[i]? = some k ∧
            k.val = (kn : Int) ∧
            kn ≤ (instrsFrom s i).length ∧
            StaysInside n.val st ((instrsFrom s i).take kn) ∧
            (∀ kn' : Nat,
              kn' ≤ (instrsFrom s i).length →
                StaysInside n.val st ((instrsFrom s i).take kn') → kn' ≤ kn) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    r.val.length = s.val.length ∧
      ∀ i, i < s.val.length →
        ∃ (k : Std.I64) (kn : Nat),
          r.val[i]? = some k ∧
            k.val = (kn : Int) ∧
            kn ≤ (instrsFrom s i).length ∧
            StaysInside n.val st ((instrsFrom s i).take kn) ∧
            (∀ kn' : Nat,
              kn' ≤ (instrsFrom s i).length →
                StaysInside n.val st ((instrsFrom s i).take kn') → kn' ≤ kn)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_2 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(s).
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_3 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    r.val.length = s.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    r.val.length = s.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), 0 <= r[i].
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_4 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ i, i < s.val.length →
      ∃ k : Std.I64, r.val[i]? = some k ∧ 0 ≤ k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ i, i < s.val.length →
      ∃ k : Std.I64, r.val[i]? = some k ∧ 0 ≤ k.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), r[i] <= len(s)-i.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_5 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ i, i < s.val.length →
      ∃ k : Std.I64,
        r.val[i]? = some k ∧ k.val ≤ (s.val.length : Int) - (i : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ i, i < s.val.length →
      ∃ k : Std.I64,
        r.val[i]? = some k ∧ k.val ≤ (s.val.length : Int) - (i : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), r[i] = 0 if and only if the move from (startPos[0], startPos[1]) in direction s[i] has resulting row < 0 or >= n or resulting column < 0 or >= n.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_6 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (b : Std.U8) (k : Std.I64),
      i < s.val.length →
        s.val[i]? = some b →
          r.val[i]? = some k → (k.val = 0 ↔ ¬ Inside n.val (step st b.val)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (b : Std.U8) (k : Std.I64),
      i < s.val.length →
        s.val[i]? = some b →
          r.val[i]? = some k → (k.val = 0 ↔ ¬ Inside n.val (step st b.val))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), r[i] = len(s)-i if and only if executing s[i], s[i+1], ..., s[len(s)-1] in order from (startPos[0], startPos[1]) keeps the robot inside the grid after every one of these instructions, i.e. after each step 0 <= row < n and 0 <= col < n.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_7 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64),
      i < s.val.length →
        r.val[i]? = some k →
          (k.val = (s.val.length : Int) - (i : Int) ↔ StaysInside n.val st (instrsFrom s i)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64),
      i < s.val.length →
        r.val[i]? = some k →
          (k.val = (s.val.length : Int) - (i : Int) ↔ StaysInside n.val st (instrsFrom s i))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), let k = r[i]. Then for every t with 1 <= t <= k, the cell reached by starting at (startPos[0], startPos[1]) and executing s[i], s[i+1], ..., s[i+t-1] in order satisfies 0 <= row < n and 0 <= col < n.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_8 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64) (t : Nat),
      i < s.val.length →
        r.val[i]? = some k →
          1 ≤ t → (t : Int) ≤ k.val → Inside n.val (cellAfter st ((instrsFrom s i).take t)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64) (t : Nat),
      i < s.val.length →
        r.val[i]? = some k →
          1 ≤ t → (t : Int) ≤ k.val → Inside n.val (cellAfter st ((instrsFrom s i).take t))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), let k = r[i]. If i+k < len(s), then executing the one further instruction s[i+k] from the cell reached after the first k instructions from start index i would leave the grid, i.e. its resulting row is < 0 or >= n or its resulting column is < 0 or >= n.
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_9 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64) (b : Std.U8),
      i < s.val.length →
        r.val[i]? = some k →
          i + k.val.toNat < s.val.length →
            s.val[i + k.val.toNat]? = some b →
              ¬ Inside n.val
                (step (cellAfter st ((instrsFrom s i).take k.val.toNat)) b.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ∀ (i : Nat) (k : Std.I64) (b : Std.U8),
      i < s.val.length →
        r.val[i]? = some k →
          i + k.val.toNat < s.val.length →
            s.val[i + k.val.toNat]? = some b →
              ¬ Inside n.val
                (step (cellAfter st ((instrsFrom s i).take k.val.toNat)) b.val)) := by
  sorry

/-- Whenever the function returns a result r, r[i] = 0 for every i with 0 <= i < len(s) if and only if for every i with 0 <= i < len(s), moving one step from (startPos[0], startPos[1]) in direction s[i] leaves the grid (resulting row < 0 or >= n or resulting column < 0 or >= n).
  Preconditions: Let m = len(s). n satisfies 1 <= n <= 500. startPos has length 2 and 0 <= startPos[0] < n and 0 <= startPos[1] < n. m satisfies 1 <= m <= 500. For every j with 0 <= j < m, s[j] is the ASCII byte for one of 'L', 'R', 'U', 'D'. -/
theorem spec_10 (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b) :
    Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ((∀ (i : Nat) (k : Std.I64), i < s.val.length → r.val[i]? = some k → k.val = 0) ↔
      ∀ (i : Nat) (b : Std.U8),
        i < s.val.length → s.val[i]? = some b → ¬ Inside n.val (step st b.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (startPos : Slice Std.I64) (s : Slice Std.U8)
    (st : Int × Int) (r : alloc.vec.Vec Std.I64)
    (hn : 1 ≤ n.val ∧ n.val ≤ 500)
    (hstart_len : startPos.val.length = 2)
    (hst : startCell? startPos = some st)
    (hin : Inside n.val st)
    (hm : 1 ≤ s.val.length ∧ s.val.length ≤ 500)
    (hdir : ∀ (j : Nat) (b : Std.U8), s.val[j]? = some b → IsInstructionByte b), Aegis.ExecuteInstructions.execute_instructions n startPos s = ok r →
    ((∀ (i : Nat) (k : Std.I64), i < s.val.length → r.val[i]? = some k → k.val = 0) ↔
      ∀ (i : Nat) (b : Std.U8),
        i < s.val.length → s.val[i]? = some b → ¬ Inside n.val (step st b.val))) := by
  sorry

end AegisSpec.ExecuteInstructions
