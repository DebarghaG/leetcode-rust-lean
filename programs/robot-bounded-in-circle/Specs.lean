import Mathlib
import Aegis.IsRobotBounded.Code.Funs

/-!
# Specifications of `Aegis.IsRobotBounded.is_robot_bounded`

LeetCode problem `robot-bounded-in-circle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsRobotBounded

namespace AegisSpec.IsRobotBounded

def IsInstrByte (b : Std.U8) : Prop := b.val = 71 ∨ b.val = 76 ∨ b.val = 82

def ValidInstructions (instructions : Slice Std.U8) : Prop :=
  1 ≤ instructions.val.length ∧ instructions.val.length ≤ 100 ∧
    ∀ (i : ℕ) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)

structure RoboState where
  x : Int
  y : Int
  dir : Int
  deriving DecidableEq, Repr

def RoboState.origin : RoboState := ⟨0, 0, 0⟩

def move (x y d : Int) : Int × Int :=
  if d = 0 then (x, y + 1)
  else if d = 1 then (x + 1, y)
  else if d = 2 then (x, y - 1)
  else (x - 1, y)

def turn (c : Std.U8) (d : Int) : Int :=
  if c.val = 71 then d
  else if c.val = 76 then (d + 3) % 4
  else if c.val = 82 then (d + 1) % 4
  else d

def step (c : Std.U8) (s : RoboState) : RoboState :=
  if c.val = 71 then
    let p := move s.x s.y s.dir
    ⟨p.1, p.2, s.dir⟩
  else ⟨s.x, s.y, turn c s.dir⟩

def runList (s : RoboState) (l : List Std.U8) : RoboState :=
  l.foldl (fun s c => step c s) s

def instrAt (l : List Std.U8) (t : Nat) : Std.U8 :=
  if h : 0 < l.length then l.get ⟨t % l.length, Nat.mod_lt t h⟩ else 0#u8

def stateAt (l : List Std.U8) : Nat → RoboState
  | 0 => RoboState.origin
  | (t + 1) => step (instrAt l t) (stateAt l t)

def posAt (l : List Std.U8) (t : Nat) : Int × Int := ((stateAt l t).x, (stateAt l t).y)

def posSet (l : List Std.U8) : Set (Int × Int) := {p | ∃ t : Nat, posAt l t = p}

def onePass (l : List Std.U8) : RoboState := runList RoboState.origin l

def endX (l : List Std.U8) : Int := (onePass l).x

def endY (l : List Std.U8) : Int := (onePass l).y

def endDir (l : List Std.U8) : Int := (onePass l).dir

def sqDistR (p : Int × Int) : ℝ := (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2

def BoundedTrajectory (l : List Std.U8) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ ∀ t : Nat, sqDistR (posAt l t) ≤ R ^ 2

def rotate (l : List Std.U8) (k : Nat) : List Std.U8 :=
  l.drop (k % l.length) ++ l.take (k % l.length)

def countL (l : List Std.U8) : Nat := l.countP fun b => b.val == 76

def countR (l : List Std.U8) : Nat := l.countP fun b => b.val == 82

def turnBalance (l : List Std.U8) : Int := (countL l : Int) - (countR l : Int)

def swapByte (b : Std.U8) : Std.U8 :=
  if b.val = 76 then 82#u8 else if b.val = 82 then 76#u8 else b

def swapLR (l : List Std.U8) : List Std.U8 := l.map swapByte

/-- The function returns a result r (it does not fail), and r = true if and only if there exists a nonnegative real number R such that, in the infinite execution starting at (0,0) facing north where at time t >= 0 the robot executes instructions[t mod len(instructions)], every reached position (x_t, y_t) satisfies x_t^2 + y_t^2 <= R^2. In other words, r = true exactly when the robot never leaves some circle in the plane.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_1 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∃ r : Bool, is_robot_bounded instructions = ok r ∧
      (r = true ↔ BoundedTrajectory instructions.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∃ r : Bool, is_robot_bounded instructions = ok r ∧
      (r = true ↔ BoundedTrajectory instructions.val)) := by
  sorry

/-- Let (X,Y) be the position after executing instructions once from (0,0) facing north, and let F be the facing after that one pass. Whenever the function returns a result r, r = true if and only if (X = 0 and Y = 0) or F is not north.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_2 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ r : Bool, is_robot_bounded instructions = ok r →
      (r = true ↔
        (endX instructions.val = 0 ∧ endY instructions.val = 0) ∨
          endDir instructions.val ≠ 0) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ r : Bool, is_robot_bounded instructions = ok r →
      (r = true ↔
        (endX instructions.val = 0 ∧ endY instructions.val = 0) ∨
          endDir instructions.val ≠ 0)) := by
  sorry

/-- For every instructions satisfying the preconditions, the function returns a result (it does not fail, panic, or overflow).
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_3 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∃ r : Bool, is_robot_bounded instructions = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∃ r : Bool, is_robot_bounded instructions = ok r) := by
  sorry

/-- If instructions[i] is not 'G' for every i with 0 <= i < len(instructions) (that is, the input contains only 'L' and 'R'), then whenever the function returns a result r, r = true.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_4 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hnoG : ∀ (i : Nat) (hi : i < instructions.val.length),
      (instructions.val.get ⟨i, hi⟩).val ≠ 71) :
    ∀ r : Bool, is_robot_bounded instructions = ok r → r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hnoG : ∀ (i : Nat) (hi : i < instructions.val.length),
      (instructions.val.get ⟨i, hi⟩).val ≠ 71), ∀ r : Bool, is_robot_bounded instructions = ok r → r = true) := by
  sorry

/-- If instructions[i] = 'G' for every i with 0 <= i < len(instructions), then whenever the function returns a result r, r = false.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_5 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hallG : ∀ (i : Nat) (hi : i < instructions.val.length),
      (instructions.val.get ⟨i, hi⟩).val = 71) :
    ∀ r : Bool, is_robot_bounded instructions = ok r → r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hallG : ∀ (i : Nat) (hi : i < instructions.val.length),
      (instructions.val.get ⟨i, hi⟩).val = 71), ∀ r : Bool, is_robot_bounded instructions = ok r → r = false) := by
  sorry

/-- For every integer k with 0 <= k < len(instructions), let rot be the slice of length len(instructions) defined by rot[i] = instructions[(i+k) mod len(instructions)] for 0 <= i < len(instructions). Whenever the function returns r on instructions and r' on rot, we have r = r'.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_6 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ (k : Nat) (hk : k < instructions.val.length) (s' : Slice Std.U8),
      s'.val = rotate instructions.val k →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ (k : Nat) (hk : k < instructions.val.length) (s' : Slice Std.U8),
      s'.val = rotate instructions.val k →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r') := by
  sorry

/-- For every pair of byte slices u and v with instructions = u ++ v, and for c equal to the two-byte slice 'LR' or the two-byte slice 'RL', if u ++ c ++ v also has length at most 100 (and therefore satisfies the same instruction constraints), then whenever the function returns r on u ++ v and r' on u ++ c ++ v, we have r = r'.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_7 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ (u v c : List Std.U8) (s' : Slice Std.U8),
      instructions.val = u ++ v →
      (c = [76#u8, 82#u8] ∨ c = [82#u8, 76#u8]) →
      (u ++ c ++ v).length ≤ 100 →
      s'.val = u ++ c ++ v →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ (u v c : List Std.U8) (s' : Slice Std.U8),
      instructions.val = u ++ v →
      (c = [76#u8, 82#u8] ∨ c = [82#u8, 76#u8]) →
      (u ++ c ++ v).length ≤ 100 →
      s'.val = u ++ c ++ v →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r') := by
  sorry

/-- For every byte slice s containing only 'L' and 'R' such that the number of 'L' bytes in s minus the number of 'R' bytes in s is divisible by 4, and such that len(instructions) + len(s) <= 100, whenever the function returns r on instructions and r' on instructions ++ s, we have r = r'.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_8 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ (s : List Std.U8) (s' : Slice Std.U8),
      (∀ b ∈ s, b.val = 76 ∨ b.val = 82) →
      (4 : Int) ∣ turnBalance s →
      instructions.val.length + s.length ≤ 100 →
      s'.val = instructions.val ++ s →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ (s : List Std.U8) (s' : Slice Std.U8),
      (∀ b ∈ s, b.val = 76 ∨ b.val = 82) →
      (4 : Int) ∣ turnBalance s →
      instructions.val.length + s.length ≤ 100 →
      s'.val = instructions.val ++ s →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r with r = true, the set of positions { (x_t, y_t) : t >= 0 } reached in the infinite execution (where at time t >= 0 the robot executes instructions[t mod len(instructions)] from the initial state (0,0) facing north) is finite.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_9 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      (posSet instructions.val).Finite := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      (posSet instructions.val).Finite) := by
  sorry

/-- Let (X,Y) be the position and F the facing after executing instructions once from (0,0) facing north. If F is north and (X,Y) is not (0,0), then whenever the function returns a result r, r = false, and for every integer k >= 0 the position after exactly k*len(instructions) executed instructions is (k*X, k*Y) with facing north; hence for every real R there exists k with k*sqrt(X^2 + Y^2) > R.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_10 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    endDir instructions.val = 0 →
      (endX instructions.val, endY instructions.val) ≠ (0, 0) →
        (∀ r : Bool, is_robot_bounded instructions = ok r → r = false) ∧
          (∀ k : Nat,
              stateAt instructions.val (k * instructions.val.length) =
                ⟨k * endX instructions.val, k * endY instructions.val, 0⟩) ∧
            (∀ R : ℝ, ∃ k : Nat,
              R < (k : ℝ) *
                Real.sqrt (sqDistR (endX instructions.val, endY instructions.val))) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), endDir instructions.val = 0 →
      (endX instructions.val, endY instructions.val) ≠ (0, 0) →
        (∀ r : Bool, is_robot_bounded instructions = ok r → r = false) ∧
          (∀ k : Nat,
              stateAt instructions.val (k * instructions.val.length) =
                ⟨k * endX instructions.val, k * endY instructions.val, 0⟩) ∧
            (∀ R : ℝ, ∃ k : Nat,
              R < (k : ℝ) *
                Real.sqrt (sqDistR (endX instructions.val, endY instructions.val)))) := by
  sorry

/-- Whenever the function returns a result r with r = true, every position (x_t, y_t) reached in the infinite execution satisfies x_t^2 + y_t^2 <= (4*len(instructions))^2.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_11 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      ∀ t : Nat,
        sqDistR (posAt instructions.val t) ≤
          ((4 * instructions.val.length : Nat) : ℝ) ^ 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      ∀ t : Nat,
        sqDistR (posAt instructions.val t) ≤
          ((4 * instructions.val.length : Nat) : ℝ) ^ 2) := by
  sorry

/-- Let L be the number of indices i with instructions[i] = 'L', and let R be the number of indices i with instructions[i] = 'R'. Whenever the function returns a result r, r = true if and only if (L - R) is not divisible by 4.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. Also, exactly one index i has instructions[i] = 'G'. -/
theorem spec_12 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hexactly : ∃ (i : Nat) (hi : i < instructions.val.length),
        (instructions.val.get ⟨i, hi⟩).val = 71 ∧
          ∀ (j : Nat) (hj : j < instructions.val.length),
            (instructions.val.get ⟨j, hj⟩).val = 71 → j = i) :
    ∀ r : Bool, is_robot_bounded instructions = ok r →
      (r = true ↔ ¬ (4 : Int) ∣ turnBalance instructions.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩))
    (hexactly : ∃ (i : Nat) (hi : i < instructions.val.length),
        (instructions.val.get ⟨i, hi⟩).val = 71 ∧
          ∀ (j : Nat) (hj : j < instructions.val.length),
            (instructions.val.get ⟨j, hj⟩).val = 71 → j = i), ∀ r : Bool, is_robot_bounded instructions = ok r →
      (r = true ↔ ¬ (4 : Int) ∣ turnBalance instructions.val)) := by
  sorry

/-- Let swap(instructions) be the slice obtained by replacing every 'L' with 'R', every 'R' with 'L', and leaving every 'G' unchanged. Whenever the function returns r on instructions and r' on swap(instructions), we have r = r'.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_13 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ (s' : Slice Std.U8), s'.val = swapLR instructions.val →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ (s' : Slice Std.U8), s'.val = swapLR instructions.val →
      ∀ (r r' : Bool), is_robot_bounded instructions = ok r →
        is_robot_bounded s' = ok r' → r = r') := by
  sorry

/-- The function returns a result r (it does not fail), and r = true if and only if after exactly 4*len(instructions) executed instructions the robot is again at (0,0) facing north.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_14 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∃ r : Bool, is_robot_bounded instructions = ok r ∧
      (r = true ↔
        stateAt instructions.val (4 * instructions.val.length) = RoboState.origin) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∃ r : Bool, is_robot_bounded instructions = ok r ∧
      (r = true ↔
        stateAt instructions.val (4 * instructions.val.length) = RoboState.origin)) := by
  sorry

/-- Whenever the function returns a result r with r = true, the set { (x_t, y_t) : t >= 0 } of positions at instruction boundaries has at most 4*len(instructions) distinct elements.
  Preconditions: instructions is a slice of bytes with 1 <= len(instructions) <= 100, and for every i with 0 <= i < len(instructions), instructions[i] is the ASCII code of 'G', 'L', or 'R'. -/
theorem spec_15 (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)) :
    ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      (posSet instructions.val).ncard ≤ 4 * instructions.val.length := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (instructions : Slice Std.U8)
    (hlen1 : 1 ≤ instructions.val.length)
    (hlen2 : instructions.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < instructions.val.length),
      IsInstrByte (instructions.val.get ⟨i, hi⟩)), ∀ r : Bool, is_robot_bounded instructions = ok r → r = true →
      (posSet instructions.val).ncard ≤ 4 * instructions.val.length) := by
  sorry

end AegisSpec.IsRobotBounded
