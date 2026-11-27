import Aegis.RobotSim.Code.Funs

/-!
# Specifications of `Aegis.RobotSim.robot_sim`

LeetCode problem `walking-robot-simulation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RobotSim

abbrev Pos : Type := Int × Int

def vecCoords (v : alloc.vec.Vec Std.I64) : List Int :=
  v.val.map (fun c => c.val)

def obstacleCoords (obstacles : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  obstacles.val.map vecCoords

def occurs (obs : List (List Int)) (p : Pos) : Bool :=
  obs.any fun o => decide (o = [p.1, p.2])

def dirVec (dir : Int) : Pos :=
  match dir % 4 with
  | 0 => (0, 1)
  | 1 => (1, 0)
  | 2 => (0, -1)
  | _ => (-1, 0)

structure St where
  x : Int
  y : Int
  dir : Int

def St.init : St := ⟨0, 0, 0⟩

def steps : Nat → List (List Int) → St → St × List Pos
  | 0, _, s => (s, [])
  | n + 1, obs, s =>
      let d := dirVec s.dir
      let p : Pos := (s.x + d.1, s.y + d.2)
      if occurs obs p then (s, [])
      else
        let r := steps n obs { s with x := p.1, y := p.2 }
        (r.1, p :: r.2)

def execCmd (obs : List (List Int)) (c : Int) (s : St) : St × List Pos :=
  if c = -2 then ({ s with dir := (s.dir + 3) % 4 }, [])
  else if c = -1 then ({ s with dir := (s.dir + 1) % 4 }, [])
  else steps c.toNat obs s

def execCmds (obs : List (List Int)) : List Int → St → St × List Pos
  | [], s => (s, [])
  | c :: cs, s =>
      let r := execCmd obs c s
      let r' := execCmds obs cs r.1
      (r'.1, r.2 ++ r'.2)

def visitedFrom (obs : List (List Int)) (cmds : List Int) (s : St) : List Pos :=
  (s.x, s.y) :: (execCmds obs cmds s).2

def cmdEndsFrom (obs : List (List Int)) : List Int → St → List Pos
  | [], _ => []
  | c :: cs, s =>
      let r := execCmd obs c s
      (r.1.x, r.1.y) :: cmdEndsFrom obs cs r.1

def sqNorm (p : Pos) : Int := p.1 * p.1 + p.2 * p.2

def maxSq : List Pos → Int
  | [] => 0
  | p :: ps => max (sqNorm p) (maxSq ps)

def visitedPositions (commands : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) : List Pos :=
  visitedFrom (obstacleCoords obstacles) commands.val St.init

def commandEndPositions (commands : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) : List Pos :=
  (0, 0) :: cmdEndsFrom (obstacleCoords obstacles) commands.val St.init

def simValue (commands : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) : Int :=
  maxSq (visitedPositions commands obstacles)

def forwardSum (commands : Slice Std.I64) : Int :=
  ((commands.val.filter fun c => decide (1 ≤ c.val ∧ c.val ≤ 9)).map fun c => c.val).sum

def CommandsOK (commands : Slice Std.I64) : Prop :=
  ∀ c ∈ commands.val, c.val = -2 ∨ c.val = -1 ∨ (1 ≤ c.val ∧ c.val ≤ 9)

def ObstaclesOK (obstacles : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ o ∈ obstacleCoords obstacles,
    ∃ a b : Int, o = [a, b] ∧ -30000 ≤ a ∧ a ≤ 30000 ∧ -30000 ≤ b ∧ b ≤ 30000

def AnswerBelow2Pow31 (commands : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  simValue commands obstacles < 2 ^ 31

/-- Let O be the set of obstacle coordinates { (obstacles[i][0], obstacles[i][1]) | 0 <= i < len(obstacles) }. The robot state (x,y,dir) starts at (0,0) facing North, where North=(0,1), East=(1,0), South=(0,-1), West=(-1,0). Execute commands in order: command -2 rotates dir 90 degrees left; command -1 rotates dir 90 degrees right; command k with 1 <= k <= 9 attempts k one-unit forward steps. For each such unit step, let (nx,ny) = (x,y) + unit(dir); if (nx,ny) is in O, the robot does not move into it and abandons the remaining steps of that command; otherwise the robot moves to (nx,ny). Record the initial position (0,0) and every position reached after a successful unit step. The function returns a result r equal to the maximum of x^2 + y^2 over all recorded positions (x,y).
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_1 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val = simValue commands obstacles := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val = simValue commands obstacles) := by
  sorry

/-- For every input satisfying these preconditions, the function returns a result r; it does not fail through arithmetic overflow or out-of-bounds access. If S is the sum of all forward command amounts, then S <= 90000 and every position the robot can visit has |x| + |y| <= S, so every squared distance that may be computed is at most S^2 <= 8100000000 < 2^63.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]. The answer < 2^31 guarantee is not needed for this specification. -/
theorem spec_2 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r) := by
  sorry

/-- Let S = sum of commands[i] over all indices i with 1 <= commands[i] <= 9. The function returns a result r and r <= S^2.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_3 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val ≤ forwardSum commands * forwardSum commands := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val ≤ forwardSum commands * forwardSum commands) := by
  sorry

/-- The function returns a result r and r is not congruent to 3 modulo 4.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_4 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r ∧ r.val % 4 ≠ 3 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r ∧ r.val % 4 ≠ 3) := by
  sorry

/-- Using the robot execution described by commands and O = { (obstacles[i][0], obstacles[i][1]) | 0 <= i < len(obstacles) }, the function returns a result r and there exists a position (x,y) visited by the robot during that execution such that r = x^2 + y^2.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_5 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ ∃ p ∈ visitedPositions commands obstacles, r.val = p.1 * p.1 + p.2 * p.2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ ∃ p ∈ visitedPositions commands obstacles, r.val = p.1 * p.1 + p.2 * p.2) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] is either -2 or -1; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_6 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : ∀ c ∈ commands.val, c.val = -2 ∨ c.val = -1)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : ∀ c ∈ commands.val, c.val = -2 ∨ c.val = -1)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r >= commands[0]^2.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) = 1, obstacles[0][0] = 0, obstacles[0][1] = 0; 1 <= commands[0] <= 9; the answer is guaranteed to be < 2^31. -/
theorem spec_7 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs : obstacleCoords obstacles = [[0, 0]])
    (hfirst : ∀ c, commands.val.head? = some c → 1 ≤ c.val ∧ c.val ≤ 9)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ ∀ c, commands.val.head? = some c → c.val * c.val ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs : obstacleCoords obstacles = [[0, 0]])
    (hfirst : ∀ c, commands.val.head? = some c → 1 ≤ c.val ∧ c.val ≤ 9)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ ∀ c, commands.val.head? = some c → c.val * c.val ≤ r.val) := by
  sorry

/-- The call robot_sim(commands, obstacles) returns a result r, the call robot_sim(commands, obstacles') returns a result r', and r = r'.
  Preconditions: For both obstacle lists obstacles and obstacles', len(obstacles) <= 10000 and len(obstacles') <= 10000; every entry of either list has length exactly 2 with coordinates in [-30000, 30000]; commands satisfies len(commands) >= 1, len(commands) <= 10000, and every commands[i] is -2, -1, or an integer k with 1 <= k <= 9. Let S be the sum of commands[i] over all i with 1 <= commands[i] <= 9. For every integer point (x,y) with -S <= x <= S and -S <= y <= S, (x,y) is in the obstacle set of obstacles if and only if it is in the obstacle set of obstacles'. -/
theorem spec_8 (commands : Slice Std.I64) (obstacles obstacles' : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000)
    (hobs_len' : obstacles'.val.length ≤ 10000)
    (hobs : ObstaclesOK obstacles) (hobs' : ObstaclesOK obstacles')
    (hagree : ∀ x y : Int,
      -forwardSum commands ≤ x → x ≤ forwardSum commands →
      -forwardSum commands ≤ y → y ≤ forwardSum commands →
      (occurs (obstacleCoords obstacles) (x, y) ↔ occurs (obstacleCoords obstacles') (x, y))) :
    ∃ r r', Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ Aegis.RobotSim.robot_sim commands obstacles' = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles obstacles' : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000)
    (hobs_len' : obstacles'.val.length ≤ 10000)
    (hobs : ObstaclesOK obstacles) (hobs' : ObstaclesOK obstacles')
    (hagree : ∀ x y : Int,
      -forwardSum commands ≤ x → x ≤ forwardSum commands →
      -forwardSum commands ≤ y → y ≤ forwardSum commands →
      (occurs (obstacleCoords obstacles) (x, y) ↔ occurs (obstacleCoords obstacles') (x, y))), ∃ r r', Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ Aegis.RobotSim.robot_sim commands obstacles' = ok r' ∧ r = r') := by
  sorry

/-- The call robot_sim(commands, obstacles) returns a result r, the call robot_sim(commands', obstacles) returns a result r', and r = r'.
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] has length exactly 2 with coordinates in [-30000, 30000]; commands' is commands concatenated with a finite sequence T of values, each of which is either -1 or -2, and len(commands') <= 10000; the answer is guaranteed to be < 2^31. -/
theorem spec_9 (commands commands' : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) (T : List Std.I64)
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hT : ∀ t ∈ T, t.val = -1 ∨ t.val = -2)
    (hcat : commands'.val = commands.val ++ T)
    (hcmd'_len : commands'.val.length ≤ 10000)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r r', Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ Aegis.RobotSim.robot_sim commands' obstacles = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (commands commands' : Slice Std.I64)
    (obstacles : Slice (alloc.vec.Vec Std.I64)) (T : List Std.I64)
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hT : ∀ t ∈ T, t.val = -1 ∨ t.val = -2)
    (hcat : commands'.val = commands.val ++ T)
    (hcmd'_len : commands'.val.length ≤ 10000)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r r', Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ Aegis.RobotSim.robot_sim commands' obstacles = ok r' ∧ r = r') := by
  sorry

/-- Let O = { (obstacles[i][0], obstacles[i][1]) | 0 <= i < len(obstacles) }. Execute the commands with the unit-step obstacle rule: -2 and -1 turn in place, and a positive command attempts one-unit forward steps but abandons the remaining steps of that command if the next square is in O. Let B be the set containing (0,0) and the robot's position immediately after each complete command. The function returns a result r and r = max_{(x,y) in B} (x^2 + y^2).
  Preconditions: len(commands) >= 1 and len(commands) <= 10000; every commands[i] for 0 <= i < len(commands) is either -2, -1, or an integer k with 1 <= k <= 9; len(obstacles) <= 10000; every obstacles[j] for 0 <= j < len(obstacles) has length exactly 2, and its two entries obstacles[j][0], obstacles[j][1] are integers in [-30000, 30000]; the answer is guaranteed to be < 2^31. -/
theorem spec_10 (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles) :
    ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val = maxSq (commandEndPositions commands obstacles) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (commands : Slice Std.I64) (obstacles : Slice (alloc.vec.Vec Std.I64))
    (hcmd_len : 1 ≤ commands.val.length) (hcmd_len' : commands.val.length ≤ 10000)
    (hcmd : CommandsOK commands)
    (hobs_len : obstacles.val.length ≤ 10000) (hobs : ObstaclesOK obstacles)
    (hans : AnswerBelow2Pow31 commands obstacles), ∃ r, Aegis.RobotSim.robot_sim commands obstacles = ok r
      ∧ r.val = maxSq (commandEndPositions commands obstacles)) := by
  sorry

end AegisSpec.RobotSim
