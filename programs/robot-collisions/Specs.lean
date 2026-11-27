import Aegis.SurvivedRobotsHealths.Code.Funs

/-!
# Specifications of `Aegis.SurvivedRobotsHealths.survived_robots_healths`

LeetCode problem `robot-collisions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SurvivedRobotsHealths

open Aegis.SurvivedRobotsHealths (survived_robots_healths)

structure Robot where

  idx : Nat

  pos : Int

  health : Int

  dir : Nat
  deriving Repr, DecidableEq

def meetDist (a b : Robot) : Option Nat :=
  if a.dir = 82 ∧ b.dir = 76 ∧ a.pos < b.pos then some (b.pos - a.pos).toNat else none

def listMin : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => min a b) x)

def meetDists (alive : List Robot) : List Nat :=
  alive.flatMap (fun a => alive.filterMap (fun b => meetDist a b))

def minMeetDist (alive : List Robot) : Option Nat := listMin (meetDists alive)

def findOpponent (d : Nat) (alive : List Robot) (r : Robot) : Option Robot :=
  alive.find? (fun s => meetDist r s == some d || meetDist s r == some d)

def resolveStep (alive : List Robot) : List Robot :=
  match minMeetDist alive with
  | none => alive
  | some d =>
    alive.filterMap (fun r =>
      match findOpponent d alive r with
      | none => some r
      | some s =>
        if r.health > s.health then some { r with health := r.health - 1 } else none)

def runProcess : Nat → List Robot → List Robot
  | 0, alive => alive
  | fuel + 1, alive =>
    if (minMeetDist alive).isSome then runProcess fuel (resolveStep alive) else alive

def toIntList (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def toNatList (s : Slice Std.U8) : List Nat := s.val.map (fun x => x.val)

def vectorInts (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def initRobots (P H : List Int) (D : List Nat) : List Robot :=
  (P.zip H).zip D |>.mapIdx (fun i t => ⟨i, t.1.1, t.1.2, t.2⟩)

def initialState (P H : List Int) (D : List Nat) : List Robot := initRobots P H D

def finalRobots (P H : List Int) (D : List Nat) : List Robot :=
  runProcess P.length (initialState P H D)

def survivorRobots (positions healths : Slice Std.I64) (directions : Slice Std.U8) :
    List Robot :=
  finalRobots (toIntList positions) (toIntList healths) (toNatList directions)

def survivorSet (positions healths : Slice Std.I64) (directions : Slice Std.U8) :
    Finset Nat :=
  (survivorRobots positions healths directions).map Robot.idx |>.toFinset

def survivorRank (positions healths : Slice Std.I64) (directions : Slice Std.U8)
    (i : Nat) : Nat :=
  ((survivorSet positions healths directions).filter (fun j => j < i)).card

def survivorHealth (positions healths : Slice Std.I64) (directions : Slice Std.U8)
    (i : Nat) : Option Int :=
  ((survivorRobots positions healths directions).find? (fun r => r.idx == i)).map
    Robot.health

def survivorHealths (positions healths : Slice Std.I64) (directions : Slice Std.U8) :
    List Int :=
  (survivorRobots positions healths directions).map Robot.health

/-- Consider the collision process in which robot i initially has position positions[i] and health healths[i] and moves at unit speed right if directions[i] is 82 ('R') and left if it is 76 ('L'). At each earliest future time at which two currently alive robots meet, if their current healths differ then the robot with smaller current health is removed and the other current health is decreased by one; if their current healths are equal both are removed. A surviving robot continues in its original direction. Meetings at the same time involving disjoint pairs are resolved independently; process them in any order. Repeat until no two alive robots would ever meet. Let S be the set of robots still alive after this process and let f(i) be the current health of i in S. Then the function returns a vector r such that len(r) = |S| and, writing the elements of S in increasing original-index order as i_0 < i_1 < ... < i_{|S|-1}, for every j with 0 <= j < |S| we have r[j] = f(i_j).
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_1
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∃ r, survived_robots_healths positions healths directions = ok r ∧
      (vectorInts r).length = (survivorSet positions healths directions).card ∧
      (∀ i (hi : i ∈ survivorSet positions healths directions),
        ∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
          survivorHealth positions healths directions i = some h) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∃ r, survived_robots_healths positions healths directions = ok r ∧
      (vectorInts r).length = (survivorSet positions healths directions).card ∧
      (∀ i (hi : i ∈ survivorSet positions healths directions),
        ∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
          survivorHealth positions healths directions i = some h)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail.
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_2
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∃ r, survived_robots_healths positions healths directions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∃ r, survived_robots_healths positions healths directions = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= n.
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_3
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∀ r, survived_robots_healths positions healths directions = ok r →
      (vectorInts r).length ≤ n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∀ r, survived_robots_healths positions healths directions = ok r →
      (vectorInts r).length ≤ n) := by
  sorry

/-- Whenever the function returns a result r, let S be the set of robots still alive after the collision process. For every i in S, if i is the k-th smallest index in S with 0-based counting, then 1 <= r[k] <= healths[i].
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_4
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), i ∈ survivorSet positions healths directions →
        ∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
          1 ≤ h ∧ h ≤ (healths.val[i]'(by omega)).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), i ∈ survivorSet positions healths directions →
        ∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
          1 ≤ h ∧ h ≤ (healths.val[i]'(by omega)).val) := by
  sorry

/-- The function returns r with len(r) = n and r[i] = healths[i] for every i with 0 <= i < n.
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'), and there do not exist indices i,j with 0 <= i,j < n such that directions[i] = 82 ('R'), directions[j] = 76 ('L'), and positions[i] < positions[j]. -/
theorem spec_5
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82)
    (hno_approach : ∀ i (hi : i < n) (j : Nat) (hj : j < n),
      (directions.val[i]'(by omega)).val = 82 → (directions.val[j]'(by omega)).val = 76 →
        ¬ ((positions.val[i]'(by omega)).val < (positions.val[j]'(by omega)).val)) :
    ∃ r, survived_robots_healths positions healths directions = ok r ∧
      (vectorInts r).length = n ∧
      (∀ i (hi : i < n),
        (vectorInts r)[i]? = some ((healths.val[i]'(by omega)).val)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82)
    (hno_approach : ∀ i (hi : i < n) (j : Nat) (hj : j < n),
      (directions.val[i]'(by omega)).val = 82 → (directions.val[j]'(by omega)).val = 76 →
        ¬ ((positions.val[i]'(by omega)).val < (positions.val[j]'(by omega)).val)), ∃ r, survived_robots_healths positions healths directions = ok r ∧
      (vectorInts r).length = n ∧
      (∀ i (hi : i < n),
        (vectorInts r)[i]? = some ((healths.val[i]'(by omega)).val))) := by
  sorry

/-- Whenever the function returns a result r, let S be the final survivor set. For every i with directions[i] = 76 ('L') such that there is no j with directions[j] = 82 ('R') and positions[j] < positions[i], robot i is in S and, if i is the k-th smallest index in S, r[k] = healths[i].
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_6
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), (directions.val[i]'(by omega)).val = 76 →
        (∀ j (hj : j < n), (directions.val[j]'(by omega)).val = 82 →
          ¬ ((positions.val[j]'(by omega)).val < (positions.val[i]'(by omega)).val)) →
        i ∈ survivorSet positions healths directions ∧
          (∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
            h = (healths.val[i]'(by omega)).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), (directions.val[i]'(by omega)).val = 76 →
        (∀ j (hj : j < n), (directions.val[j]'(by omega)).val = 82 →
          ¬ ((positions.val[j]'(by omega)).val < (positions.val[i]'(by omega)).val)) →
        i ∈ survivorSet positions healths directions ∧
          (∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
            h = (healths.val[i]'(by omega)).val)) := by
  sorry

/-- Whenever the function returns a result r, let S be the final survivor set. For every i with directions[i] = 82 ('R') such that there is no j with directions[j] = 76 ('L') and positions[j] > positions[i], robot i is in S and, if i is the k-th smallest index in S, r[k] = healths[i].
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, and each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'). -/
theorem spec_7
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82) :
    ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), (directions.val[i]'(by omega)).val = 82 →
        (∀ j (hj : j < n), (directions.val[j]'(by omega)).val = 76 →
          ¬ ((positions.val[i]'(by omega)).val < (positions.val[j]'(by omega)).val)) →
        i ∈ survivorSet positions healths directions ∧
          (∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
            h = (healths.val[i]'(by omega)).val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82), ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ i (hi : i < n), (directions.val[i]'(by omega)).val = 82 →
        (∀ j (hj : j < n), (directions.val[j]'(by omega)).val = 76 →
          ¬ ((positions.val[i]'(by omega)).val < (positions.val[j]'(by omega)).val)) →
        i ∈ survivorSet positions healths directions ∧
          (∃ h, (vectorInts r)[survivorRank positions healths directions i]? = some h ∧
            h = (healths.val[i]'(by omega)).val)) := by
  sorry

/-- Whenever the function returns a result r, r[j] = H for every j with 0 <= j < len(r).
  Preconditions: Let n = len(positions) = len(healths) = len(directions). We have 1 <= n <= 100000, positions[0],...,positions[n-1] are pairwise distinct, 1 <= positions[i] <= 1000000000 and 1 <= healths[i] <= 1000000000 for every i with 0 <= i < n, each directions[i] is either 76 (ASCII 'L') or 82 (ASCII 'R'), and there exists H such that healths[i] = H for every i with 0 <= i < n. -/
theorem spec_8
    (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82)
    (H : Int) (hH : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val = H) :
    ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ j (hj : j < (vectorInts r).length), (vectorInts r)[j]'hj = H := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (positions healths : Slice Std.I64) (directions : Slice Std.U8) (n : Nat)
    (hn_pos : positions.val.length = n)
    (hn_healths : healths.val.length = n)
    (hn_dirs : directions.val.length = n)
    (hn_ge : 1 ≤ n)
    (hn_le : n ≤ 100000)
    (hpos_distinct : ∀ i (hi : i < n) (j : Nat) (hj : j < n), i ≠ j →
      (positions.val[i]'(by omega)).val ≠ (positions.val[j]'(by omega)).val)
    (hpos_ge : ∀ i (hi : i < n), 1 ≤ (positions.val[i]'(by omega)).val)
    (hpos_le : ∀ i (hi : i < n), (positions.val[i]'(by omega)).val ≤ 1000000000)
    (hhealth_ge : ∀ i (hi : i < n), 1 ≤ (healths.val[i]'(by omega)).val)
    (hhealth_le : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val ≤ 1000000000)
    (hdirs : ∀ i (hi : i < n),
      (directions.val[i]'(by omega)).val = 76 ∨ (directions.val[i]'(by omega)).val = 82)
    (H : Int) (hH : ∀ i (hi : i < n), (healths.val[i]'(by omega)).val = H), ∀ r, survived_robots_healths positions healths directions = ok r →
      ∀ j (hj : j < (vectorInts r).length), (vectorInts r)[j]'hj = H) := by
  sorry

end AegisSpec.SurvivedRobotsHealths
