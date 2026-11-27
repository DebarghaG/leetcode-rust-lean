import Aegis.LongestObstacleCourseAtEachPosition.Code.Funs

/-!
# Specifications of `Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position`

LeetCode problem `find-the-longest-valid-obstacle-course-at-each-position`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestObstacleCourseAtEachPosition

  def valAt (l : List Std.I64) (i : Nat) : Int :=
    ((l[i]?).map (fun x => x.val)).getD 0

  def obstacleVals (obstacles : Slice Std.I64) : List Int :=
    obstacles.val.map (fun x => x.val)

  def answerVals (r : alloc.vec.Vec Std.I64) : List Int :=
    r.val.map (fun x => x.val)

  def maxOf (l : List Int) : Int :=
    l.max?.getD 0

  def ChainEndingAt (a : List Int) : Nat → Nat → Prop
    | 0, _ => False
    | 1, i => i < a.length
    | L + 2, i =>
        ∃ j, j < i ∧ a.getD j 0 ≤ a.getD i 0 ∧ ChainEndingAt a (L + 1) j

  def IsLongestChainAt (a : List Int) (i L : Nat) : Prop :=
    ChainEndingAt a L i ∧ ∀ M : Nat, ChainEndingAt a M i → M ≤ L

  def maxPredecessors (a rv : List Int) (i : Nat) : Int :=
    maxOf <|
      (List.range i).filterMap (fun j =>
        if a.getD j 0 ≤ a.getD i 0 then some (rv.getD j 0) else none)

  def maxPreviousAnswers (rv : List Int) (i : Nat) : Int :=
    maxOf <| (List.range i).map (fun j => rv.getD j 0)

  def countLeqThrough (a : List Int) (i : Nat) : Nat :=
    ((List.range (i + 1)).filter (fun j => decide (a.getD j 0 ≤ a.getD i 0))).length

  /-- Whenever the function returns a result r, len(r) = n, and for every i with 0 <= i < n, r[i] is the maximum integer L for which there exist indices j_0 < j_1 < ... < j_{L-1} = i such that 0 <= j_0 and obstacles[j_0] <= obstacles[j_1] <= ... <= obstacles[j_{L-1}]. This maximum is the length of the longest nondecreasing obstacle course using only indices at most i and ending at index i.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_1 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      r.val.length = obstacles.val.length ∧
        ∀ i, i < obstacles.val.length →
          ∃ L : Nat,
            valAt r.val i = (L : Int) ∧
              IsLongestChainAt (obstacleVals obstacles) i L := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), r.val.length = obstacles.val.length ∧
          ∀ i, i < obstacles.val.length →
            ∃ L : Nat,
              valAt r.val i = (L : Int) ∧
                IsLongestChainAt (obstacleVals obstacles) i L) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail, panic, go out of bounds, or overflow during execution.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_2 (obstacles : Slice Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (obstacles : Slice Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
            obstacles = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 1 + max({ r[j] | 0 <= j < i and obstacles[j] <= obstacles[i] }), where the maximum of the empty set is defined to be 0.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_3 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        valAt r.val i =
          1 + maxPredecessors (obstacleVals obstacles) (answerVals r) i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          valAt r.val i =
            1 + maxPredecessors (obstacleVals obstacles) (answerVals r) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n, if obstacles[i-1] = obstacles[i], then r[i] = r[i-1] + 1.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_4 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, 1 ≤ i → i < obstacles.val.length →
        valAt obstacles.val (i - 1) = valAt obstacles.val i →
          valAt r.val i = valAt r.val (i - 1) + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, 1 ≤ i → i < obstacles.val.length →
          valAt obstacles.val (i - 1) = valAt obstacles.val i →
            valAt r.val i = valAt r.val (i - 1) + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < n, if obstacles[i] < obstacles[i-1], then r[i] <= r[i-1].
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_5 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, 1 ≤ i → i < obstacles.val.length →
        valAt obstacles.val i < valAt obstacles.val (i - 1) →
          valAt r.val i ≤ valAt r.val (i - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, 1 ≤ i → i < obstacles.val.length →
          valAt obstacles.val i < valAt obstacles.val (i - 1) →
            valAt r.val i ≤ valAt r.val (i - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if obstacles[0] <= obstacles[1] <= ... <= obstacles[i], then r[i] = i + 1.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_6 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        (∀ k, k < i → valAt obstacles.val k ≤ valAt obstacles.val (k + 1)) →
          valAt r.val i = (i : Int) + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          (∀ k, k < i → valAt obstacles.val k ≤ valAt obstacles.val (k + 1)) →
            valAt r.val i = (i : Int) + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 1 if and only if for every j with 0 <= j < i, obstacles[j] > obstacles[i].
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_7 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        (valAt r.val i = 1 ↔
          ∀ j, j < i → valAt obstacles.val j > valAt obstacles.val i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          (valAt r.val i = 1 ↔
            ∀ j, j < i → valAt obstacles.val j > valAt obstacles.val i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] > 1, then there exists an index j such that 0 <= j < i, obstacles[j] <= obstacles[i], and r[i] = r[j] + 1.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_8 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        valAt r.val i > 1 →
          ∃ j, j < i ∧ valAt obstacles.val j ≤ valAt obstacles.val i ∧
            valAt r.val i = valAt r.val j + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          valAt r.val i > 1 →
            ∃ j, j < i ∧ valAt obstacles.val j ≤ valAt obstacles.val i ∧
              valAt r.val i = valAt r.val j + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < n, if obstacles[i] <= obstacles[j], then r[j] >= r[i] + 1.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_9 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i j, i < j → j < obstacles.val.length →
        valAt obstacles.val i ≤ valAt obstacles.val j →
          valAt r.val j ≥ valAt r.val i + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i j, i < j → j < obstacles.val.length →
          valAt obstacles.val i ≤ valAt obstacles.val j →
            valAt r.val j ≥ valAt r.val i + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if obstacles[j] <= obstacles[i] for every j with 0 <= j < i, then r[i] = 1 + max({ r[j] | 0 <= j < i }), where the maximum of the empty set is defined to be 0.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_10 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        (∀ j, j < i → valAt obstacles.val j ≤ valAt obstacles.val i) →
          valAt r.val i = 1 + maxPreviousAnswers (answerVals r) i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          (∀ j, j < i → valAt obstacles.val j ≤ valAt obstacles.val i) →
            valAt r.val i = 1 + maxPreviousAnswers (answerVals r) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= card({ j | 0 <= j <= i and obstacles[j] <= obstacles[i] }), where card denotes the number of indices in the set.
    Preconditions: Let n = len(obstacles). 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= obstacles[k] <= 10^7. -/
  theorem spec_11 (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hn1 : 1 ≤ obstacles.val.length)
      (hn2 : obstacles.val.length ≤ 100000)
      (hobs : ∀ k, k < obstacles.val.length →
        1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
      (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
        obstacles = ok r) :
      ∀ i, i < obstacles.val.length →
        valAt r.val i ≤ (countLeqThrough (obstacleVals obstacles) i : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hn1 : 1 ≤ obstacles.val.length)
        (hn2 : obstacles.val.length ≤ 100000)
        (hobs : ∀ k, k < obstacles.val.length →
          1 ≤ valAt obstacles.val k ∧ valAt obstacles.val k ≤ 10000000)
        (hres : Aegis.LongestObstacleCourseAtEachPosition.longest_obstacle_course_at_each_position
          obstacles = ok r), ∀ i, i < obstacles.val.length →
          valAt r.val i ≤ (countLeqThrough (obstacleVals obstacles) i : Int)) := by
    sorry

  end AegisSpec.LongestObstacleCourseAtEachPosition
