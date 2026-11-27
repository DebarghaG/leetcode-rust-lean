import Aegis.MinSideJumps.Code.Funs

/-!
# Specifications of `Aegis.MinSideJumps.min_side_jumps`

LeetCode problem `minimum-sideway-jumps`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSideJumps

  def vals (obstacles : Slice Std.I64) : List Int :=
    obstacles.val.map (fun x => x.val)

  def entry (obstacles : Slice Std.I64) (i : Nat) : Option Int :=
    (vals obstacles)[i]?

  def IsLane (l : Nat) : Prop :=
    l = 1 ∨ l = 2 ∨ l = 3

  def StepOK (q r : Nat × Nat) : Prop :=
    (r.1 = q.1 + 1 ∧ r.2 = q.2) ∨ (r.1 = q.1 ∧ r.2 ≠ q.2)

  def ChainOK : List (Nat × Nat) → Prop
    | [] => True
    | [_] => True
    | q :: r :: rest => StepOK q r ∧ ChainOK (r :: rest)

  def numJumps : List (Nat × Nat) → Nat
    | [] => 0
    | [_] => 0
    | q :: r :: rest =>
      (if q.1 = r.1 ∧ q.2 ≠ r.2 then 1 else 0) + numJumps (r :: rest)

  def IsRoute (obs : List Int) (n : Nat) (s : List (Nat × Nat)) : Prop :=
    s ≠ [] ∧
    s.head? = some (0, 2) ∧
    (∃ l, s.getLast? = some (n, l)) ∧
    (∀ q ∈ s, IsLane q.2 ∧ q.1 ≤ n ∧ obs[q.1]? ≠ some (q.2 : Int)) ∧
    (∀ q ∈ s.dropLast, q.1 < n) ∧
    ChainOK s

  def IsMinJumps (obs : List Int) (n : Nat) (r : Int) : Prop :=
    (∃ s, IsRoute obs n s ∧ (numJumps s : Int) = r) ∧
    (∀ s, IsRoute obs n s → r ≤ (numJumps s : Int))

  def swapLanes (obs : List Int) : List Int :=
    obs.map (fun v => if v = 1 then 3 else if v = 3 then 1 else v)

  def RemovalOf (obs obs' : List Int) (n : Nat) : Prop :=
    obs'.length = obs.length ∧
    ∀ i, i ≤ n →
      obs'[i]? = obs[i]? ∨ (1 ≤ i ∧ i ≤ n - 1 ∧ obs'[i]? = some 0)

  def nonzeroInterior (obs : List Int) (n : Nat) : List Nat :=
    (List.range (n + 1)).filter
      (fun i => decide (1 ≤ i ∧ i ≤ n - 1 ∧ obs[i]? ≠ some 0))

  /-- Whenever the function returns a result r, r is the minimum number of side jumps over all valid routes from (point 0, lane 2) to any lane at point n. A valid route is a finite sequence of pairs (p_0,l_0),...,(p_m,l_m) such that p_0=0, l_0=2, p_m=n, for every t with 0 <= t <= m we have 0 <= p_t <= n, l_t in {1,2,3}, and obstacles[p_t] != l_t, for every t < m we have p_t < n, and for every t < m either (i) p_{t+1}=p_t+1 and l_{t+1}=l_t, or (ii) p_{t+1}=p_t and l_{t+1} != l_t. The number of side jumps of the route is the number of t < m for which case (ii) holds. The minimum is taken over all such routes; the preconditions guarantee that at least one route exists.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_1 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      IsMinJumps (vals obstacles) n r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), IsMinJumps (vals obstacles) n r.val) := by
    sorry

  /-- The function returns a result r (it does not panic, access an out-of-bounds index, or overflow 64-bit arithmetic) for every obstacles satisfying the preconditions.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_2 (obstacles : Slice Std.I64) (n : Nat)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3) :
      ∃ r, Aegis.MinSideJumps.min_side_jumps obstacles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3), ∃ r, Aegis.MinSideJumps.min_side_jumps obstacles = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n - 1, where n = len(obstacles) - 1.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_3 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      0 ≤ r.val ∧ r.val ≤ (n : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if obstacles[i] != 2 for every i with 1 <= i <= n. Equivalently, no side jumps are needed exactly when lane 2 is free at every point from 1 through n.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_4 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      r.val = 0 ↔ ∀ i, 1 ≤ i → i ≤ n → entry obstacles i ≠ some 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), r.val = 0 ↔ ∀ i, 1 ≤ i → i ≤ n → entry obstacles i ≠ some 2) := by
    sorry

  /-- Whenever the function returns a result r, if the number of indices i with 1 <= i <= n-1 and obstacles[i] != 0 is at most 2, then r = 1 if at least one of those indices has obstacles[i] = 2, and r = 0 otherwise.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_5 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hcount : (nonzeroInterior (vals obstacles) n).length ≤ 2)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      ((∃ i, 1 ≤ i ∧ i ≤ n - 1 ∧ entry obstacles i = some 2) → r.val = 1) ∧
      ((∀ i, 1 ≤ i → i ≤ n - 1 → entry obstacles i ≠ some 2) → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hcount : (nonzeroInterior (vals obstacles) n).length ≤ 2)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), ((∃ i, 1 ≤ i ∧ i ≤ n - 1 ∧ entry obstacles i = some 2) → r.val = 1) ∧
        ((∀ i, 1 ≤ i → i ≤ n - 1 → entry obstacles i ≠ some 2) → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, suppose there is an index i0 with 1 <= i0 <= n-1 such that obstacles[i0] = 2 and obstacles[i] != 2 for every i with 1 <= i < i0 (so i0 is the first point where lane 2 is blocked). Then r = 1 if and only if there exists a lane l in {1,3} such that obstacles[i] != l for every i with i0-1 <= i <= n.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_6 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      (∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
          (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2)) →
        (r.val = 1 ↔
          ∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
            (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2) ∧
            ∃ l : Int, (l = 1 ∨ l = 3) ∧
              ∀ i, i0 - 1 ≤ i → i ≤ n → entry obstacles i ≠ some l) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), (∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
            (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2)) →
          (r.val = 1 ↔
            ∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
              (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2) ∧
              ∃ l : Int, (l = 1 ∨ l = 3) ∧
                ∀ i, i0 - 1 ≤ i → i ≤ n → entry obstacles i ≠ some l)) := by
    sorry

  /-- Whenever the function returns a result r, if r >= 2, then there exists an index i0 with 1 <= i0 <= n-1 such that obstacles[i0] = 2 and obstacles[i] != 2 for every i with 1 <= i < i0 (the first lane-2 obstacle), and for each l in {1,3} there exists an index i with i0-1 <= i <= n such that obstacles[i] = l.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_7 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      2 ≤ r.val →
        ∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
          (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2) ∧
          ∀ l : Int, (l = 1 ∨ l = 3) →
            ∃ i, i0 - 1 ≤ i ∧ i ≤ n ∧ entry obstacles i = some l := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), 2 ≤ r.val →
          ∃ i0, 1 ≤ i0 ∧ i0 ≤ n - 1 ∧ entry obstacles i0 = some 2 ∧
            (∀ i, 1 ≤ i → i < i0 → entry obstacles i ≠ some 2) ∧
            ∀ l : Int, (l = 1 ∨ l = 3) →
              ∃ i, i0 - 1 ≤ i ∧ i ≤ n ∧ entry obstacles i = some l) := by
    sorry

  /-- Whenever the function returns a result r for obstacles, r is unchanged if every occurrence of lane 1 in obstacles is replaced by lane 3 and every occurrence of lane 3 in obstacles is replaced by lane 1. More formally, for the array obstacles' defined by obstacles'[i] = 3 when obstacles[i] = 1, obstacles'[i] = 1 when obstacles[i] = 3, and obstacles'[i] = obstacles[i] otherwise, the minimum number of side jumps for obstacles' is also r.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_8 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      IsMinJumps (swapLanes (vals obstacles)) n r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), IsMinJumps (swapLanes (vals obstacles)) n r.val) := by
    sorry

  /-- Whenever the function returns a result r for obstacles, if obstacles' is any array satisfying the same preconditions and obtained from obstacles by replacing some entries among indices 1..n-1 with 0 (removing obstacles), then the minimum number of side jumps for obstacles' is at most r.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_9 (obstacles obstacles' : Slice Std.I64) (n : Nat) (r r' : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hlen' : obstacles'.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hfirst' : entry obstacles' 0 = some 0)
      (hlast' : entry obstacles' n = some 0)
      (hbound' : ∀ i, i ≤ n → ∃ v : Int, entry obstacles' i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hrem : RemovalOf (vals obstacles) (vals obstacles') n)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r)
      (hres' : Aegis.MinSideJumps.min_side_jumps obstacles' = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (obstacles obstacles' : Slice Std.I64) (n : Nat) (r r' : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hlen' : obstacles'.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hfirst' : entry obstacles' 0 = some 0)
        (hlast' : entry obstacles' n = some 0)
        (hbound' : ∀ i, i ≤ n → ∃ v : Int, entry obstacles' i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hrem : RemovalOf (vals obstacles) (vals obstacles') n)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r)
        (hres' : Aegis.MinSideJumps.min_side_jumps obstacles' = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a route from (point 0, lane 2) to some lane at point n, using only forward moves on the same lane and same-point side jumps to any other lane, never standing on a blocked lane, whose number of side jumps is exactly r.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_10 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      ∃ s : List (Nat × Nat), IsRoute (vals obstacles) n s ∧ (numJumps s : Int) = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), ∃ s : List (Nat × Nat), IsRoute (vals obstacles) n s ∧ (numJumps s : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, every route from (point 0, lane 2) to any lane at point n, using only forward moves on the same lane and same-point side jumps to any other lane, never standing on a blocked lane, has at least r side jumps.
    Preconditions: Let n = len(obstacles) - 1. 1 <= n <= 5 * 10^5, obstacles[0] = 0, obstacles[n] = 0, and for every i with 0 <= i <= n, 0 <= obstacles[i] <= 3. -/
  theorem spec_11 (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hlen : obstacles.val.length = n + 1)
      (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
      (hfirst : entry obstacles 0 = some 0)
      (hlast : entry obstacles n = some 0)
      (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
      (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r) :
      ∀ s : List (Nat × Nat), IsRoute (vals obstacles) n s → r.val ≤ (numJumps s : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (obstacles : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hlen : obstacles.val.length = n + 1)
        (hn1 : 1 ≤ n) (hn5 : n ≤ 500000)
        (hfirst : entry obstacles 0 = some 0)
        (hlast : entry obstacles n = some 0)
        (hbound : ∀ i, i ≤ n → ∃ v : Int, entry obstacles i = some v ∧ 0 ≤ v ∧ v ≤ 3)
        (hres : Aegis.MinSideJumps.min_side_jumps obstacles = ok r), ∀ s : List (Nat × Nat), IsRoute (vals obstacles) n s → r.val ≤ (numJumps s : Int)) := by
    sorry

  end AegisSpec.MinSideJumps
