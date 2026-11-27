import Aegis.MinRefuelStops.Code.Funs

/-!
# Specifications of `Aegis.MinRefuelStops.min_refuel_stops`

LeetCode problem `minimum-number-of-refueling-stops`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinRefuelStops

  open Aegis.MinRefuelStops

  abbrev I64 := Aeneas.Std.I64

  abbrev I64Vec := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  def stationPos (v : I64Vec) : Int :=
    match v.val with
    | x :: _ => x.val
    | [] => 0

  def stationFuel (v : I64Vec) : Int :=
    match v.val with
    | _ :: x :: _ => x.val
    | _ => 0

  def stationPairs (stations : Slice I64Vec) : List (Int × Int) :=
    stations.val.map fun v => (stationPos v, stationFuel v)

  def stationPosAt (stations : Slice I64Vec) (i : Nat) : Int :=
    match stations.val[i]? with
    | some v => stationPos v
    | none => 0

  def stationFuelAt (stations : Slice I64Vec) (i : Nat) : Int :=
    match stations.val[i]? with
    | some v => stationFuel v
    | none => 0

  def TargetBounds (target : Int) : Prop :=
    1 ≤ target ∧ target ≤ 1000000000

  def StartFuelBounds (startFuel : Int) : Prop :=
    1 ≤ startFuel ∧ startFuel ≤ 1000000000

  def StationBounds (target : Int) (v : I64Vec) : Prop :=
    v.val.length = 2 ∧ 1 ≤ stationPos v ∧ stationPos v < target ∧
      1 ≤ stationFuel v ∧ stationFuel v < 1000000000

  def PositionsSorted (stations : Slice I64Vec) : Prop :=
    ∀ i : Nat, i + 1 < stations.val.length →
      stationPosAt stations i < stationPosAt stations (i + 1)

  def StationsWellFormed (target : Int) (stations : Slice I64Vec) : Prop :=
    stations.val.length ≤ 500 ∧ (∀ v ∈ stations.val, StationBounds target v) ∧
      PositionsSorted stations

  def ProblemConstraints (target startFuel : I64) (stations : Slice I64Vec) : Prop :=
    TargetBounds target.val ∧ StartFuelBounds startFuel.val ∧
      StationsWellFormed target.val stations

  def StrictlyIncreasing : List Nat → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => a < b ∧ StrictlyIncreasing (b :: rest)

  def selectStations (stations : Slice I64Vec) (idxs : List Nat) : List (Int × Int) :=
    idxs.map fun i => (stationPairs stations).getD i (0, 0)

  def Feasible (target : Int) : Int → List (Int × Int) → Prop
    | fuel, [] => target ≤ fuel
    | fuel, s :: rest => s.1 ≤ fuel ∧ Feasible target (fuel + s.2) rest

  def ValidPlan (target startFuel : Int) (stations : Slice I64Vec) (k : Nat) : Prop :=
    (k = 0 ∧ startFuel ≥ target) ∨
      (1 ≤ k ∧
        ∃ idxs : List Nat,
          idxs.length = k ∧ StrictlyIncreasing idxs ∧
            (∀ i ∈ idxs, i < stations.val.length) ∧
            Feasible target startFuel (selectStations stations idxs))

  def InsertOneStation (stations stations' : Slice I64Vec) : Prop :=
    ∃ (extra : I64Vec) (pre post : List I64Vec),
      stations.val = pre ++ post ∧ stations'.val = pre ++ extra :: post

  /-- Whenever the function returns a result r, the following holds. Define a valid refueling plan of k stops (for 0 <= k <= len(stations)) as: either k = 0 and start_fuel >= target, or k >= 1 and there exist indices 0 <= i_1 < i_2 < ... < i_k < len(stations) such that (1) start_fuel >= stations[i_1][0], (2) for every j with 1 <= j < k, start_fuel + sum_{m=1}^{j} stations[i_m][1] >= stations[i_{j+1}][0], and (3) start_fuel + sum_{m=1}^{k} stations[i_m][1] >= target. Then r is the smallest k in {0, 1, ..., len(stations)} for which a valid refueling plan of k stops exists; if no such k exists, r = -1.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_1 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
        ((∃ k : Nat,
            k ≤ stations.val.length ∧ ValidPlan target.val startFuel.val stations k ∧
              r.val = (k : Int) ∧
              ∀ k' : Nat, k' < k → ¬ ValidPlan target.val startFuel.val stations k') ∨
          (r.val = -1 ∧
            ∀ k : Nat,
              k ≤ stations.val.length → ¬ ValidPlan target.val startFuel.val stations k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
          ((∃ k : Nat,
              k ≤ stations.val.length ∧ ValidPlan target.val startFuel.val stations k ∧
                r.val = (k : Int) ∧
                ∀ k' : Nat, k' < k → ¬ ValidPlan target.val startFuel.val stations k') ∨
            (r.val = -1 ∧
              ∀ k : Nat,
                k ≤ stations.val.length → ¬ ValidPlan target.val startFuel.val stations k))) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail) for every input satisfying the preconditions.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_2 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∃ r : I64, min_refuel_stops target startFuel stations = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∃ r : I64, min_refuel_stops target startFuel stations = ok r) := by
    sorry

  /-- Whenever the function returns a result r, it holds that -1 <= r <= len(stations).
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_3 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
        -1 ≤ r.val ∧ r.val ≤ (stations.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
          -1 ≤ r.val ∧ r.val ≤ (stations.val.length : Int)) := by
    sorry

  /-- If start_fuel >= target, then whenever the function returns a result r, r = 0.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_4 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations)
      (hfuel : target.val ≤ startFuel.val) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations)
        (hfuel : target.val ≤ startFuel.val), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 0) := by
    sorry

  /-- If len(stations) = 0, then whenever the function returns a result r, r = 0 if start_fuel >= target, and r = -1 otherwise.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_5 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations)
      (hempty : stations.val.length = 0) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
        (target.val ≤ startFuel.val ∧ r.val = 0) ∨
          (startFuel.val < target.val ∧ r.val = -1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations)
        (hempty : stations.val.length = 0), ∀ r : I64, min_refuel_stops target startFuel stations = ok r →
          (target.val ≤ startFuel.val ∧ r.val = 0) ∨
            (startFuel.val < target.val ∧ r.val = -1)) := by
    sorry

  /-- If start_fuel + sum_{i=0}^{len(stations)-1} stations[i][1] < target, then whenever the function returns a result r, r = -1.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_6 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations)
      (hfuel : startFuel.val + ((stationPairs stations).map fun s => s.2).sum < target.val) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations)
        (hfuel : startFuel.val + ((stationPairs stations).map fun s => s.2).sum < target.val), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1) := by
    sorry

  /-- If start_fuel < target and for every i with 0 <= i < len(stations), stations[i][0] > start_fuel, then whenever the function returns a result r, r = -1.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_7 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations)
      (hfuel : startFuel.val < target.val)
      (hreach : ∀ i : Nat, i < stations.val.length → startFuel.val < stationPosAt stations i) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations)
        (hfuel : startFuel.val < target.val)
        (hreach : ∀ i : Nat, i < stations.val.length → startFuel.val < stationPosAt stations i), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r and r >= 0, there exists a valid refueling plan of exactly r stops (using the definition of valid plan from spec_1).
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_8 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → 0 ≤ r.val →
        ∃ k : Nat, r.val = (k : Int) ∧
          k ≤ stations.val.length ∧ ValidPlan target.val startFuel.val stations k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → 0 ≤ r.val →
          ∃ k : Nat, r.val = (k : Int) ∧
            k ≤ stations.val.length ∧ ValidPlan target.val startFuel.val stations k) := by
    sorry

  /-- Whenever the function returns a result r and r >= 0, for every k with 0 <= k < r, there does not exist a valid refueling plan of k stops (using the definition of valid plan from spec_1).
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_9 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → 0 ≤ r.val →
        ∀ k : Nat, (k : Int) < r.val → ¬ ValidPlan target.val startFuel.val stations k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → 0 ≤ r.val →
          ∀ k : Nat, (k : Int) < r.val → ¬ ValidPlan target.val startFuel.val stations k) := by
    sorry

  /-- Whenever the function returns a result r and r = -1, for every k with 0 <= k <= len(stations), there does not exist a valid refueling plan of k stops (using the definition of valid plan from spec_1).
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_10 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1 →
        ∀ k : Nat,
          k ≤ stations.val.length → ¬ ValidPlan target.val startFuel.val stations k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = -1 →
          ∀ k : Nat,
            k ≤ stations.val.length → ¬ ValidPlan target.val startFuel.val stations k) := by
    sorry

  /-- Let r1 be the result of the function on (target, s1, stations) and r2 be the result on (target, s2, stations). Whenever r1 >= 0, it holds that r2 >= 0 and r2 <= r1.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. Additionally, let s1 and s2 be integers with 1 <= s1 <= s2 <= 10^9. -/
  theorem spec_11 (target s1 s2 : I64) (stations : Slice I64Vec)
      (h : TargetBounds target.val ∧ StartFuelBounds s1.val ∧ StartFuelBounds s2.val ∧
        s1.val ≤ s2.val ∧ StationsWellFormed target.val stations) :
      ∀ r1 r2 : I64, min_refuel_stops target s1 stations = ok r1 →
        min_refuel_stops target s2 stations = ok r2 →
        0 ≤ r1.val → 0 ≤ r2.val ∧ r2.val ≤ r1.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (target s1 s2 : I64) (stations : Slice I64Vec)
        (h : TargetBounds target.val ∧ StartFuelBounds s1.val ∧ StartFuelBounds s2.val ∧
          s1.val ≤ s2.val ∧ StationsWellFormed target.val stations), ∀ r1 r2 : I64, min_refuel_stops target s1 stations = ok r1 →
          min_refuel_stops target s2 stations = ok r2 →
          0 ≤ r1.val → 0 ≤ r2.val ∧ r2.val ≤ r1.val) := by
    sorry

  /-- Let r1 be the result of the function on (target1, start_fuel, stations) and r2 the result on (target2, start_fuel, stations). Then: (a) if r1 = -1, then r2 = -1; and (b) if r2 >= 0, then r1 >= 0 and r1 <= r2.
    Preconditions: The inputs satisfy the problem constraints for both targets: 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target1, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. Additionally, target1 and target2 are integers with 1 <= target1 <= target2 <= 10^9. -/
  theorem spec_12 (target1 target2 startFuel : I64) (stations : Slice I64Vec)
      (h : TargetBounds target1.val ∧ TargetBounds target2.val ∧
        target1.val ≤ target2.val ∧ StartFuelBounds startFuel.val ∧
        StationsWellFormed target1.val stations) :
      ∀ r1 r2 : I64, min_refuel_stops target1 startFuel stations = ok r1 →
        min_refuel_stops target2 startFuel stations = ok r2 →
        (r1.val = -1 → r2.val = -1) ∧ (0 ≤ r2.val → 0 ≤ r1.val ∧ r1.val ≤ r2.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (target1 target2 startFuel : I64) (stations : Slice I64Vec)
        (h : TargetBounds target1.val ∧ TargetBounds target2.val ∧
          target1.val ≤ target2.val ∧ StartFuelBounds startFuel.val ∧
          StationsWellFormed target1.val stations), ∀ r1 r2 : I64, min_refuel_stops target1 startFuel stations = ok r1 →
          min_refuel_stops target2 startFuel stations = ok r2 →
          (r1.val = -1 → r2.val = -1) ∧ (0 ≤ r2.val → 0 ≤ r1.val ∧ r1.val ≤ r2.val)) := by
    sorry

  /-- Let r be the result of the function on (target, start_fuel, stations) and r' be the result on (target, start_fuel, stations'). Whenever r >= 0, it holds that r' >= 0 and r' <= r.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 499; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. Let stations' be any list obtained from stations by inserting one additional vector [p, f] (so len(stations') = len(stations) + 1) such that the positions in stations' are strictly increasing, 1 <= p < target, and 1 <= f < 10^9. -/
  theorem spec_13 (target startFuel : I64) (stations stations' : Slice I64Vec)
      (h : TargetBounds target.val ∧ StartFuelBounds startFuel.val ∧
        stations.val.length ≤ 499 ∧ (∀ v ∈ stations.val, StationBounds target.val v) ∧
        PositionsSorted stations)
      (hins : InsertOneStation stations stations')
      (h' : stations'.val.length = stations.val.length + 1 ∧
        (∀ v ∈ stations'.val, StationBounds target.val v) ∧ PositionsSorted stations') :
      ∀ r r' : I64, min_refuel_stops target startFuel stations = ok r →
        min_refuel_stops target startFuel stations' = ok r' →
        0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (target startFuel : I64) (stations stations' : Slice I64Vec)
        (h : TargetBounds target.val ∧ StartFuelBounds startFuel.val ∧
          stations.val.length ≤ 499 ∧ (∀ v ∈ stations.val, StationBounds target.val v) ∧
          PositionsSorted stations)
        (hins : InsertOneStation stations stations')
        (h' : stations'.val.length = stations.val.length + 1 ∧
          (∀ v ∈ stations'.val, StationBounds target.val v) ∧ PositionsSorted stations'), ∀ r r' : I64, min_refuel_stops target startFuel stations = ok r →
          min_refuel_stops target startFuel stations' = ok r' →
          0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val) := by
    sorry

  /-- If start_fuel < target and there exists an index i with 0 <= i < len(stations) such that start_fuel >= stations[i][0] and start_fuel + stations[i][1] >= target, then whenever the function returns a result r, r = 1.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_14 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations)
      (hfuel : startFuel.val < target.val)
      (hreach : ∃ i : Nat,
        i < stations.val.length ∧ stationPosAt stations i ≤ startFuel.val ∧
          target.val ≤ startFuel.val + stationFuelAt stations i) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations)
        (hfuel : startFuel.val < target.val)
        (hreach : ∃ i : Nat,
          i < stations.val.length ∧ stationPosAt stations i ≤ startFuel.val ∧
            target.val ≤ startFuel.val + stationFuelAt stations i), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r and r = 0, it holds that start_fuel >= target.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_15 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 0 →
        target.val ≤ startFuel.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 0 →
          target.val ≤ startFuel.val) := by
    sorry

  /-- Whenever the function returns a result r and r = 1, it holds that start_fuel < target and there exists an index i with 0 <= i < len(stations) such that start_fuel >= stations[i][0] and start_fuel + stations[i][1] >= target.
    Preconditions: The inputs satisfy the problem constraints: 1 <= target <= 10^9, 1 <= start_fuel <= 10^9, 0 <= len(stations) <= 500; for every i with 0 <= i < len(stations), len(stations[i]) = 2, 1 <= stations[i][0] < target, 1 <= stations[i][1] < 10^9; and for every i with 0 <= i < len(stations)-1, stations[i][0] < stations[i+1][0]. -/
  theorem spec_16 (target startFuel : I64) (stations : Slice I64Vec)
      (h : ProblemConstraints target startFuel stations) :
      ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 1 →
        startFuel.val < target.val ∧
          (∃ i : Nat,
            i < stations.val.length ∧ stationPosAt stations i ≤ startFuel.val ∧
              target.val ≤ startFuel.val + stationFuelAt stations i) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (target startFuel : I64) (stations : Slice I64Vec)
        (h : ProblemConstraints target startFuel stations), ∀ r : I64, min_refuel_stops target startFuel stations = ok r → r.val = 1 →
          startFuel.val < target.val ∧
            (∃ i : Nat,
              i < stations.val.length ∧ stationPosAt stations i ≤ startFuel.val ∧
                target.val ≤ startFuel.val + stationFuelAt stations i)) := by
    sorry

  end AegisSpec.MinRefuelStops
