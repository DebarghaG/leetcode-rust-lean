import Aegis.MinimumTotalDistance.Code.Funs

/-!
# Specifications of `Aegis.MinimumTotalDistance.minimum_total_distance`

LeetCode problem `minimum-total-distance-traveled`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTotalDistance

  def robotVal (robot : Slice Std.I64) (i : ℕ) : ℤ :=
    ((robot.val[i]?).map fun x => x.val).getD 0

  def factoryRow (factory : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : List ℤ :=
    ((factory.val[j]?).map fun row => row.val.map fun x => x.val).getD []

  def factoryPos (factory : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ :=
    (factoryRow factory j)[0]?.getD 0

  def factoryCap (factory : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ :=
    (factoryRow factory j)[1]?.getD 0

  def totalCapacity (factory : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range factory.val.length).map fun j => factoryCap factory j).sum

  def robotMultiset (robot : Slice Std.I64) : Multiset ℤ :=
    Multiset.ofList (robot.val.map fun x => x.val)

  def Precond (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    (1 ≤ robot.val.length ∧ robot.val.length ≤ 100) ∧
    (1 ≤ factory.val.length ∧ factory.val.length ≤ 100) ∧
    (∀ i, i < robot.val.length → -1000000000 ≤ robotVal robot i ∧ robotVal robot i ≤ 1000000000) ∧
    (∀ j, j < factory.val.length →
        (factoryRow factory j).length = 2 ∧
        -1000000000 ≤ factoryPos factory j ∧ factoryPos factory j ≤ 1000000000 ∧
        0 ≤ factoryCap factory j ∧ factoryCap factory j ≤ (robot.val.length : ℤ)) ∧
    (robot.val.length : ℤ) ≤ totalCapacity factory

  def countAssign (n : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
    ((List.range n).filter fun i => f i = j).length

  def ValidAssign (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (f : ℕ → ℕ) : Prop :=
    (∀ i, i < robot.val.length → f i < factory.val.length) ∧
    (∀ j, j < factory.val.length → (countAssign robot.val.length f j : ℤ) ≤ factoryCap factory j)

  def assignCost (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (f : ℕ → ℕ) : ℤ :=
    ((List.range robot.val.length).map fun i => |robotVal robot i - factoryPos factory (f i)|).sum

  def achievableCosts (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64)) : Set ℤ :=
    {c | ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧ assignCost robot factory f = c}

  def listMin? : List ℤ → Option ℤ
    | [] => none
    | x :: xs =>
      match listMin? xs with
      | none => some x
      | some y => some (min x y)

  def listMin (l : List ℤ) : ℤ := (listMin? l).getD 0

  def nearestAvailableDist (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (i : ℕ) : ℤ :=
    listMin (((List.range factory.val.length).filter fun j => 1 ≤ factoryCap factory j).map
      fun j => |robotVal robot i - factoryPos factory j|)

  def totalNearestAvailable (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range robot.val.length).map fun i => nearestAvailableDist robot factory i).sum

  def nearestDist (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (i : ℕ) : ℤ :=
    listMin (((List.range factory.val.length).map fun j => |robotVal robot i - factoryPos factory j|))

  def totalNearest (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range robot.val.length).map fun i => nearestDist robot factory i).sum

  def IsPermOn (n : ℕ) (pi : ℕ → ℕ) : Prop :=
    (∀ i, i < n → pi i < n) ∧
    (∀ i, i < n → ∀ i', i' < n → pi i = pi i' → i = i') ∧
    (∀ j, j < n → ∃ i, i < n ∧ pi i = j)

  /-- The function returns a result r and r = min { sum_{i=0}^{n-1} |robot[i] - factory[f(i)][0]| | f : {0,...,n-1} -> {0,...,m-1} is a valid assignment }, where n = len(robot), m = len(factory), and a valid assignment means that for every j in {0,...,m-1}, the number of i in {0,...,n-1} with f(i) = j is at most factory[j][1].
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_1 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        IsLeast (achievableCosts robot factory) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          IsLeast (achievableCosts robot factory) r.val) := by
    sorry

  /-- The function returns a result r and r >= sum_{i=0}^{n-1} min_{0 <= j < m, factory[j][1] >= 1} |robot[i] - factory[j][0]|, where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_2 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        totalNearestAvailable robot factory ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          totalNearestAvailable robot factory ≤ r.val) := by
    sorry

  /-- The function returns a result r and there exists a valid assignment f : {0,...,n-1} -> {0,...,m-1} (as defined in spec_1) such that sum_{i=0}^{n-1} |robot[i] - factory[f(i)][0]| = r, where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_3 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧ assignCost robot factory f = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧ assignCost robot factory f = r.val) := by
    sorry

  /-- The function returns a result r and for every valid assignment f : {0,...,n-1} -> {0,...,m-1} (as defined in spec_1), r <= sum_{i=0}^{n-1} |robot[i] - factory[f(i)][0]|, where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_4 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∀ f : ℕ → ℕ, ValidAssign robot factory f → r.val ≤ assignCost robot factory f := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∀ f : ℕ → ℕ, ValidAssign robot factory f → r.val ≤ assignCost robot factory f) := by
    sorry

  /-- The function returns a result r and r = min_{0 <= j < m, factory[j][1] >= 1} |robot[0] - factory[j][0]|, where m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot); len(robot) = 1. -/
  theorem spec_5 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) (hlen : robot.val.length = 1) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        r.val = nearestAvailableDist robot factory 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory) (hlen : robot.val.length = 1), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          r.val = nearestAvailableDist robot factory 0) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if there exists a valid assignment f : {0,...,n-1} -> {0,...,m-1} (as defined in spec_1) such that for every i in {0,...,n-1}, robot[i] = factory[f(i)][0], where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_6 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        (r.val = 0 ↔
          ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧
            ∀ i, i < robot.val.length → robotVal robot i = factoryPos factory (f i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          (r.val = 0 ↔
            ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧
              ∀ i, i < robot.val.length → robotVal robot i = factoryPos factory (f i))) := by
    sorry

  /-- For every integer c, define robot'[i] = robot[i] + c for all i and factory'[j] = [factory[j][0] + c, factory[j][1]] for all j. If (robot', factory') also satisfies the base preconditions (with robot' and factory' in place of robot and factory), then minimum_total_distance(robot', factory') = minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_7 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (c : ℤ) (robot' : Slice Std.I64) (factory' : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hrobot_len : robot'.val.length = robot.val.length)
      (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = robotVal robot i + c)
      (hfactory_len : factory'.val.length = factory.val.length)
      (hfactory : ∀ j, j < factory.val.length →
        factoryPos factory' j = factoryPos factory j + c ∧ factoryCap factory' j = factoryCap factory j)
      (h' : Precond robot' factory') :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory' = ok r' ∧
          r'.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (c : ℤ) (robot' : Slice Std.I64) (factory' : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hrobot_len : robot'.val.length = robot.val.length)
        (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = robotVal robot i + c)
        (hfactory_len : factory'.val.length = factory.val.length)
        (hfactory : ∀ j, j < factory.val.length →
          factoryPos factory' j = factoryPos factory j + c ∧ factoryCap factory' j = factoryCap factory j)
        (h' : Precond robot' factory'), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory' = ok r' ∧
            r'.val = r.val) := by
    sorry

  /-- For every permutation pi of {0,...,n-1}, define robot'[i] = robot[pi(i)] for all i, where n = len(robot). If (robot', factory) also satisfies the base preconditions, then minimum_total_distance(robot', factory) = minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_8 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (pi : ℕ → ℕ) (robot' : Slice Std.I64)
      (h : Precond robot factory)
      (hperm : IsPermOn robot.val.length pi)
      (hrobot_len : robot'.val.length = robot.val.length)
      (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = robotVal robot (pi i))
      (h' : Precond robot' factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory = ok r' ∧
          r'.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (pi : ℕ → ℕ) (robot' : Slice Std.I64)
        (h : Precond robot factory)
        (hperm : IsPermOn robot.val.length pi)
        (hrobot_len : robot'.val.length = robot.val.length)
        (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = robotVal robot (pi i))
        (h' : Precond robot' factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory = ok r' ∧
            r'.val = r.val) := by
    sorry

  /-- For every permutation sigma of {0,...,m-1}, define factory'[j] = factory[sigma(j)] for all j, where m = len(factory). If (robot, factory') also satisfies the base preconditions, then minimum_total_distance(robot, factory') = minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_9 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (sigma : ℕ → ℕ) (factory' : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hperm : IsPermOn factory.val.length sigma)
      (hfactory_len : factory'.val.length = factory.val.length)
      (hfactory_pos : ∀ j, j < factory.val.length → factoryPos factory' j = factoryPos factory (sigma j))
      (hfactory_cap : ∀ j, j < factory.val.length → factoryCap factory' j = factoryCap factory (sigma j))
      (h' : Precond robot factory') :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
          r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (sigma : ℕ → ℕ) (factory' : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hperm : IsPermOn factory.val.length sigma)
        (hfactory_len : factory'.val.length = factory.val.length)
        (hfactory_pos : ∀ j, j < factory.val.length → factoryPos factory' j = factoryPos factory (sigma j))
        (hfactory_cap : ∀ j, j < factory.val.length → factoryCap factory' j = factoryCap factory (sigma j))
        (h' : Precond robot factory'), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
            r'.val = r.val) := by
    sorry

  /-- Let factory' be any list of length m such that for all j, factory'[j][0] = factory[j][0] and factory'[j][1] >= factory[j][1], and suppose (robot, factory') also satisfies the base preconditions. Then minimum_total_distance(robot, factory') <= minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_10 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (factory' : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hfactory_len : factory'.val.length = factory.val.length)
      (hfactory_pos : ∀ j, j < factory.val.length → factoryPos factory' j = factoryPos factory j)
      (hfactory_cap : ∀ j, j < factory.val.length → factoryCap factory j ≤ factoryCap factory' j)
      (h' : Precond robot factory') :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
          r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (factory' : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hfactory_len : factory'.val.length = factory.val.length)
        (hfactory_pos : ∀ j, j < factory.val.length → factoryPos factory' j = factoryPos factory j)
        (hfactory_cap : ∀ j, j < factory.val.length → factoryCap factory j ≤ factoryCap factory' j)
        (h' : Precond robot factory'), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
            r'.val ≤ r.val) := by
    sorry

  /-- Let robot' be any list such that the multiset of robot' contains the multiset of robot, and suppose (robot', factory) also satisfies the base preconditions. Then minimum_total_distance(robot', factory) >= minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_11 (robot : Slice Std.I64) (robot' : Slice Std.I64)
      (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hsub : robotMultiset robot ≤ robotMultiset robot')
      (h' : Precond robot' factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory = ok r' ∧
          r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (robot : Slice Std.I64) (robot' : Slice Std.I64)
        (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hsub : robotMultiset robot ≤ robotMultiset robot')
        (h' : Precond robot' factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory = ok r' ∧
            r.val ≤ r'.val) := by
    sorry

  /-- The function returns a result r and r <= 2 * 10^9 * len(robot).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_12 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        r.val ≤ 2000000000 * (robot.val.length : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          r.val ≤ 2000000000 * (robot.val.length : ℤ)) := by
    sorry

  /-- Suppose factory[j][1] = 0 for some j. Let factory' be obtained by deleting row j from factory, and assume (robot, factory') also satisfies the base preconditions. Then minimum_total_distance(robot, factory') = minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_13 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (j : ℕ) (factory' : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hj : j < factory.val.length)
      (hjcap : factoryCap factory j = 0)
      (hfactory : factory'.val = factory.val.eraseIdx j)
      (h' : Precond robot factory') :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
          r'.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (j : ℕ) (factory' : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hj : j < factory.val.length)
        (hjcap : factoryCap factory j = 0)
        (hfactory : factory'.val = factory.val.eraseIdx j)
        (h' : Precond robot factory'), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot factory' = ok r' ∧
            r'.val = r.val) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{n-1} min_{0 <= j < m} |robot[i] - factory[j][0]|, where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot); additionally, for every j with 0 <= j < len(factory), factory[j][1] >= len(robot). -/
  theorem spec_14 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hcap : ∀ j, j < factory.val.length → (robot.val.length : ℤ) ≤ factoryCap factory j) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        r.val = totalNearest robot factory := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hcap : ∀ j, j < factory.val.length → (robot.val.length : ℤ) ≤ factoryCap factory j), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          r.val = totalNearest robot factory) := by
    sorry

  /-- The function returns a result r and there exists a valid assignment f : {0,...,n-1} -> {0,...,m-1} (as defined in spec_1) such that sum_{i=0}^{n-1} |robot[i] - factory[f(i)][0]| = r and, for all i,k with 0 <= i,k < n and robot[i] < robot[k], factory[f(i)][0] <= factory[f(k)][0], where n = len(robot) and m = len(factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_15 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory) :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧ assignCost robot factory f = r.val ∧
          ∀ i k, i < robot.val.length → k < robot.val.length → robotVal robot i < robotVal robot k →
            factoryPos factory (f i) ≤ factoryPos factory (f k) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ f : ℕ → ℕ, ValidAssign robot factory f ∧ assignCost robot factory f = r.val ∧
            ∀ i k, i < robot.val.length → k < robot.val.length → robotVal robot i < robotVal robot k →
              factoryPos factory (f i) ≤ factoryPos factory (f k)) := by
    sorry

  /-- For robot'[i] = -robot[i] for all i and factory'[j] = [-factory[j][0], factory[j][1]] for all j, if (robot', factory') also satisfies the base preconditions, then minimum_total_distance(robot', factory') = minimum_total_distance(robot, factory).
    Preconditions: 1 <= len(robot) <= 100 and 1 <= len(factory) <= 100; for every i with 0 <= i < len(robot), -10^9 <= robot[i] <= 10^9; for every j with 0 <= j < len(factory), factory[j] is a list of length 2 with -10^9 <= factory[j][0] <= 10^9 and 0 <= factory[j][1] <= len(robot); sum_{j=0}^{len(factory)-1} factory[j][1] >= len(robot). -/
  theorem spec_16 (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
      (robot' : Slice Std.I64) (factory' : Slice (alloc.vec.Vec Std.I64))
      (h : Precond robot factory)
      (hrobot_len : robot'.val.length = robot.val.length)
      (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = -robotVal robot i)
      (hfactory_len : factory'.val.length = factory.val.length)
      (hfactory : ∀ j, j < factory.val.length →
        factoryPos factory' j = -factoryPos factory j ∧ factoryCap factory' j = factoryCap factory j)
      (h' : Precond robot' factory') :
      ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
        ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory' = ok r' ∧
          r'.val = r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (robot : Slice Std.I64) (factory : Slice (alloc.vec.Vec Std.I64))
        (robot' : Slice Std.I64) (factory' : Slice (alloc.vec.Vec Std.I64))
        (h : Precond robot factory)
        (hrobot_len : robot'.val.length = robot.val.length)
        (hrobot : ∀ i, i < robot.val.length → robotVal robot' i = -robotVal robot i)
        (hfactory_len : factory'.val.length = factory.val.length)
        (hfactory : ∀ j, j < factory.val.length →
          factoryPos factory' j = -factoryPos factory j ∧ factoryCap factory' j = factoryCap factory j)
        (h' : Precond robot' factory'), ∃ r, Aegis.MinimumTotalDistance.minimum_total_distance robot factory = ok r ∧
          ∃ r', Aegis.MinimumTotalDistance.minimum_total_distance robot' factory' = ok r' ∧
            r'.val = r.val) := by
    sorry

  end AegisSpec.MinimumTotalDistance
