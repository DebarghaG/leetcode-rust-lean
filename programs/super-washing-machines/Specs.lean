import Aegis.FindMinMoves.Code.Funs

/-!
# Specifications of `Aegis.FindMinMoves.find_min_moves`

LeetCode problem `super-washing-machines`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMinMoves

  open Aeneas Aeneas.Std Result
  open Aegis.FindMinMoves (find_min_moves)

  def contents (machines : Slice Std.I64) : List Int := machines.val.map (fun x => x.val)

  def entry (machines : Slice Std.I64) (i : Nat) : Int := (contents machines).getD i 0

  def prefixSum (machines : Slice Std.I64) (m : Nat) : Int := ((contents machines).take m).sum

  def totalDresses (machines : Slice Std.I64) : Int := (contents machines).sum

  def card (machines : Slice Std.I64) : Int := (machines.val.length : Int)

  def TotalDivisible (machines : Slice Std.I64) : Prop := card machines ∣ totalDresses machines

  def avg (machines : Slice Std.I64) : Int := totalDresses machines / card machines

  abbrev Config (n : Nat) : Type := Fin n → Int

  def initialConfig (machines : Slice Std.I64) : Config machines.val.length :=
    fun i => (machines.val.get i).val

  def uniformConfig (n : Nat) (a : Int) : Config n := fun _ => a

  def LegalMove (n : Nat) (c c' : Config n) : Prop :=
    ∃ out : Fin n → Int, ∃ tgt : Fin n → Int,
      (∀ i, out i = 0 ∨ out i = 1) ∧
      (∀ i, out i = 1 → 1 ≤ c i) ∧
      (∀ i, out i = 1 →
        (tgt i = -1 ∧ 1 ≤ (i : Nat)) ∨ (tgt i = 1 ∧ (i : Nat) + 1 < n)) ∧
      (∀ i, c' i = c i - out i +
        ∑ j : Fin n, (if out j = 1 ∧ (j : Int) + tgt j = (i : Int) then (1 : Int) else 0))

  def ReachIn (n : Nat) : Nat → Config n → Config n → Prop
    | 0, c, d => d = c
    | t + 1, c, d => ∃ m, LegalMove n c m ∧ ReachIn n t m d

  def ReachesUniform (machines : Slice Std.I64) (a : Int) (t : Nat) : Prop :=
    ReachIn machines.val.length t (initialConfig machines) (uniformConfig machines.val.length a)

  def IsMinMoves (machines : Slice Std.I64) (a : Int) (r : Int) : Prop :=
    (∃ t : Nat, (t : Int) = r ∧ ReachesUniform machines a t) ∧
      ∀ t : Nat, (t : Int) < r → ¬ ReachesUniform machines a t

  def prefixImbalance (machines : Slice Std.I64) (k : Nat) : Int :=
    |prefixSum machines (k + 1) - ((k : Int) + 1) * avg machines|

  def surplusSum (machines : Slice Std.I64) : Int :=
    ((List.range machines.val.length).map (fun i => max 0 (entry machines i - avg machines))).sum

  def listMax (l : List Int) : Int := l.foldr max 0

  def boundValue (machines : Slice Std.I64) : Int :=
    listMax (((List.range machines.val.length).map
          (fun i => max 0 (entry machines i - avg machines))) ++
      ((List.range machines.val.length).map (fun k => prefixImbalance machines k)))

  /-- Let T = sum_{i=0}^{n-1} machines[i]. The function returns a result r. If T is not divisible by n, then r = -1. If T is divisible by n, let a = T / n. A legal move from a configuration c (a sequence of n nonnegative integers) to a configuration c' is defined as follows: for each index i there is out_i in {0,1}; if out_i = 1 then c_i >= 1 and i chooses exactly one target neighbor i-1 or i+1 that exists in [0,n-1]; for each i, c'_i = c_i - out_i + in_i, where in_i is the number of indices j with out_j = 1 whose chosen target is i. Then r is the least integer t >= 0 for which there exists a sequence of configurations c^0, c^1, ..., c^t such that c^0 = machines, each step c^s to c^{s+1} (0 <= s < t) is a legal move, and c^t_i = a for every i with 0 <= i < n.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_1 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        (¬ TotalDivisible machines → r.val = -1) ∧
        (TotalDivisible machines → IsMinMoves machines (avg machines) r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          (¬ TotalDivisible machines → r.val = -1) ∧
          (TotalDivisible machines → IsMinMoves machines (avg machines) r.val)) := by
    sorry

  /-- Let T = sum_{i=0}^{n-1} machines[i]. The function returns a result r, and r = -1 if and only if T is not divisible by n.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_2 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        (r.val = -1 ↔ ¬ TotalDivisible machines) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          (r.val = -1 ↔ ¬ TotalDivisible machines)) := by
    sorry

  /-- Let T = sum_{i=0}^{n-1} machines[i]. If T is divisible by n, then the function returns a result r and r >= 0.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_3 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      TotalDivisible machines →
        ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), TotalDivisible machines →
          ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if machines[0] = machines[1] = ... = machines[n-1] (equivalently, for every i and j with 0 <= i < n and 0 <= j < n, machines[i] = machines[j]).
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_4 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        (r.val = 0 ↔ ∀ i j, i < machines.val.length → j < machines.val.length →
          entry machines i = entry machines j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          (r.val = 0 ↔ ∀ i j, i < machines.val.length → j < machines.val.length →
            entry machines i = entry machines j)) := by
    sorry

  /-- Let avg = T / n. The function returns a result r, and for every k with 0 <= k < n-1, r >= | (sum_{i=0}^{k} machines[i]) - (k+1) * avg |.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= machines[i] <= 100000, and the total T = sum_{i=0}^{n-1} machines[i] is divisible by n. -/
  theorem spec_5 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000)
      (hdiv : TotalDivisible machines) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        ∀ k, k < machines.val.length - 1 → r.val ≥ prefixImbalance machines k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000)
        (hdiv : TotalDivisible machines), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          ∀ k, k < machines.val.length - 1 → r.val ≥ prefixImbalance machines k) := by
    sorry

  /-- Let avg = T / n. The function returns a result r, and for every i with 0 <= i < n, r >= max(0, machines[i] - avg).
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= machines[i] <= 100000, and the total T = sum_{i=0}^{n-1} machines[i] is divisible by n. -/
  theorem spec_6 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000)
      (hdiv : TotalDivisible machines) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        ∀ i, i < machines.val.length → r.val ≥ max 0 (entry machines i - avg machines) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000)
        (hdiv : TotalDivisible machines), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          ∀ i, i < machines.val.length → r.val ≥ max 0 (entry machines i - avg machines)) := by
    sorry

  /-- Let T = sum_{i=0}^{n-1} machines[i]. The function returns a result r. If T is not divisible by n, then r = -1. If T is divisible by n, let avg = T / n; then r = max( { max(0, machines[i] - avg) | 0 <= i < n } union { | (sum_{j=0}^{k} machines[j]) - (k+1) * avg | | 0 <= k < n } ).
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_7 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        (¬ TotalDivisible machines → r.val = -1) ∧
        (TotalDivisible machines → r.val = boundValue machines) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          (¬ TotalDivisible machines → r.val = -1) ∧
          (TotalDivisible machines → r.val = boundValue machines)) := by
    sorry

  /-- Let avg = T / n and let D = sum_{i=0}^{n-1} max(0, machines[i] - avg). The function returns a result r, and r <= D.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= machines[i] <= 100000, and the total T = sum_{i=0}^{n-1} machines[i] is divisible by n. -/
  theorem spec_8 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000)
      (hdiv : TotalDivisible machines) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧ r.val ≤ surplusSum machines := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000)
        (hdiv : TotalDivisible machines), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧ r.val ≤ surplusSum machines) := by
    sorry

  /-- Under the stated preconditions, the function returns a result r (it does not fail, overflow, or panic).
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_9 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r) := by
    sorry

  /-- Let n = len(machines). The function returns a result r, and r = -1 if and only if for every integer a >= 0 there is no finite sequence of legal moves (as defined in spec_1) that starts from machines and ends at the configuration in which every machine has exactly a dresses.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000 and, for every i with 0 <= i < n, 0 <= machines[i] <= 100000. -/
  theorem spec_10 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        (r.val = -1 ↔ ∀ a : Int, 0 ≤ a → ¬ ∃ t : Nat, ReachesUniform machines a t) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          (r.val = -1 ↔ ∀ a : Int, 0 ≤ a → ¬ ∃ t : Nat, ReachesUniform machines a t)) := by
    sorry

  /-- Let avg = T / n. The function returns a result r, and there exists a finite sequence of legal moves (as defined in spec_1) starting from machines and ending at the configuration in which every machine has exactly avg dresses; moreover, the sequence has exactly r moves.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= machines[i] <= 100000, and the total T = sum_{i=0}^{n-1} machines[i] is divisible by n. -/
  theorem spec_11 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000)
      (hdiv : TotalDivisible machines) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        ∃ t : Nat, (t : Int) = r.val ∧ ReachesUniform machines (avg machines) t := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000)
        (hdiv : TotalDivisible machines), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          ∃ t : Nat, (t : Int) = r.val ∧ ReachesUniform machines (avg machines) t) := by
    sorry

  /-- Let avg = T / n. The function returns a result r, and for every integer t with 0 <= t < r there is no finite sequence of t legal moves (as defined in spec_1) that starts from machines and ends at the configuration in which every machine has exactly avg dresses.
    Preconditions: Let n = len(machines). Assume 1 <= n <= 10000, for every i with 0 <= i < n, 0 <= machines[i] <= 100000, and the total T = sum_{i=0}^{n-1} machines[i] is divisible by n. -/
  theorem spec_12 (machines : Slice Std.I64)
      (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
      (hbound : ∀ i, i < machines.val.length →
        0 ≤ entry machines i ∧ entry machines i ≤ 100000)
      (hdiv : TotalDivisible machines) :
      ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
        ∀ t : Nat, (t : Int) < r.val → ¬ ReachesUniform machines (avg machines) t := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (machines : Slice Std.I64)
        (hpos : 1 ≤ machines.val.length) (hlen : machines.val.length ≤ 10000)
        (hbound : ∀ i, i < machines.val.length →
          0 ≤ entry machines i ∧ entry machines i ≤ 100000)
        (hdiv : TotalDivisible machines), ∃ r : Std.I64, find_min_moves machines = Result.ok r ∧
          ∀ t : Nat, (t : Int) < r.val → ¬ ReachesUniform machines (avg machines) t) := by
    sorry

  end AegisSpec.FindMinMoves
