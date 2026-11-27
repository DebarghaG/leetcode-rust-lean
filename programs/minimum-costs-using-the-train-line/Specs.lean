import Aegis.MinimumCosts.Code.Funs

/-!
# Specifications of `Aegis.MinimumCosts.minimum_costs`

LeetCode problem `minimum-costs-using-the-train-line`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumCosts

  namespace AegisSpec.MinimumCosts

  inductive Route where
    | R : Route
    | E : Route
    deriving DecidableEq, Repr

  def slList (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

  def vecList (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

  def nthD (l : List ℤ) (i : ℕ) : ℤ := (l[i]?).getD 0

  def slAt (s : Slice I64) (i : ℕ) : ℤ := nthD (slList s) i

  def outAt (r : alloc.vec.Vec I64) (j : ℕ) : ℤ := nthD (vecList r) j

  def prefixSum (l : List ℤ) (j : ℕ) : ℤ := (l.take (j + 1)).sum

  def minList (l m : List ℤ) : List ℤ := l.zipWith (fun a b => min a b) m

  def moveCost (regular express : List ℤ) (expressCost : ℤ) :
      (ℕ × Route) → (ℕ × Route) → Option ℤ
    | (i, Route.R), (j, Route.R) => if j = i + 1 then regular[i]? else none
    | (i, Route.E), (j, Route.E) => if j = i + 1 then express[i]? else none
    | (i, Route.R), (j, Route.E) => if j = i then some expressCost else none
    | (i, Route.E), (j, Route.R) => if j = i then some 0 else none

  def pathCost (regular express : List ℤ) (expressCost : ℤ) : List (ℕ × Route) → Option ℤ
    | [] => some 0
    | [_] => some 0
    | s :: t :: rest =>
      (moveCost regular express expressCost s t).bind (fun c =>
        (pathCost regular express expressCost (t :: rest)).map (fun d => c + d))

  def IsJourneyTo (regular express : List ℤ) (expressCost : ℤ) (k : ℕ) (u : Route)
      (l : List (ℕ × Route)) (c : ℤ) : Prop :=
    l.head? = some (0, Route.R) ∧ l.getLast? = some (k, u) ∧
      pathCost regular express expressCost l = some c

  def IsJourneyToStop (regular express : List ℤ) (expressCost : ℤ) (k : ℕ)
      (l : List (ℕ × Route)) (c : ℤ) : Prop :=
    IsJourneyTo regular express expressCost k Route.R l c ∨
      IsJourneyTo regular express expressCost k Route.E l c

  def MinCostToStop (regular express : List ℤ) (expressCost : ℤ) (k : ℕ) (c : ℤ) : Prop :=
    (∃ (u : Route) (l : List (ℕ × Route)),
        IsJourneyTo regular express expressCost k u l c) ∧
      ∀ (u : Route) (l : List (ℕ × Route)) (c' : ℤ),
        IsJourneyTo regular express expressCost k u l c' → c ≤ c'

  def MinCostAt (regular express : List ℤ) (expressCost : ℤ) (k : ℕ) (u : Route)
      (c : ℤ) : Prop :=
    (∃ l : List (ℕ × Route), IsJourneyTo regular express expressCost k u l c) ∧
      ∀ (l : List (ℕ × Route)) (c' : ℤ),
        IsJourneyTo regular express expressCost k u l c' → c ≤ c'

  /-- Whenever the function returns a result r, len(r) = n and for every j with 0 <= j < n, r[j] = mc(j+1), where mc(k) is the minimum cost to reach stop k from stop 0 over all journeys defined as follows. A state is (i,t) with 0 <= i <= n and t in {R,E}. A journey from (0,R) to (k,u) is a finite sequence of steps, each of one of these forms: (i,R) -> (i+1,R) with cost regular[i] for 0 <= i < n; (i,E) -> (i+1,E) with cost express[i] for 0 <= i < n; (i,R) -> (i,E) with cost express_cost for 0 <= i <= n; (i,E) -> (i,R) with cost 0 for 0 <= i <= n. The cost of a journey is the sum of its step costs. mc(k) is the least integer c for which such a journey from (0,R) to (k,R) or from (0,R) to (k,E) has cost c.
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. All indices used below are 0-based; in the original 1-indexed statement, regular[i] and express[i] are the costs from stop i to stop i+1, and output position j describes stop j+1. -/
  theorem spec_1 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        r.val.length = regular.val.length ∧
          ∀ j, j < regular.val.length →
            ∃ c : ℤ,
              MinCostToStop (slList regular) (slList express) express_cost.val (j + 1) c ∧
                outAt r j = c := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          r.val.length = regular.val.length ∧
            ∀ j, j < regular.val.length →
              ∃ c : ℤ,
                MinCostToStop (slList regular) (slList express) express_cost.val (j + 1) c ∧
                  outAt r j = c) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(regular).
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_2 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        r.val.length = regular.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          r.val.length = regular.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n, 1 <= r[j].
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_3 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length → 1 ≤ outAt r j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length → 1 ≤ outAt r j) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = min(regular[0], express_cost + express[0]).
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_4 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        outAt r 0 = min (slAt regular 0) (express_cost.val + slAt express 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          outAt r 0 = min (slAt regular 0) (express_cost.val + slAt express 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n, r[j] <= sum_{t=0}^{j} regular[t].
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_5 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length → outAt r j ≤ prefixSum (slList regular) j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length → outAt r j ≤ prefixSum (slList regular) j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n, r[j] <= express_cost + sum_{t=0}^{j} express[t].
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_6 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length →
          outAt r j ≤ express_cost.val + prefixSum (slList express) j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length →
            outAt r j ≤ express_cost.val + prefixSum (slList express) j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n, r[j] >= sum_{t=0}^{j} min(regular[t], express[t]).
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_7 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length →
          prefixSum (minList (slList regular) (slList express)) j ≤ outAt r j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length →
            prefixSum (minList (slList regular) (slList express)) j ≤ outAt r j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n - 1, r[j+1] >= r[j] + min(regular[j+1], express[j+1]).
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_8 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length - 1 →
          outAt r j + min (slAt regular (j + 1)) (slAt express (j + 1)) ≤ outAt r (j + 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length - 1 →
            outAt r j + min (slAt regular (j + 1)) (slAt express (j + 1)) ≤ outAt r (j + 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n - 1, r[j+1] <= r[j] + regular[j+1].
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_9 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length - 1 →
          outAt r (j + 1) ≤ outAt r j + slAt regular (j + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length - 1 →
            outAt r (j + 1) ≤ outAt r j + slAt regular (j + 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n - 1, r[j+1] <= r[j] + express[j+1] + express_cost.
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_10 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length - 1 →
          outAt r (j + 1) ≤ outAt r j + slAt express (j + 1) + express_cost.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length - 1 →
            outAt r (j + 1) ≤ outAt r j + slAt express (j + 1) + express_cost.val) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n there exists a journey from (0,R) to stop j+1, ending on either R or E, whose total cost is exactly r[j], where a journey uses these moves: advance on the current route with cost regular[i] or express[i] for an edge from stop i to i+1; transfer from R to E at any stop with cost express_cost; transfer from E to R at any stop with cost 0.
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_11 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length →
          ∃ l : List (ℕ × Route),
            IsJourneyToStop (slList regular) (slList express) express_cost.val (j + 1) l
              (outAt r j) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length →
            ∃ l : List (ℕ × Route),
              IsJourneyToStop (slList regular) (slList express) express_cost.val (j + 1) l
                (outAt r j)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n and every journey from (0,R) to stop j+1 ending on either R or E, the total cost of that journey is at least r[j].
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_12 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∀ j, j < regular.val.length →
          ∀ (l : List (ℕ × Route)) (c : ℤ),
            IsJourneyToStop (slList regular) (slList express) express_cost.val (j + 1) l c →
              outAt r j ≤ c := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∀ j, j < regular.val.length →
            ∀ (l : List (ℕ × Route)) (c : ℤ),
              IsJourneyToStop (slList regular) (slList express) express_cost.val (j + 1) l c →
                outAt r j ≤ c) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions; no i64 arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_13 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∃ r, minimum_costs regular express express_cost = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∃ r, minimum_costs regular express express_cost = ok r) := by
    sorry

  /-- Whenever the function returns a result r, let R[k] be the minimum cost of a journey from (0,R) to (k,R) and E[k] the minimum cost of a journey from (0,R) to (k,E), for 0 <= k <= n, using the journey model of spec_1. Then R[0] = 0, E[0] = express_cost, and for every k with 0 <= k < n, R[k+1] = min(R[k] + regular[k], E[k] + express[k]) and E[k+1] = min(E[k] + express[k], R[k] + regular[k] + express_cost); moreover, for every j with 0 <= j < n, r[j] = min(R[j+1], E[j+1]).
    Preconditions: Let n = len(regular). The constraints are: len(regular) = len(express) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= regular[i] <= 100000 and 1 <= express[i] <= 100000, and 1 <= express_cost <= 100000. -/
  theorem spec_14 (regular express : Slice I64) (express_cost : I64)
      (hlen : regular.val.length = express.val.length)
      (hpos : 1 ≤ regular.val.length)
      (hn : regular.val.length ≤ 100000)
      (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
      (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
      (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000) :
      ∀ r, minimum_costs regular express express_cost = ok r →
        ∃ R E : ℕ → ℤ,
          (∀ k, k ≤ regular.val.length →
              MinCostAt (slList regular) (slList express) express_cost.val k Route.R (R k)) ∧
            (∀ k, k ≤ regular.val.length →
              MinCostAt (slList regular) (slList express) express_cost.val k Route.E (E k)) ∧
            R 0 = 0 ∧
            E 0 = express_cost.val ∧
            (∀ k, k < regular.val.length →
              R (k + 1) = min (R k + slAt regular k) (E k + slAt express k)) ∧
            (∀ k, k < regular.val.length →
              E (k + 1) =
                min (E k + slAt express k) (R k + slAt regular k + express_cost.val)) ∧
            (∀ j, j < regular.val.length → outAt r j = min (R (j + 1)) (E (j + 1))) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (regular express : Slice I64) (express_cost : I64)
        (hlen : regular.val.length = express.val.length)
        (hpos : 1 ≤ regular.val.length)
        (hn : regular.val.length ≤ 100000)
        (hreg : ∀ i, i < regular.val.length → 1 ≤ slAt regular i ∧ slAt regular i ≤ 100000)
        (hexp : ∀ i, i < express.val.length → 1 ≤ slAt express i ∧ slAt express i ≤ 100000)
        (hec : 1 ≤ express_cost.val ∧ express_cost.val ≤ 100000), ∀ r, minimum_costs regular express express_cost = ok r →
          ∃ R E : ℕ → ℤ,
            (∀ k, k ≤ regular.val.length →
                MinCostAt (slList regular) (slList express) express_cost.val k Route.R (R k)) ∧
              (∀ k, k ≤ regular.val.length →
                MinCostAt (slList regular) (slList express) express_cost.val k Route.E (E k)) ∧
              R 0 = 0 ∧
              E 0 = express_cost.val ∧
              (∀ k, k < regular.val.length →
                R (k + 1) = min (R k + slAt regular k) (E k + slAt express k)) ∧
              (∀ k, k < regular.val.length →
                E (k + 1) =
                  min (E k + slAt express k) (R k + slAt regular k + express_cost.val)) ∧
              (∀ j, j < regular.val.length → outAt r j = min (R (j + 1)) (E (j + 1)))) := by
    sorry

  end AegisSpec.MinimumCosts
