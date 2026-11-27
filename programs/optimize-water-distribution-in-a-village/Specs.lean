import Aegis.MinCostToSupplyWater.Code.Funs

/-!
# Specifications of `Aegis.MinCostToSupplyWater.min_cost_to_supply_water`

LeetCode problem `optimize-water-distribution-in-a-village`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCostToSupplyWater

def numHouses (n : Std.I64) : Nat := n.val.toNat

def wellCount (wells : Slice Std.I64) : Nat := wells.val.length

def pipeCount (pipes : Slice (alloc.vec.Vec Std.I64)) : Nat := pipes.val.length

def wellCosts (wells : Slice Std.I64) : List Int := wells.val.map (fun w => w.val)

def wellCost (wells : Slice Std.I64) (i : Nat) : Int := (wellCosts wells).getD i 0

def vecRow (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def vecGet (v : alloc.vec.Vec Std.I64) (k : Nat) : Int := (vecRow v).getD k 0

def pipeRows (pipes : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  pipes.val.map vecRow

def pipeRow (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : List Int :=
  (pipeRows pipes).getD j []

def pipeWidth (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  (pipeRow pipes j).length

def pipeFrom (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  (pipeRow pipes j).getD 0 0

def pipeTo (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  (pipeRow pipes j).getD 1 0

def pipeCost (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int :=
  (pipeRow pipes j).getD 2 0

def pipeSrc (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  (pipeFrom pipes j - 1).toNat

def pipeDst (pipes : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  (pipeTo pipes j - 1).toNat

def listMin : List Int → Int
  | [] => 0
  | a :: l => l.foldr min a

def listMax : List Int → Int
  | [] => 0
  | a :: l => l.foldr max a

def wellCostList (n : Std.I64) (wells : Slice Std.I64) : List Int :=
  (List.range (numHouses n)).map (fun i => wellCost wells i)

def pipeCostList (pipes : Slice (alloc.vec.Vec Std.I64)) : List Int :=
  (List.range (pipeCount pipes)).map (fun j => pipeCost pipes j)

def sumWells (n : Std.I64) (wells : Slice Std.I64) : Int := (wellCostList n wells).sum

def minWellCost (n : Std.I64) (wells : Slice Std.I64) : Int :=
  listMin (wellCostList n wells)

def maxWellCost (n : Std.I64) (wells : Slice Std.I64) : Int :=
  listMax (wellCostList n wells)

def minPipeCost (pipes : Slice (alloc.vec.Vec Std.I64)) : Int :=
  listMin (pipeCostList pipes)

def IsPermOn (N : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i : Nat, i < N → σ i < N) ∧
    (∀ i j : Nat, i < N → j < N → σ i = σ j → i = j) ∧
      ∀ k : Nat, k < N → ∃ i : Nat, i < N ∧ σ i = k

def NRange (n : Std.I64) : Prop := 2 ≤ n.val ∧ n.val ≤ 10000

def WellsOk (n : Std.I64) (wells : Slice Std.I64) : Prop :=
  (wellCount wells : Int) = n.val ∧
    ∀ i : Nat, i < numHouses n → 0 ≤ wellCost wells i ∧ wellCost wells i ≤ 100000

def PipesOk (n : Std.I64) (pipes : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ pipeCount pipes ∧ pipeCount pipes ≤ 10000 ∧
    ∀ j : Nat, j < pipeCount pipes →
      pipeWidth pipes j = 3 ∧
        1 ≤ pipeFrom pipes j ∧ pipeFrom pipes j ≤ n.val ∧
          1 ≤ pipeTo pipes j ∧ pipeTo pipes j ≤ n.val ∧
            pipeFrom pipes j ≠ pipeTo pipes j ∧
              0 ≤ pipeCost pipes j ∧ pipeCost pipes j ≤ 100000

def Admissible (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  NRange n ∧ WellsOk n wells ∧ PipesOk n pipes

def Adj (pipes : Slice (alloc.vec.Vec Std.I64)) (E : Finset Nat) (a b : Nat) : Prop :=
  ∃ j ∈ E, (pipeSrc pipes j = a ∧ pipeDst pipes j = b) ∨
    (pipeSrc pipes j = b ∧ pipeDst pipes j = a)

def Reach (pipes : Slice (alloc.vec.Vec Std.I64)) (E : Finset Nat) (a b : Nat) : Prop :=
  Relation.ReflTransGen (Adj pipes E) a b

def Feasible (n : Std.I64) (pipes : Slice (alloc.vec.Vec Std.I64))
    (W E : Finset Nat) : Prop :=
  (∀ w ∈ W, w < numHouses n) ∧
    (∀ j ∈ E, j < pipeCount pipes) ∧
      ∀ h : Nat, h < numHouses n → ∃ w ∈ W, Reach pipes E h w

def planCost (wells : Slice Std.I64) (pipes : Slice (alloc.vec.Vec Std.I64))
    (W E : Finset Nat) : Int :=
  W.sum (fun w => wellCost wells w) + E.sum (fun j => pipeCost pipes j)

def IsMinPlanCost (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (r : Int) : Prop :=
  (∃ W E : Finset Nat, Feasible n pipes W E ∧ planCost wells pipes W E = r) ∧
    ∀ W E : Finset Nat, Feasible n pipes W E → r ≤ planCost wells pipes W E

def allPipes (pipes : Slice (alloc.vec.Vec Std.I64)) : Finset Nat :=
  Finset.range (pipeCount pipes)

def IsForest (pipes : Slice (alloc.vec.Vec Std.I64)) (E : Finset Nat) : Prop :=
  ∀ j ∈ E, ¬ Reach pipes (E.erase j) (pipeSrc pipes j) (pipeDst pipes j)

def IsComponents (n : Std.I64) (pipes : Slice (alloc.vec.Vec Std.I64))
    (C : Finset (Finset Nat)) : Prop :=
  (∀ c ∈ C, c.Nonempty) ∧
    (∀ c ∈ C, ∀ a ∈ c, a < numHouses n) ∧
      (∀ c ∈ C, ∀ a ∈ c, ∀ b ∈ c, Reach pipes (allPipes pipes) a b) ∧
        (∀ c ∈ C, ∀ a ∈ c, ∀ b : Nat, b < numHouses n →
          Reach pipes (allPipes pipes) a b → b ∈ c) ∧
          (∀ h : Nat, h < numHouses n → ∃ c ∈ C, h ∈ c) ∧
            ∀ c₁ ∈ C, ∀ c₂ ∈ C, ∀ a : Nat, a ∈ c₁ → a ∈ c₂ → c₁ = c₂

noncomputable def componentMinCost (wells : Slice Std.I64) (c : Finset Nat) : Int :=
  listMin (c.toList.map (fun i => wellCost wells i))

def augEdges (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) : Finset (Nat × Nat × Int) :=
  ((Finset.range (numHouses n)).image (fun i => (0, i + 1, wellCost wells i))) ∪
    ((Finset.range (pipeCount pipes)).image
      (fun j => ((pipeFrom pipes j).toNat, (pipeTo pipes j).toNat, pipeCost pipes j)))

def AugAdj (T : Finset (Nat × Nat × Int)) (a b : Nat) : Prop :=
  (∃ c : Int, (a, b, c) ∈ T) ∨ ∃ c : Int, (b, a, c) ∈ T

def AugReach (T : Finset (Nat × Nat × Int)) (a b : Nat) : Prop :=
  Relation.ReflTransGen (AugAdj T) a b

def IsSpanningTree (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (T : Finset (Nat × Nat × Int)) : Prop :=
  T ⊆ augEdges n wells pipes ∧
    (∀ v : Nat, v ≤ numHouses n → AugReach T 0 v) ∧ T.card = numHouses n

def treeWeight (T : Finset (Nat × Nat × Int)) : Int := T.sum (fun e => e.2.2)

/-- Whenever the function returns a result r on an admissible input, r equals the minimum total cost over all feasible plans. A feasible plan chooses a set W of house indices in {0,...,n-1} at which wells are built and a set E of pipe indices in {0,...,len(pipes)-1} to lay. Its cost is (sum_{w in W} wells[w]) + (sum_{j in E} pipes[j][2]). Pipe j connects houses pipes[j][0]-1 and pipes[j][1]-1, converting the input's 1-based house labels to 0-based indices. Every house h in {0,...,n-1} must be connected by selected pipes in E to at least one house in W; a house in W is connected to itself. The minimum is over all such feasible plans. Since n >= 2, at least one well is always required; the empty well set is not feasible.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. Multiple pipes between the same two houses are allowed. -/
theorem spec_1 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        IsMinPlanCost n wells pipes r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        IsMinPlanCost n wells pipes r.val) := by
  sorry

/-- The function returns a result r on every admissible input; it does not fail due to integer overflow, panic, out-of-bounds access, or any other runtime error.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_2 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∃ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∃ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= sum_{i=0}^{n-1} wells[i].
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_3 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        0 ≤ r.val ∧ r.val ≤ sumWells n wells := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        0 ≤ r.val ∧ r.val ≤ sumWells n wells) := by
  sorry

/-- Whenever the function returns a result r, r >= min_{0 <= i < n} wells[i].
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_4 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        minWellCost n wells ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        minWellCost n wells ≤ r.val) := by
  sorry

/-- Whenever n = 2 and the function returns a result r, let m = min_{0 <= j < len(pipes)} pipes[j][2]. Then r = min(wells[0] + wells[1], min(wells[0], wells[1]) + m).
  Preconditions: 2 <= n <= 10000; n = 2; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_5 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hn : n.val = 2) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = min (wellCost wells 0 + wellCost wells 1)
          (min (wellCost wells 0) (wellCost wells 1) + minPipeCost pipes) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hn : n.val = 2), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = min (wellCost wells 0 + wellCost wells 1)
          (min (wellCost wells 0) (wellCost wells 1) + minPipeCost pipes)) := by
  sorry

/-- Whenever all well costs are 0 and the function returns a result r, r = 0.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, wells[i] = 0; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_6 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hzero : ∀ i : Nat, i < numHouses n → wellCost wells i = 0) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hzero : ∀ i : Nat, i < numHouses n → wellCost wells i = 0), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r → r.val = 0) := by
  sorry

/-- Whenever every pipe cost is 0 and the function returns a result r, let G be the undirected graph with vertex set {0,...,n-1} and, for each 0 <= j < len(pipes), an edge between pipes[j][0]-1 and pipes[j][1]-1. If C_1,...,C_k are the connected components of G, each a subset of {0,...,n-1}, then r = sum_{t=1}^{k} min_{i in C_t} wells[i].
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and pipes[j][2] = 0. -/
theorem spec_7 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hzero : ∀ j : Nat, j < pipeCount pipes → pipeCost pipes j = 0)
    (C : Finset (Finset Nat)) (hC : IsComponents n pipes C) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = C.sum (fun c => componentMinCost wells c) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hzero : ∀ j : Nat, j < pipeCount pipes → pipeCost pipes j = 0)
    (C : Finset (Finset Nat)) (hC : IsComponents n pipes C), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = C.sum (fun c => componentMinCost wells c)) := by
  sorry

/-- Whenever the function returns a result r and every pipe cost satisfies pipes[j][2] >= max_{0 <= i < n} wells[i], we have r = sum_{i=0}^{n-1} wells[i].
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_8 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hexp : ∀ j : Nat, j < pipeCount pipes → maxWellCost n wells ≤ pipeCost pipes j) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = sumWells n wells := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hexp : ∀ j : Nat, j < pipeCount pipes → maxWellCost n wells ≤ pipeCost pipes j), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        r.val = sumWells n wells) := by
  sorry

/-- Whenever the function returns r on (n,wells,pipes) and r' on (n,wells,pipes'), we have r' = r.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. Also pipes' has the same length as pipes and satisfies the same pipe constraints, and there is a bijection π on {0,...,len(pipes)-1} such that pipes'[j] = pipes[π(j)] for every j. -/
theorem spec_9 (n : Std.I64) (wells : Slice Std.I64)
    (pipes pipes' : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hinput' : Admissible n wells pipes') (hlen : pipeCount pipes' = pipeCount pipes)
    (π : Nat → Nat) (hπ : IsPermOn (pipeCount pipes) π)
    (hrow : ∀ j : Nat, j < pipeCount pipes → pipeRow pipes' j = pipeRow pipes (π j)) :
    ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes' = ok r' →
          r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes pipes' : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hinput' : Admissible n wells pipes') (hlen : pipeCount pipes' = pipeCount pipes)
    (π : Nat → Nat) (hπ : IsPermOn (pipeCount pipes) π)
    (hrow : ∀ j : Nat, j < pipeCount pipes → pipeRow pipes' j = pipeRow pipes (π j)), ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes' = ok r' →
          r'.val = r.val) := by
  sorry

/-- Whenever the function returns r on (n,wells,pipes) and r' on (n,wells,pipes'), we have r' <= r.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. Also len(pipes) < 10000, e is a vector of length 3 with 1 <= e[0] <= n, 1 <= e[1] <= n, e[0] != e[1], and 0 <= e[2] <= 100000, and pipes' is pipes with e appended. -/
theorem spec_10 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hlen : pipeCount pipes < 10000) (e : alloc.vec.Vec Std.I64)
    (he_len : e.val.length = 3)
    (he0 : 1 ≤ vecGet e 0) (he0' : vecGet e 0 ≤ n.val)
    (he1 : 1 ≤ vecGet e 1) (he1' : vecGet e 1 ≤ n.val)
    (hene : vecGet e 0 ≠ vecGet e 1)
    (he2 : 0 ≤ vecGet e 2) (he2' : vecGet e 2 ≤ 100000)
    (pipes' : Slice (alloc.vec.Vec Std.I64)) (happend : pipes'.val = pipes.val ++ [e]) :
    ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes' = ok r' →
          r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (hlen : pipeCount pipes < 10000) (e : alloc.vec.Vec Std.I64)
    (he_len : e.val.length = 3)
    (he0 : 1 ≤ vecGet e 0) (he0' : vecGet e 0 ≤ n.val)
    (he1 : 1 ≤ vecGet e 1) (he1' : vecGet e 1 ≤ n.val)
    (hene : vecGet e 0 ≠ vecGet e 1)
    (he2 : 0 ≤ vecGet e 2) (he2' : vecGet e 2 ≤ 100000)
    (pipes' : Slice (alloc.vec.Vec Std.I64)) (happend : pipes'.val = pipes.val ++ [e]), ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes' = ok r' →
          r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns r on (n,wells,pipes) and r' on (n,wells',pipes), we have r' <= r.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. Also len(wells') = n and for every i, 0 <= wells'[i] <= wells[i] <= 100000. -/
theorem spec_11 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (wells' : Slice Std.I64) (hwellen : (wellCount wells' : Int) = n.val)
    (hle : ∀ i : Nat, i < numHouses n →
      0 ≤ wellCost wells' i ∧ wellCost wells' i ≤ wellCost wells i) :
    ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells' pipes = ok r' →
          r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (wells' : Slice Std.I64) (hwellen : (wellCount wells' : Int) = n.val)
    (hle : ∀ i : Nat, i < numHouses n →
      0 ≤ wellCost wells' i ∧ wellCost wells' i ≤ wellCost wells i), ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells' pipes = ok r' →
          r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist sets W ⊆ {0,...,n-1} and E ⊆ {0,...,len(pipes)-1} such that: (i) (W,E) is feasible in the sense of spec_1; (ii) its cost equals r; (iii) the undirected graph on {0,...,n-1} with edge set E is a forest, containing no cycle; and (iv) every connected component of this forest contains exactly one house from W.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_12 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        ∃ W E : Finset Nat,
          Feasible n pipes W E ∧ planCost wells pipes W E = r.val ∧ IsForest pipes E ∧
            ∀ h : Nat, h < numHouses n → ∃! w : Nat, w ∈ W ∧ Reach pipes E h w := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        ∃ W E : Finset Nat,
          Feasible n pipes W E ∧ planCost wells pipes W E = r.val ∧ IsForest pipes E ∧
            ∀ h : Nat, h < numHouses n → ∃! w : Nat, w ∈ W ∧ Reach pipes E h w) := by
  sorry

/-- Whenever the function returns r on (n,wells,pipes) and r' on (n,wells',pipes'), we have r' = r.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. Also σ is a permutation of {0,...,n-1}; wells'[i] = wells[σ(i)] for 0 <= i < n; and pipes'[j] = [σ(pipes[j][0]-1)+1, σ(pipes[j][1]-1)+1, pipes[j][2]] for 0 <= j < len(pipes). -/
theorem spec_13 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (wells' : Slice Std.I64) (pipes' : Slice (alloc.vec.Vec Std.I64)) (σ : Nat → Nat)
    (hσ : IsPermOn (numHouses n) σ)
    (hwellen : (wellCount wells' : Int) = n.val)
    (hwells' : ∀ i : Nat, i < numHouses n → wellCost wells' i = wellCost wells (σ i))
    (hplen : pipeCount pipes' = pipeCount pipes)
    (hpipes' : ∀ j : Nat, j < pipeCount pipes →
      pipeRow pipes' j =
        [(σ (pipeSrc pipes j) : Int) + 1, (σ (pipeDst pipes j) : Int) + 1,
          pipeCost pipes j]) :
    ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells' pipes' = ok r' →
          r'.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes)
    (wells' : Slice Std.I64) (pipes' : Slice (alloc.vec.Vec Std.I64)) (σ : Nat → Nat)
    (hσ : IsPermOn (numHouses n) σ)
    (hwellen : (wellCount wells' : Int) = n.val)
    (hwells' : ∀ i : Nat, i < numHouses n → wellCost wells' i = wellCost wells (σ i))
    (hplen : pipeCount pipes' = pipeCount pipes)
    (hpipes' : ∀ j : Nat, j < pipeCount pipes →
      pipeRow pipes' j =
        [(σ (pipeSrc pipes j) : Int) + 1, (σ (pipeDst pipes j) : Int) + 1,
          pipeCost pipes j]), ∀ r r' : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells' pipes' = ok r' →
          r'.val = r.val) := by
  sorry

/-- Whenever the function returns a result r on an admissible input, let G be the undirected graph with vertex set {0,1,...,n} (where 0 is a dummy node and the houses are 1,...,n) and edge set consisting of, for each house i in {1,...,n}, an edge between 0 and i with cost wells[i-1], and for each pipe index j, an edge between pipes[j][0] and pipes[j][1] with cost pipes[j][2]. Then r equals the minimum total weight of a spanning tree of G.
  Preconditions: 2 <= n <= 10000; len(wells) = n; for every i with 0 <= i < n, 0 <= wells[i] <= 100000; 1 <= len(pipes) <= 10000; for every j with 0 <= j < len(pipes), len(pipes[j]) = 3, 1 <= pipes[j][0] <= n, 1 <= pipes[j][1] <= n, pipes[j][0] != pipes[j][1], and 0 <= pipes[j][2] <= 100000. -/
theorem spec_14 (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes) :
    ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        (∃ T : Finset (Nat × Nat × Int),
            IsSpanningTree n wells pipes T ∧ treeWeight T = r.val) ∧
          ∀ T : Finset (Nat × Nat × Int),
            IsSpanningTree n wells pipes T → r.val ≤ treeWeight T := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (wells : Slice Std.I64)
    (pipes : Slice (alloc.vec.Vec Std.I64)) (hinput : Admissible n wells pipes), ∀ r : Std.I64,
      Aegis.MinCostToSupplyWater.min_cost_to_supply_water n wells pipes = ok r →
        (∃ T : Finset (Nat × Nat × Int),
            IsSpanningTree n wells pipes T ∧ treeWeight T = r.val) ∧
          ∀ T : Finset (Nat × Nat × Int),
            IsSpanningTree n wells pipes T → r.val ≤ treeWeight T) := by
  sorry

end AegisSpec.MinCostToSupplyWater
