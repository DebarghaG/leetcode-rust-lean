import Aegis.TotalCost.Code.Funs

/-!
# Specifications of `Aegis.TotalCost.total_cost`

LeetCode problem `total-cost-to-hire-k-workers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TotalCost

def vals (costs : Slice Std.I64) : List Int := costs.val.map (fun x => x.val)

def Pre (costs : Slice Std.I64) (k candidates : Std.I64) : Prop :=
  1 ≤ costs.val.length ∧
    costs.val.length ≤ 100000 ∧
    (∀ i : Fin costs.val.length,
      1 ≤ (costs.val.get i).val ∧ (costs.val.get i).val ≤ 100000) ∧
    1 ≤ k.val ∧ k.val ≤ (costs.val.length : Int) ∧
    1 ≤ candidates.val ∧ candidates.val ≤ (costs.val.length : Int)

def insertInt (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

def sortInt : List Int → List Int
  | [] => []
  | x :: xs => insertInt x (sortInt xs)

def beforeIdx (cs : List Int) (i j : Nat) : Bool :=
  cs.getD i 0 < cs.getD j 0 || (cs.getD i 0 == cs.getD j 0 && i < j)

def insertIdx (cs : List Int) (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if beforeIdx cs i j then i :: j :: js else j :: insertIdx cs i js

def sortIdx (cs : List Int) : List Nat → List Nat
  | [] => []
  | i :: is => insertIdx cs i (sortIdx cs is)

def sortedIndices (cs : List Int) : List Nat := sortIdx cs (List.range cs.length)

def window (candidates : Nat) (R : List Nat) : List Nat :=
  let m := Nat.min candidates R.length
  (R.take m ++ R.drop (R.length - m)).dedup

def pickFrom (cs : List Int) : List Nat → Option Nat
  | [] => none
  | i :: rest =>
    match pickFrom cs rest with
    | none => some i
    | some b => if beforeIdx cs i b then some i else some b

def pick (cs : List Int) (candidates : Nat) (R : List Nat) : Option Nat :=
  pickFrom cs (window candidates R)

def removeIdx (R : List Nat) (w : Nat) : List Nat := R.filter (fun i => i != w)

def hires (cs : List Int) (candidates : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | k + 1, R =>
    match pick cs candidates R with
    | none => []
    | some w => w :: hires cs candidates k (removeIdx R w)

def costOf (cs : List Int) (is : List Nat) : Int := (is.map (fun i => cs.getD i 0)).sum

def hireTotalFrom (cs : List Int) (candidates k : Nat) (R : List Nat) : Int :=
  costOf cs (hires cs candidates k R)

def hiredSeq (cs : List Int) (candidates k : Nat) : List Nat :=
  hires cs candidates k (List.range cs.length)

def hireTotal (cs : List Int) (candidates k : Nat) : Int :=
  hireTotalFrom cs candidates k (List.range cs.length)

def hireAt (cs : List Int) (candidates k t : Nat) : Nat := (hiredSeq cs candidates k).getD t 0

def firstHire (cs : List Int) (candidates : Nat) : Nat :=
  (pick cs candidates (List.range cs.length)).getD 0

def states (cs : List Int) (candidates : Nat) : Nat → List Nat → List (List Nat)
  | 0, R => [R]
  | k + 1, R =>
    R :: (match pick cs candidates R with
          | none => []
          | some w => states cs candidates k (removeIdx R w))

def stateAt (cs : List Int) (candidates t : Nat) : List Nat :=
  (states cs candidates t (List.range cs.length)).getD t []

/-- Let R_0 be the list [0,1,...,n-1] of original worker indices. For each session t = 0,1,...,k-1, let m_t = len(R_t), let C_t consist of the first min(candidates,m_t) entries of R_t together with the last min(candidates,m_t) entries of R_t (duplicates counted once), and let w_t be the entry of C_t with minimal costs[w_t], breaking ties by choosing the smallest original index. Set R_{t+1} = R_t with w_t removed, preserving order. Whenever total_cost(costs,k,candidates) returns a result r, r = sum_{t=0}^{k-1} costs[w_t].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_1 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val = hireTotal (vals costs) candidates.val.toNat k.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val = hireTotal (vals costs) candidates.val.toNat k.val.toNat) := by
  sorry

/-- Under these preconditions, total_cost(costs,k,candidates) returns a result r and does not fail (no out-of-bounds, panic, or i64 overflow).
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_2 (costs : Slice Std.I64) (k candidates : Std.I64)
    (hpre : Pre costs k candidates) :
    ∃ r : Std.I64, Aegis.TotalCost.total_cost costs k candidates = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates : Std.I64)
    (hpre : Pre costs k candidates), ∃ r : Std.I64, Aegis.TotalCost.total_cost costs k candidates = ok r) := by
  sorry

/-- Let d_0 <= d_1 <= ... <= d_{n-1} be the entries of costs sorted in nondecreasing order, with multiplicity. Whenever total_cost(costs,k,candidates) returns a result r, r >= sum_{j=0}^{k-1} d_j.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_3 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    ((sortInt (vals costs)).take k.val.toNat).sum ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), ((sortInt (vals costs)).take k.val.toNat).sum ≤ r.val) := by
  sorry

/-- Let d_0 <= d_1 <= ... <= d_{n-1} be the entries of costs sorted in nondecreasing order, with multiplicity. Whenever total_cost(costs,k,candidates) returns a result r, r <= sum_{j=n-k}^{n-1} d_j.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_4 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val ≤ ((sortInt (vals costs)).drop (costs.val.length - k.val.toNat)).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val ≤ ((sortInt (vals costs)).drop (costs.val.length - k.val.toNat)).sum) := by
  sorry

/-- Whenever total_cost(costs,k,candidates) returns a result r, there exist k pairwise distinct integer indices i_0,...,i_{k-1} with 0 <= i_j < n such that r = sum_{j=0}^{k-1} costs[i_j].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_5 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    ∃ idxs : List Nat,
      idxs.length = k.val.toNat ∧
        idxs.Nodup ∧
        (∀ i ∈ idxs, i < costs.val.length) ∧
        r.val = (idxs.map (fun i => (vals costs).getD i 0)).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), ∃ idxs : List Nat,
      idxs.length = k.val.toNat ∧
        idxs.Nodup ∧
        (∀ i ∈ idxs, i < costs.val.length) ∧
        r.val = (idxs.map (fun i => (vals costs).getD i 0)).sum) := by
  sorry

/-- Let C_0 = {i | 0 <= i < candidates or n-candidates <= i < n}. Let i* be the smallest index in C_0 that minimizes costs[i] over i in C_0. Then the first worker selected by the hiring process is i*. Consequently, whenever total_cost(costs,k,candidates) returns a result r, there exists an integer r_rest such that r = costs[i*] + r_rest, where r_rest is the total cost of the remaining k-1 sessions (and r_rest = 0 when k = 1).
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_6 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    firstHire (vals costs) candidates.val.toNat
        ∈ window candidates.val.toNat (List.range (vals costs).length) ∧
      (∀ i ∈ window candidates.val.toNat (List.range (vals costs).length),
        (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 ≤
            (vals costs).getD i 0 ∧
          ((vals costs).getD i 0 = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 →
            firstHire (vals costs) candidates.val.toNat ≤ i)) ∧
      ∃ r_rest : Int,
        r.val = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 + r_rest ∧
          r_rest = hireTotalFrom (vals costs) candidates.val.toNat (k.val.toNat - 1)
            (removeIdx (List.range (vals costs).length)
              (firstHire (vals costs) candidates.val.toNat)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), firstHire (vals costs) candidates.val.toNat
        ∈ window candidates.val.toNat (List.range (vals costs).length) ∧
      (∀ i ∈ window candidates.val.toNat (List.range (vals costs).length),
        (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 ≤
            (vals costs).getD i 0 ∧
          ((vals costs).getD i 0 = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 →
            firstHire (vals costs) candidates.val.toNat ≤ i)) ∧
      ∃ r_rest : Int,
        r.val = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 + r_rest ∧
          r_rest = hireTotalFrom (vals costs) candidates.val.toNat (k.val.toNat - 1)
            (removeIdx (List.range (vals costs).length)
              (firstHire (vals costs) candidates.val.toNat))) := by
  sorry

/-- Let C_0 = {i | 0 <= i < candidates or n-candidates <= i < n}. Let i* be the smallest index in C_0 that minimizes costs[i] over i in C_0. Whenever total_cost(costs,k,candidates) returns a result r, r = costs[i*].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, 1 <= candidates <= n, and k = 1. All values are i64 integers. -/
theorem spec_7 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hk : k.val = 1)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hk : k.val = 1)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val = (vals costs).getD (firstHire (vals costs) candidates.val.toNat) 0) := by
  sorry

/-- Whenever total_cost(costs,k,candidates) returns a result r, r = sum_{i=0}^{n-1} costs[i].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, 1 <= candidates <= n, and k = n. All values are i64 integers. -/
theorem spec_8 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hk : k.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val = (vals costs).sum := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hk : k.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val = (vals costs).sum) := by
  sorry

/-- Let d_0 <= d_1 <= ... <= d_{n-1} be the entries of costs sorted in nondecreasing order, with multiplicity. Whenever total_cost(costs,k,candidates) returns a result r, r = sum_{j=0}^{k-1} d_j.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, candidates = n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_9 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hc : candidates.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val = ((sortInt (vals costs)).take k.val.toNat).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hc : candidates.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val = ((sortInt (vals costs)).take k.val.toNat).sum) := by
  sorry

/-- Whenever total_cost(costs,k,candidates) returns a result r, r = k * v.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, 1 <= candidates <= n, and there exists an integer v such that costs[i] = v for all 0 <= i < n. All values are i64 integers. -/
theorem spec_10 (costs : Slice Std.I64) (k candidates r : Std.I64) (v : Int)
    (hpre : Pre costs k candidates)
    (hv : ∀ i : Fin costs.val.length, (costs.val.get i).val = v)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r.val = k.val * v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64) (v : Int)
    (hpre : Pre costs k candidates)
    (hv : ∀ i : Fin costs.val.length, (costs.val.get i).val = v)
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r.val = k.val * v) := by
  sorry

/-- Whenever total_cost(costs',k,candidates) returns a result r' and total_cost(costs,k,candidates) returns a result r, r' = r + k*d.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. Let costs' be a slice of i64 with len(costs') = n, and let d be an integer such that costs'[i] = costs[i] + d and 1 <= costs'[i] <= 100000 for every 0 <= i < n. All values are i64 integers. -/
theorem spec_11 (costs costs' : Slice Std.I64) (k candidates r r' : Std.I64) (d : Int)
    (hpre : Pre costs k candidates)
    (hlen : (vals costs').length = (vals costs).length)
    (hd : ∀ i : Nat, i < (vals costs).length → (vals costs').getD i 0 = (vals costs).getD i 0 + d)
    (hbounds : ∀ x ∈ vals costs', 1 ≤ x ∧ x ≤ 100000)
    (h' : Aegis.TotalCost.total_cost costs' k candidates = ok r')
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r'.val = r.val + k.val * d := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (costs costs' : Slice Std.I64) (k candidates r r' : Std.I64) (d : Int)
    (hpre : Pre costs k candidates)
    (hlen : (vals costs').length = (vals costs).length)
    (hd : ∀ i : Nat, i < (vals costs).length → (vals costs').getD i 0 = (vals costs).getD i 0 + d)
    (hbounds : ∀ x ∈ vals costs', 1 ≤ x ∧ x ≤ 100000)
    (h' : Aegis.TotalCost.total_cost costs' k candidates = ok r')
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r'.val = r.val + k.val * d) := by
  sorry

/-- Whenever total_cost(costs',k,candidates) returns a result r' and total_cost(costs,k,candidates) returns a result r, r' = p*r.
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, and 1 <= candidates <= n. Let costs' be a slice of i64 with len(costs') = n, and let p >= 1 be an integer such that costs'[i] = p * costs[i] and 1 <= costs'[i] <= 100000 for every 0 <= i < n. All values are i64 integers. -/
theorem spec_12 (costs costs' : Slice Std.I64) (k candidates r r' : Std.I64) (p : Int)
    (hpre : Pre costs k candidates)
    (hp : 1 ≤ p)
    (hlen : (vals costs').length = (vals costs).length)
    (hmul : ∀ i : Nat, i < (vals costs).length → (vals costs').getD i 0 = p * (vals costs).getD i 0)
    (hbounds : ∀ x ∈ vals costs', 1 ≤ x ∧ x ≤ 100000)
    (h' : Aegis.TotalCost.total_cost costs' k candidates = ok r')
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    r'.val = p * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (costs costs' : Slice Std.I64) (k candidates r r' : Std.I64) (p : Int)
    (hpre : Pre costs k candidates)
    (hp : 1 ≤ p)
    (hlen : (vals costs').length = (vals costs).length)
    (hmul : ∀ i : Nat, i < (vals costs).length → (vals costs').getD i 0 = p * (vals costs).getD i 0)
    (hbounds : ∀ x ∈ vals costs', 1 ≤ x ∧ x ≤ 100000)
    (h' : Aegis.TotalCost.total_cost costs' k candidates = ok r')
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), r'.val = p * r.val) := by
  sorry

/-- Sort the indices 0,...,n-1 by the key (costs[i],i) in increasing lexicographic order, obtaining i_0,...,i_{n-1}. Then the sequence of workers hired in the k sessions is exactly i_0,...,i_{k-1}; in particular, whenever total_cost(costs,k,candidates) returns a result r, r = sum_{j=0}^{k-1} costs[i_j].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, candidates = n, and 1 <= candidates <= n. All values are i64 integers. -/
theorem spec_13 (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hc : candidates.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r) :
    hiredSeq (vals costs) candidates.val.toNat k.val.toNat =
        (sortedIndices (vals costs)).take k.val.toNat ∧
      r.val =
        (((sortedIndices (vals costs)).take k.val.toNat).map
          (fun i => (vals costs).getD i 0)).sum := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (costs : Slice Std.I64) (k candidates r : Std.I64)
    (hpre : Pre costs k candidates)
    (hc : candidates.val = (costs.val.length : Int))
    (h : Aegis.TotalCost.total_cost costs k candidates = ok r), hiredSeq (vals costs) candidates.val.toNat k.val.toNat =
        (sortedIndices (vals costs)).take k.val.toNat ∧
      r.val =
        (((sortedIndices (vals costs)).take k.val.toNat).map
          (fun i => (vals costs).getD i 0)).sum) := by
  sorry

/-- Run the hiring process for k+1 sessions using the same rule. Let w be the worker selected in session k (0-based, the last of these k+1 sessions). Whenever total_cost(costs,k+1,candidates) returns a result r_{k+1} and total_cost(costs,k,candidates) returns a result r_k, r_{k+1} = r_k + costs[w].
  Preconditions: Let n = len(costs). Assume n >= 1, n <= 100000, 1 <= costs[i] <= 100000 for every i with 0 <= i < n, 1 <= k <= n, 1 <= candidates <= n, and k + 1 <= n. All values are i64 integers. -/
theorem spec_14 (costs : Slice Std.I64) (k k1 candidates rk rk1 : Std.I64)
    (hpre : Pre costs k candidates)
    (hk1 : k1.val = k.val + 1)
    (hk : k.val + 1 ≤ (costs.val.length : Int))
    (h1 : Aegis.TotalCost.total_cost costs k1 candidates = ok rk1)
    (h0 : Aegis.TotalCost.total_cost costs k candidates = ok rk) :
    rk1.val = rk.val +
      (vals costs).getD
        (hireAt (vals costs) candidates.val.toNat (k.val.toNat + 1) k.val.toNat) 0 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (costs : Slice Std.I64) (k k1 candidates rk rk1 : Std.I64)
    (hpre : Pre costs k candidates)
    (hk1 : k1.val = k.val + 1)
    (hk : k.val + 1 ≤ (costs.val.length : Int))
    (h1 : Aegis.TotalCost.total_cost costs k1 candidates = ok rk1)
    (h0 : Aegis.TotalCost.total_cost costs k candidates = ok rk), rk1.val = rk.val +
      (vals costs).getD
        (hireAt (vals costs) candidates.val.toNat (k.val.toNat + 1) k.val.toNat) 0) := by
  sorry

end AegisSpec.TotalCost
