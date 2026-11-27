import Aegis.CanCompleteCircuit.Code.Funs

/-!
# Specifications of `Aegis.CanCompleteCircuit.can_complete_circuit`

LeetCode problem `gas-station`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanCompleteCircuit

namespace AegisSpec.CanCompleteCircuit

def getI (s : Slice I64) (i : ℕ) : ℤ := ((s.val[i]?).map IScalar.val).getD 0

def prefixSum (s : Slice I64) (n : ℕ) : ℤ := ((List.range n).map (fun i => getI s i)).sum

def D (gas cost : Slice I64) (n s k : ℕ) : ℤ :=
  ((List.range (k + 1)).map
    (fun j => getI gas ((s + j) % n) - getI cost ((s + j) % n))).sum

def feasible (gas cost : Slice I64) (n s : ℕ) : Prop := ∀ k, k < n → 0 ≤ D gas cost n s k

def zmod (a : ℤ) (n : ℕ) : ℕ := (a % (n : ℤ)).toNat

def rotateList (l : List I64) (k : ℕ) : List I64 :=
  List.ofFn (fun i : Fin l.length =>
    l[(i.val + k) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)))

def rotate (s : Slice I64) (k : ℕ) : Slice I64 :=
  let l := rotateList s.val k
  Slice.mk l.length (Aeneas.Data.ListN.ListN.fromList l) (by
    have h1 : l.length = s.val.length := List.length_ofFn
    have h2 : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    rw [h1, h2]
    exact s.bound)

theorem rotate_val_length (s : Slice I64) (k : ℕ) : (rotate s k).val.length = s.val.length := by
  simp [rotate, rotateList, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

theorem rotate_val (s : Slice I64) (k : ℕ) : (rotate s k).val = rotateList s.val k := by
  simp only [rotate, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- Whenever can_complete_circuit(gas, cost) returns a value r, exactly one of the following holds: (a) r = -1 and no s with 0 <= s < n is feasible; (b) 0 <= r < n and r is feasible. In particular, if any feasible start exists, r must be one such start; if none exists, r must be -1.
  Preconditions: Let n = len(gas) = len(cost). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= gas[i] <= 10000 and 0 <= cost[i] <= 10000. All indices are 0-based. For 0 <= s < n and 0 <= k < n, define D_s(k) = sum_{j=0}^{k} (gas[(s+j) mod n] - cost[(s+j) mod n]); call s feasible iff D_s(k) >= 0 for every k with 0 <= k < n. (Intuitively, starting at s with an empty tank and processing stations clockwise, the tank is nonnegative after every edge, including the last edge back to s.) -/
theorem spec_1 (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (r : I64) (hr : can_complete_circuit gas cost = ok r) :
    (r.val = -1 ∧ ∀ s : ℕ, s < gas.val.length → ¬ feasible gas cost gas.val.length s) ∨
      (∃ s : ℕ, s < gas.val.length ∧ (s : ℤ) = r.val ∧
        feasible gas cost gas.val.length s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (r : I64) (hr : can_complete_circuit gas cost = ok r), (r.val = -1 ∧ ∀ s : ℕ, s < gas.val.length → ¬ feasible gas cost gas.val.length s) ∨
      (∃ s : ℕ, s < gas.val.length ∧ (s : ℤ) = r.val ∧
        feasible gas cost gas.val.length s)) := by
  sorry

/-- For every input satisfying the preconditions, can_complete_circuit(gas, cost) returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(gas) = len(cost). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= gas[i] <= 10000 and 0 <= cost[i] <= 10000. All indices are 0-based. For 0 <= s < n and 0 <= k < n, define D_s(k) = sum_{j=0}^{k} (gas[(s+j) mod n] - cost[(s+j) mod n]); call s feasible iff D_s(k) >= 0 for every k with 0 <= k < n. (Intuitively, starting at s with an empty tank and processing stations clockwise, the tank is nonnegative after every edge, including the last edge back to s.) -/
theorem spec_2 (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000) :
    ∃ r : I64, can_complete_circuit gas cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000), ∃ r : I64, can_complete_circuit gas cost = ok r) := by
  sorry

/-- Whenever can_complete_circuit(gas, cost) returns r, r = -1 if and only if sum_{i=0}^{n-1} gas[i] < sum_{i=0}^{n-1} cost[i].
  Preconditions: Let n = len(gas) = len(cost). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= gas[i] <= 10000 and 0 <= cost[i] <= 10000. All indices are 0-based. For 0 <= s < n and 0 <= k < n, define D_s(k) = sum_{j=0}^{k} (gas[(s+j) mod n] - cost[(s+j) mod n]); call s feasible iff D_s(k) >= 0 for every k with 0 <= k < n. (Intuitively, starting at s with an empty tank and processing stations clockwise, the tank is nonnegative after every edge, including the last edge back to s.) -/
theorem spec_3 (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (r : I64) (hr : can_complete_circuit gas cost = ok r) :
    (r.val = -1 ↔
      prefixSum gas gas.val.length < prefixSum cost gas.val.length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (r : I64) (hr : can_complete_circuit gas cost = ok r), (r.val = -1 ↔
      prefixSum gas gas.val.length < prefixSum cost gas.val.length)) := by
  sorry

/-- For any k with 0 <= k < n, let gas_k[i] = gas[(i+k) mod n] and cost_k[i] = cost[(i+k) mod n] for 0 <= i < n. Whenever can_complete_circuit(gas, cost) returns r and can_complete_circuit(gas_k, cost_k) returns r_k, r = -1 if and only if r_k = -1.
  Preconditions: Let n = len(gas) = len(cost). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= gas[i] <= 10000 and 0 <= cost[i] <= 10000. All indices are 0-based. For 0 <= s < n and 0 <= k < n, define D_s(k) = sum_{j=0}^{k} (gas[(s+j) mod n] - cost[(s+j) mod n]); call s feasible iff D_s(k) >= 0 for every k with 0 <= k < n. (Intuitively, starting at s with an empty tank and processing stations clockwise, the tank is nonnegative after every edge, including the last edge back to s.) -/
theorem spec_4 (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (k : ℕ) (hk : k < gas.val.length)
    (r rk : I64)
    (hr : can_complete_circuit gas cost = ok r)
    (hrk : can_complete_circuit (rotate gas k) (rotate cost k) = ok rk) :
    (r.val = -1 ↔ rk.val = -1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (k : ℕ) (hk : k < gas.val.length)
    (r rk : I64)
    (hr : can_complete_circuit gas cost = ok r)
    (hrk : can_complete_circuit (rotate gas k) (rotate cost k) = ok rk), (r.val = -1 ↔ rk.val = -1)) := by
  sorry

/-- For any k with 0 <= k < n, let gas_k and cost_k be as in spec_4. Whenever can_complete_circuit(gas, cost) returns r with r != -1, the index (r - k) mod n, taken in {0,...,n-1}, is a feasible start for (gas_k, cost_k).
  Preconditions: Let n = len(gas) = len(cost). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= gas[i] <= 10000 and 0 <= cost[i] <= 10000. All indices are 0-based. For 0 <= s < n and 0 <= k < n, define D_s(k) = sum_{j=0}^{k} (gas[(s+j) mod n] - cost[(s+j) mod n]); call s feasible iff D_s(k) >= 0 for every k with 0 <= k < n. (Intuitively, starting at s with an empty tank and processing stations clockwise, the tank is nonnegative after every edge, including the last edge back to s.) -/
theorem spec_5 (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (k : ℕ) (hk : k < gas.val.length)
    (r : I64) (hr : can_complete_circuit gas cost = ok r)
    (hne : r.val ≠ -1) :
    feasible (rotate gas k) (rotate cost k) gas.val.length
      (zmod (r.val - (k : ℤ)) gas.val.length) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (gas cost : Slice I64)
    (hlen : gas.val.length = cost.val.length)
    (hpos : 1 ≤ gas.val.length)
    (hbound : gas.val.length ≤ 100000)
    (hgas : ∀ x ∈ gas.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (hcost : ∀ x ∈ cost.val, 0 ≤ x.val ∧ x.val ≤ 10000)
    (k : ℕ) (hk : k < gas.val.length)
    (r : I64) (hr : can_complete_circuit gas cost = ok r)
    (hne : r.val ≠ -1), feasible (rotate gas k) (rotate cost k) gas.val.length
      (zmod (r.val - (k : ℤ)) gas.val.length)) := by
  sorry

end AegisSpec.CanCompleteCircuit
