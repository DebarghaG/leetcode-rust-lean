import Aegis.LongestCycle.Code.Funs

/-!
# Specifications of `Aegis.LongestCycle.longest_cycle`

LeetCode problem `longest-cycle-in-a-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestCycle

  def succ (edges : Slice Std.I64) (i : Nat) : Option Int :=
    (edges.val[i]?).map (fun x => x.val)

  def IsCycle (edges : Slice Std.I64) (k : Nat) (v : Fin k → Nat) : Prop :=
    Function.Injective v ∧
      (∀ j, v j < edges.val.length) ∧
      (∀ j : Fin k,
        succ edges (v j) =
          some ((v ⟨((j : Nat) + 1) % k,
            Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩ : Nat) : Int))

  def HasCycle (edges : Slice Std.I64) (k : Nat) : Prop :=
    ∃ v : Fin k → Nat, IsCycle edges k v

  def vals (edges : Slice Std.I64) : List Int :=
    edges.val.map (fun x => x.val)

  /-- longest_cycle(edges) returns r, where r is characterized as follows. For k >= 1, call a k-cycle a tuple (v_0, ..., v_{k-1}) of pairwise distinct integers such that 0 <= v_j < n for every j and edges[v_j] equals the integer v_{(j+1) mod k} for every j (indices are 0-based; for k = 1 this requires edges[v_0] = v_0). If the graph has no k-cycle for any k >= 1, then r = -1. Otherwise r is the maximum of the set { k | k >= 1 and the graph has a k-cycle }.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_1 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∃ r, Aegis.LongestCycle.longest_cycle edges = ok r ∧
        (((∀ k, 1 ≤ k → ¬ HasCycle edges k) ∧ r.val = -1) ∨
          (1 ≤ r.val ∧ HasCycle edges r.val.toNat ∧
            ∀ k, 1 ≤ k → HasCycle edges k → k ≤ r.val.toNat)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∃ r, Aegis.LongestCycle.longest_cycle edges = ok r ∧
          (((∀ k, 1 ≤ k → ¬ HasCycle edges k) ∧ r.val = -1) ∨
            (1 ≤ r.val ∧ HasCycle edges r.val.toNat ∧
              ∀ k, 1 ≤ k → HasCycle edges k → k ≤ r.val.toNat))) := by
    sorry

  /-- longest_cycle(edges) returns a result; in particular it does not fail by out-of-bounds access, arithmetic overflow, panic, or any other failure.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_2 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∃ r, Aegis.LongestCycle.longest_cycle edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∃ r, Aegis.LongestCycle.longest_cycle edges = ok r) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r, either r = -1 or 2 <= r <= n.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_3 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
        r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (edges.val.length : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
          r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (edges.val.length : Int))) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r, r = -1 if and only if there is no k-cycle for any k >= 1, where a k-cycle is a tuple (v_0, ..., v_{k-1}) of pairwise distinct integers with 0 <= v_j < n and edges[v_j] = v_{(j+1) mod k} for all j.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_4 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
        (r.val = -1 ↔ ∀ k, 1 ≤ k → ¬ HasCycle edges k) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
          (r.val = -1 ↔ ∀ k, 1 ≤ k → ¬ HasCycle edges k)) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r with r >= 1, there exist pairwise distinct nodes v_0, ..., v_{r-1} in [0, n) such that edges[v_j] equals the integer v_{(j+1) mod r} for every j in [0, r).
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_5 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r → 1 ≤ r.val →
        HasCycle edges r.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r → 1 ≤ r.val →
          HasCycle edges r.val.toNat) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r with r >= 1, every k-cycle has k <= r. Here a k-cycle is a tuple (v_0, ..., v_{k-1}) of pairwise distinct integers with 0 <= v_j < n and edges[v_j] = v_{(j+1) mod k} for all j.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_6 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r → 1 ≤ r.val →
        ∀ k, 1 ≤ k → HasCycle edges k → k ≤ r.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r → 1 ≤ r.val →
          ∀ k, 1 ≤ k → HasCycle edges k → k ≤ r.val.toNat) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r, r = n if and only if there exists an n-cycle, i.e. a tuple (v_0, ..., v_{n-1}) containing every integer 0, ..., n-1 exactly once such that edges[v_j] equals the integer v_{(j+1) mod n} for all j.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_7 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
        (r.val = (edges.val.length : Int) ↔ HasCycle edges edges.val.length) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
          (r.val = (edges.val.length : Int) ↔ HasCycle edges edges.val.length)) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r and every node has an outgoing edge (edges[i] != -1 for every i with 0 <= i < n), then r >= 1.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. -/
  theorem spec_8 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
        (∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ -1) → 1 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
          (∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ -1) → 1 ≤ r.val) := by
    sorry

  /-- Let edges' be the slice of length n + 1 with edges'[i] = edges[i] for 0 <= i < n and edges'[n] = -1. Whenever longest_cycle(edges) returns r and longest_cycle(edges') returns r', we have r = r'.
    Preconditions: Let n = len(edges). 2 <= n <= 99999. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and edges[i] != i. Let edges' be the slice of length n + 1 with edges'[i] = edges[i] for 0 <= i < n and edges'[n] = -1. -/
  theorem spec_9 (edges edges' : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 99999)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int))
      (hpre : vals edges' = vals edges ++ [-1]) :
      ∀ r r', Aegis.LongestCycle.longest_cycle edges = ok r →
        Aegis.LongestCycle.longest_cycle edges' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges edges' : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 99999)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int))
        (hpre : vals edges' = vals edges ++ [-1]), ∀ r r', Aegis.LongestCycle.longest_cycle edges = ok r →
          Aegis.LongestCycle.longest_cycle edges' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r and longest_cycle(edges') returns r', we have r' >= r.
    Preconditions: Let n = len(edges) = len(edges') with 2 <= n <= 100000. For every i with 0 <= i < n, each of edges[i] and edges'[i] is either -1 or in [0, n); moreover edges[i] != i and edges'[i] != i. For every i with 0 <= i < n, if edges[i] != -1 then edges'[i] = edges[i]. -/
  theorem spec_10 (edges edges' : Slice Std.I64)
      (hlen : edges'.val.length = edges.val.length)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int))
      (hval' : ∀ i (hi : i < edges'.val.length),
        (edges'.val[i]).val = -1 ∨
          (0 ≤ (edges'.val[i]).val ∧ (edges'.val[i]).val < (edges'.val.length : Int)))
      (hself' : ∀ i (hi : i < edges'.val.length), (edges'.val[i]).val ≠ (i : Int))
      (hext : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val ≠ -1 → (edges'.val[i]).val = (edges.val[i]).val) :
      ∀ r r', Aegis.LongestCycle.longest_cycle edges = ok r →
        Aegis.LongestCycle.longest_cycle edges' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges edges' : Slice Std.I64)
        (hlen : edges'.val.length = edges.val.length)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int))
        (hval' : ∀ i (hi : i < edges'.val.length),
          (edges'.val[i]).val = -1 ∨
            (0 ≤ (edges'.val[i]).val ∧ (edges'.val[i]).val < (edges'.val.length : Int)))
        (hself' : ∀ i (hi : i < edges'.val.length), (edges'.val[i]).val ≠ (i : Int))
        (hext : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val ≠ -1 → (edges'.val[i]).val = (edges.val[i]).val), ∀ r r', Aegis.LongestCycle.longest_cycle edges = ok r →
          Aegis.LongestCycle.longest_cycle edges' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever longest_cycle(edges) returns r and the graph contains at least one directed cycle, r >= 2, where a directed cycle of length k >= 1 is a tuple (v_0, ..., v_{k-1}) of pairwise distinct integers with 0 <= v_j < n and edges[v_j] = v_{(j+1) mod k} for all j.
    Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, either edges[i] = -1 or 0 <= edges[i] < n, and additionally edges[i] != i for every i. -/
  theorem spec_11 (edges : Slice Std.I64)
      (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
      (hval : ∀ i (hi : i < edges.val.length),
        (edges.val[i]).val = -1 ∨
          (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
      (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)) :
      ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
        (∃ k, 1 ≤ k ∧ HasCycle edges k) → 2 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : Slice Std.I64)
        (hlen_lo : 2 ≤ edges.val.length) (hlen_hi : edges.val.length ≤ 100000)
        (hval : ∀ i (hi : i < edges.val.length),
          (edges.val[i]).val = -1 ∨
            (0 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.val.length : Int)))
        (hself : ∀ i (hi : i < edges.val.length), (edges.val[i]).val ≠ (i : Int)), ∀ r, Aegis.LongestCycle.longest_cycle edges = ok r →
          (∃ k, 1 ≤ k ∧ HasCycle edges k) → 2 ≤ r.val) := by
    sorry

  end AegisSpec.LongestCycle
