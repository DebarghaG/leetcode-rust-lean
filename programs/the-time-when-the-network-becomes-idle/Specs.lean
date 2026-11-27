import Aegis.NetworkBecomesIdle.Code.Funs

/-!
# Specifications of `Aegis.NetworkBecomesIdle.network_becomes_idle`

LeetCode problem `the-time-when-the-network-becomes-idle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NetworkBecomesIdle

def entryAt (l : List I64) (i : ℕ) : ℤ := ((l[i]?).map IScalar.val).getD 0

def patienceAt (patience : Slice I64) (i : ℕ) : ℤ := entryAt patience.val i

def edgeAt (edges : Slice (alloc.vec.Vec I64)) (e : ℕ) : alloc.vec.Vec I64 :=
  (edges.val[e]?).getD (alloc.vec.Vec.new I64)

def edgeVert (edges : Slice (alloc.vec.Vec I64)) (e j : ℕ) : ℤ := entryAt (edgeAt edges e).val j

def numVerts (patience : Slice I64) : ℕ := patience.val.length

def numEdges (edges : Slice (alloc.vec.Vec I64)) : ℕ := edges.val.length

def endpoints (e : alloc.vec.Vec I64) : List ℕ := e.val.map (fun x => x.val.toNat)

def Adj (edges : Slice (alloc.vec.Vec I64)) (u v : ℕ) : Prop :=
  ∃ e ∈ edges.val, endpoints e = [u, v] ∨ endpoints e = [v, u]

inductive Walk (edges : Slice (alloc.vec.Vec I64)) : ℕ → ℕ → ℕ → Prop where
  | nil (u : ℕ) : Walk edges 0 u u
  | cons {u v w k : ℕ} : Adj edges u v → Walk edges k v w → Walk edges (k + 1) u w

noncomputable def distToZero (edges : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, Walk edges k i 0 then Nat.find h else 0

def Connected (edges : Slice (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i, i < n → ∃ k, Walk edges k i 0

def PatienceOk (patience : Slice I64) : Prop :=
  2 ≤ numVerts patience ∧
    numVerts patience ≤ 100000 ∧
    patienceAt patience 0 = 0 ∧
    ∀ i, 1 ≤ i → i < numVerts patience →
      1 ≤ patienceAt patience i ∧ patienceAt patience i ≤ 100000

def EdgesOk (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64) : Prop :=
  1 ≤ numEdges edges ∧
    numEdges edges ≤ Nat.min 100000 (numVerts patience * (numVerts patience - 1) / 2) ∧
    (∀ e, e < numEdges edges → (edgeAt edges e).val.length = 2) ∧
    (∀ e, e < numEdges edges →
      (0 : ℤ) ≤ edgeVert edges e 0 ∧ edgeVert edges e 0 < (numVerts patience : ℤ) ∧
        (0 : ℤ) ≤ edgeVert edges e 1 ∧ edgeVert edges e 1 < (numVerts patience : ℤ) ∧
        edgeVert edges e 0 ≠ edgeVert edges e 1) ∧
    ∀ e e', e < numEdges edges → e' < numEdges edges → e ≠ e' →
      ¬(endpoints (edgeAt edges e) = endpoints (edgeAt edges e') ∨
        endpoints (edgeAt edges e) = (endpoints (edgeAt edges e')).reverse)

def WellFormed (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64) : Prop :=
  PatienceOk patience ∧ EdgesOk edges patience ∧ Connected edges (numVerts patience)

noncomputable def idleTime (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (i : ℕ) : ℤ :=
  let d : ℤ := (distToZero edges i : ℤ)
  let p : ℤ := patienceAt patience i
  2 * d + Int.fdiv (2 * d - 1) p * p

noncomputable def maxDist (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64) : ℕ :=
  (Finset.Icc 1 (numVerts patience - 1)).sup (fun i => distToZero edges i)

noncomputable def maxIdleTime (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64) : ℤ := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (numVerts patience - 1)
  exact if h : s.Nonempty then s.sup' h (fun i => idleTime edges patience i) else 0

def EdgeSubset (edges edges' : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ u v, Adj edges u v → Adj edges' u v

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0 in the undirected graph represented by edges; this is well-defined because the graph is connected. For each i with 1 <= i < n define L(i) = 2*d(i) + floor((2*d(i)-1)/patience[i]) * patience[i], where floor is integer division rounding down. The function returns a result r (Result.ok r) and r = 1 + max_{1 <= i < n} L(i).
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_1 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    ∃ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r ∧
      r.val = 1 + maxIdleTime edges patience := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), ∃ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r ∧
      r.val = 1 + maxIdleTime edges patience) := by
  sorry

/-- The function returns a result r and does not fail: it performs no out-of-bounds slice access, no panic, no I64 overflow, and no division by zero. In particular, any divisor patience[i] that may be used satisfies 1 <= i < n, and for those patience[i] >= 1.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_2 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    (∃ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r) ∧
      (∀ i, 1 ≤ i → i < numVerts patience → 1 ≤ patienceAt patience i) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), (∃ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r) ∧
      (∀ i, 1 ≤ i → i < numVerts patience → 1 ≤ patienceAt patience i)) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0, and let D = max_{1 <= i < n} d(i). Whenever the function returns a result r, 3 <= r <= 4*D.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_3 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      3 ≤ r.val ∧ r.val ≤ 4 * (maxDist edges patience : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      3 ≤ r.val ∧ r.val ≤ 4 * (maxDist edges patience : ℤ)) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0, and for each i with 1 <= i < n define L(i) = 2*d(i) + floor((2*d(i)-1)/patience[i]) * patience[i]. Whenever the function returns a result r, there exists an index k with 1 <= k < n such that r = 1 + L(k), and for every j with 1 <= j < n, L(j) <= L(k).
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_4 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      ∃ k, 1 ≤ k ∧ k < numVerts patience ∧ r.val = 1 + idleTime edges patience k ∧
        (∀ j, 1 ≤ j → j < numVerts patience →
          idleTime edges patience j ≤ idleTime edges patience k) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      ∃ k, 1 ≤ k ∧ k < numVerts patience ∧ r.val = 1 + idleTime edges patience k ∧
        (∀ j, 1 ≤ j → j < numVerts patience →
          idleTime edges patience j ≤ idleTime edges patience k)) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0, and for each i with 1 <= i < n define L(i) = 2*d(i) + floor((2*d(i)-1)/patience[i]) * patience[i]. Whenever the function returns a result r, for every i with 1 <= i < n, r >= 1 + L(i).
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_5 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      ∀ i, 1 ≤ i → i < numVerts patience → 1 + idleTime edges patience i ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
      ∀ i, 1 ≤ i → i < numVerts patience → 1 + idleTime edges patience i ≤ r.val) := by
  sorry

/-- If n = 2, then the only edge is {0,1} and the shortest-path distance from 1 to 0 is 1. Whenever the function returns a result r, r = 4 if patience[1] = 1, and r = 3 if patience[1] >= 2.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_6 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    numVerts patience = 2 →
      (Adj edges 0 1 ∧
        (∀ u v, Adj edges u v → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
        distToZero edges 1 = 1) ∧
      (∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        (patienceAt patience 1 = 1 → r.val = 4) ∧
          (2 ≤ patienceAt patience 1 → r.val = 3)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), numVerts patience = 2 →
      (Adj edges 0 1 ∧
        (∀ u v, Adj edges u v → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
        distToZero edges 1 = 1) ∧
      (∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        (patienceAt patience 1 = 1 → r.val = 4) ∧
          (2 ≤ patienceAt patience 1 → r.val = 3))) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0, and let D = max_{1 <= i < n} d(i). If there exists an index k with 1 <= k < n such that d(k) = D and patience[k] = 1, then whenever the function returns a result r, r = 4*D.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_7 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    (∃ k, 1 ≤ k ∧ k < numVerts patience ∧
        distToZero edges k = maxDist edges patience ∧ patienceAt patience k = 1) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        r.val = 4 * (maxDist edges patience : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), (∃ k, 1 ≤ k ∧ k < numVerts patience ∧
        distToZero edges k = maxDist edges patience ∧ patienceAt patience k = 1) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        r.val = 4 * (maxDist edges patience : ℤ)) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0, and let D = max_{1 <= i < n} d(i). If for every i with 1 <= i < n, patience[i] >= 2*d(i), then whenever the function returns a result r, r = 1 + 2*D.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_8 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    (∀ i, 1 ≤ i → i < numVerts patience →
        2 * (distToZero edges i : ℤ) ≤ patienceAt patience i) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        r.val = 1 + 2 * (maxDist edges patience : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), (∀ i, 1 ≤ i → i < numVerts patience →
        2 * (distToZero edges i : ℤ) ≤ patienceAt patience i) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        r.val = 1 + 2 * (maxDist edges patience : ℤ)) := by
  sorry

/-- Let d(i) be the length in edges of a shortest path from vertex i to vertex 0. If d(i) = 1 for every i with 1 <= i < n, then whenever the function returns a result r: r = 4 if there exists i with 1 <= i < n and patience[i] = 1; otherwise r = 3 (equivalently, r = 3 if patience[i] >= 2 for all i with 1 <= i < n).
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_9 (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) :
    (∀ i, 1 ≤ i → i < numVerts patience → distToZero edges i = 1) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        ((∃ i, 1 ≤ i ∧ i < numVerts patience ∧ patienceAt patience i = 1) → r.val = 4) ∧
          ((∀ i, 1 ≤ i → i < numVerts patience → 2 ≤ patienceAt patience i) → r.val = 3) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience), (∀ i, 1 ≤ i → i < numVerts patience → distToZero edges i = 1) →
      ∀ r, Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r →
        ((∃ i, 1 ≤ i ∧ i < numVerts patience ∧ patienceAt patience i = 1) → r.val = 4) ∧
          ((∀ i, 1 ≤ i → i < numVerts patience → 2 ≤ patienceAt patience i) → r.val = 3)) := by
  sorry

/-- Let E be the undirected graph represented by edges. For any other slice edges' of Vec I64 that, together with the same patience, satisfies all the stated problem constraints with the same n, represents an undirected graph E' on vertices 0..n-1, and has E as a subset of E' (every edge of E is an edge of E'), let r = network_becomes_idle(edges, patience) and r' = network_becomes_idle(edges', patience). The calls return results r and r', and r' <= r.
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_10 (edges edges' : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) (hwf' : WellFormed edges' patience)
    (hsub : EdgeSubset edges edges') :
    ∃ r r', Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r ∧
      Aegis.NetworkBecomesIdle.network_becomes_idle edges' patience = ok r' ∧
        r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec I64)) (patience : Slice I64)
    (hwf : WellFormed edges patience) (hwf' : WellFormed edges' patience)
    (hsub : EdgeSubset edges edges'), ∃ r r', Aegis.NetworkBecomesIdle.network_becomes_idle edges patience = ok r ∧
      Aegis.NetworkBecomesIdle.network_becomes_idle edges' patience = ok r' ∧
        r'.val ≤ r.val) := by
  sorry

/-- For any two inputs (edges, patience) and (edges', patience') satisfying the problem constraints with the same n, if for every i with 1 <= i < n the shortest-path distance from i to 0 is the same in the two graphs and patience[i] = patience'[i], then network_becomes_idle(edges, patience) = network_becomes_idle(edges', patience').
  Preconditions: Let n = len(patience) and m = len(edges). The problem constraints hold: 2 <= n <= 100000; patience[0] = 0; for every i with 1 <= i < n, 1 <= patience[i] <= 100000; 1 <= m <= min(100000, n*(n-1)/2); every edges[e] has length 2; for every e with 0 <= e < m, 0 <= edges[e][0] < n, 0 <= edges[e][1] < n, and edges[e][0] != edges[e][1]; no two distinct indices e,e' represent the same unordered pair of endpoints; and the undirected graph on vertices 0..n-1 with an edge between u and v exactly when some edges[e] is [u,v] or [v,u] is connected. -/
theorem spec_11 (edges edges' : Slice (alloc.vec.Vec I64)) (patience patience' : Slice I64)
    (hwf : WellFormed edges patience) (hwf' : WellFormed edges' patience')
    (hn : numVerts patience = numVerts patience')
    (hd : ∀ i, 1 ≤ i → i < numVerts patience → distToZero edges i = distToZero edges' i)
    (hp : ∀ i, 1 ≤ i → i < numVerts patience →
      patienceAt patience i = patienceAt patience' i) :
    Aegis.NetworkBecomesIdle.network_becomes_idle edges patience =
      Aegis.NetworkBecomesIdle.network_becomes_idle edges' patience' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec I64)) (patience patience' : Slice I64)
    (hwf : WellFormed edges patience) (hwf' : WellFormed edges' patience')
    (hn : numVerts patience = numVerts patience')
    (hd : ∀ i, 1 ≤ i → i < numVerts patience → distToZero edges i = distToZero edges' i)
    (hp : ∀ i, 1 ≤ i → i < numVerts patience →
      patienceAt patience i = patienceAt patience' i), Aegis.NetworkBecomesIdle.network_becomes_idle edges patience =
      Aegis.NetworkBecomesIdle.network_becomes_idle edges' patience') := by
  sorry

end AegisSpec.NetworkBecomesIdle
