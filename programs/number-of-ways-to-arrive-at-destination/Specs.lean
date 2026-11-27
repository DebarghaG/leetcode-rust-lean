import Aegis.CountPaths.Code.Funs

/-!
# Specifications of `Aegis.CountPaths.count_paths`

LeetCode problem `number-of-ways-to-arrive-at-destination`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

noncomputable section

namespace AegisSpec.CountPaths

open Aegis.CountPaths (count_paths)

def roadU (r : alloc.vec.Vec Std.I64) : ℤ :=
  match r.val with
  | [] => 0
  | a :: _ => a.val

def roadV (r : alloc.vec.Vec Std.I64) : ℤ :=
  match r.val with
  | [] => 0
  | [_] => 0
  | _ :: b :: _ => b.val

def roadT (r : alloc.vec.Vec Std.I64) : ℤ :=
  match r.val with
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | _ :: _ :: c :: _ => c.val

def roadKey (r : alloc.vec.Vec Std.I64) : ℤ × ℤ :=
  (min (roadU r) (roadV r), max (roadU r) (roadV r))

def MOD : ℤ := 1000000007

@[reducible] def Joins (r : alloc.vec.Vec Std.I64) (a b : ℤ) : Prop :=
  (roadU r = a ∧ roadV r = b) ∨ (roadU r = b ∧ roadV r = a)

def Adj (rs : List (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  ∃ r ∈ rs, Joins r a b

def AdjUnique (rs : List (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  ∃! r, r ∈ rs ∧ Joins r a b

def GraphConnected (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) : Prop :=
  ∀ a b : ℤ, 0 ≤ a → a < n → 0 ≤ b → b < n → Relation.ReflTransGen (Adj rs) a b

def numEdges (p : List ℤ) : ℕ := p.length - 1

def IsWalk (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (p : List ℤ) : Prop :=
  p ≠ [] ∧ p.head? = some 0 ∧ p.getLast? = some (n - 1) ∧
    ∀ (j : ℕ) (a b : ℤ), p[j]? = some a → p[j+1]? = some b → Adj rs a b

def IsPath (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (p : List ℤ) : Prop :=
  p ≠ [] ∧ p.head? = some 0 ∧ p.getLast? = some (n - 1) ∧
    ∀ (j : ℕ) (a b : ℤ), p[j]? = some a → p[j+1]? = some b → AdjUnique rs a b

def edgeTime (rs : List (alloc.vec.Vec Std.I64)) (a b : ℤ) : ℤ :=
  match rs.find? (fun r => decide (Joins r a b)) with
  | some r => roadT r
  | none => 0

def pathTime (rs : List (alloc.vec.Vec Std.I64)) : List ℤ → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => edgeTime rs a b + pathTime rs (b :: rest)

def IsMinPathTime (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (D : ℤ) : Prop :=
  (∃ p, IsPath rs n p ∧ pathTime rs p = D) ∧ ∀ p, IsPath rs n p → D ≤ pathTime rs p

def numShortestPaths (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (D : ℤ) : ℕ :=
  Set.ncard {p : List ℤ | IsPath rs n p ∧ pathTime rs p = D}

def IsMinEdgeCount (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (k : ℕ) : Prop :=
  (∃ p, IsWalk rs n p ∧ numEdges p = k) ∧ ∀ p, IsWalk rs n p → k ≤ numEdges p

def numWalksWithEdges (rs : List (alloc.vec.Vec Std.I64)) (n : ℤ) (k : ℕ) : ℕ :=
  Set.ncard {p : List ℤ | IsWalk rs n p ∧ numEdges p = k}

def ValidInput (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 200 ∧
  (n.val - 1 ≤ (roads.val.length : ℤ)) ∧
  ((roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2) ∧
  (∀ r ∈ roads.val, r.val.length = 3) ∧
  (∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val) ∧
  (∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val) ∧
  (∀ r ∈ roads.val, roadU r ≠ roadV r) ∧
  (∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000) ∧
  (roads.val.map roadKey).Nodup ∧
  GraphConnected roads.val n.val

/-- Let MOD = 1000000007. For a finite sequence p = (p_0,...,p_k) with k >= 0, call p a path from 0 to n-1 if p_0 = 0, p_k = n-1, and for every j with 0 <= j < k there is exactly one road index i with {roads[i][0], roads[i][1]} = {p_j, p_{j+1}}; its time is the sum over j of roads[i][2] for that unique i, with the empty sum 0 when k = 0. Let D be the minimum time of such paths (which exists by connectivity), and let N be the number of such paths whose time is D. Then count_paths(n, roads) returns a result r such that 0 <= r < MOD and r is congruent to N modulo MOD (equivalently r = N mod MOD).
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected. -/
theorem spec_1 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val) :
    ∃ (D : ℤ) (N : ℕ) (r : Std.I64),
      IsMinPathTime roads.val n.val D ∧
      numShortestPaths roads.val n.val D = N ∧
      count_paths n roads = Result.ok r ∧
      0 ≤ r.val ∧ r.val < MOD ∧ r.val % MOD = (N : ℤ) % MOD := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val), ∃ (D : ℤ) (N : ℕ) (r : Std.I64),
      IsMinPathTime roads.val n.val D ∧
      numShortestPaths roads.val n.val D = N ∧
      count_paths n roads = Result.ok r ∧
      0 ≤ r.val ∧ r.val < MOD ∧ r.val % MOD = (N : ℤ) % MOD) := by
  sorry

/-- For every input satisfying the preconditions, count_paths(n, roads) does not fail: there exists an i64 r with count_paths(n, roads) = Result.ok r. No i64 overflow, out-of-bounds indexing, or panic occurs.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected. -/
theorem spec_2 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val) :
    ∃ r : Std.I64, count_paths n roads = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val), ∃ r : Std.I64, count_paths n roads = Result.ok r) := by
  sorry

/-- Whenever count_paths(n, roads) returns Result.ok r, the value r satisfies 0 <= r < 1000000007.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected. -/
theorem spec_3 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (r : Std.I64) (hr : count_paths n roads = Result.ok r) :
    0 ≤ r.val ∧ r.val < MOD := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (r : Std.I64) (hr : count_paths n roads = Result.ok r), 0 ≤ r.val ∧ r.val < MOD) := by
  sorry

/-- count_paths(n, roads) returns Result.ok 1.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected; and len(roads) = n - 1. -/
theorem spec_4 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hlen : (roads.val.length : ℤ) = n.val - 1) :
    count_paths n roads = Result.ok (1#i64) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hlen : (roads.val.length : ℤ) = n.val - 1), count_paths n roads = Result.ok (1#i64)) := by
  sorry

/-- Let N be the number of shortest paths from 0 to n-1, counted as in spec_1. If N < 1000000007, then count_paths(n, roads) returns Result.ok N.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected. -/
theorem spec_5 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (D : ℤ) (N : ℕ)
    (hD : IsMinPathTime roads.val n.val D)
    (hN : numShortestPaths roads.val n.val D = N)
    (hsmall : N < 1000000007) :
    ∃ r : Std.I64, count_paths n roads = Result.ok r ∧ r.val = (N : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (D : ℤ) (N : ℕ)
    (hD : IsMinPathTime roads.val n.val D)
    (hN : numShortestPaths roads.val n.val D = N)
    (hsmall : N < 1000000007), ∃ r : Std.I64, count_paths n roads = Result.ok r ∧ r.val = (N : ℤ)) := by
  sorry

/-- If count_paths(n, roads) returns Result.ok r and count_paths(n, roads') returns Result.ok r', then r = r'.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected. Let roads' be the slice obtained from roads by replacing every triple [u_i, v_i, t_i] with [v_i, u_i, t_i], keeping the same order; then (n, roads') also satisfies the valid-input constraints. -/
theorem spec_6 (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hswap_len : roads'.val.length = roads.val.length)
    (hswap : ∀ (i : ℕ) (r r' : alloc.vec.Vec Std.I64),
      roads.val[i]? = some r → roads'.val[i]? = some r' →
        roadU r' = roadV r ∧ roadV r' = roadU r ∧ roadT r' = roadT r)
    (hvalid' : ValidInput n roads')
    (r r' : Std.I64)
    (hr : count_paths n roads = Result.ok r)
    (hr' : count_paths n roads' = Result.ok r') :
    r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hswap_len : roads'.val.length = roads.val.length)
    (hswap : ∀ (i : ℕ) (r r' : alloc.vec.Vec Std.I64),
      roads.val[i]? = some r → roads'.val[i]? = some r' →
        roadU r' = roadV r ∧ roadV r' = roadU r ∧ roadT r' = roadT r)
    (hvalid' : ValidInput n roads')
    (r r' : Std.I64)
    (hr : count_paths n roads = Result.ok r)
    (hr' : count_paths n roads' = Result.ok r'), r = r') := by
  sorry

/-- Let k_min be the minimum number of edges in any path from 0 to n-1, where a path is a vertex sequence p_0,...,p_k with p_0 = 0, p_k = n-1 and each consecutive pair joined by a road, and the empty path has 0 edges when n = 1. Let N be the number of such paths with exactly k_min edges. Then count_paths(n, roads) returns Result.ok (N mod 1000000007).
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected; and all roads have the same positive travel time, i.e. if len(roads) > 0 then there is an integer c with 1 <= c <= 1000000000 such that roads[i][2] = c for every i (if len(roads) = 0 the condition is vacuous). -/
theorem spec_7 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hconst : roads.val ≠ [] → ∃ c : ℤ, 1 ≤ c ∧ c ≤ 1000000000 ∧
      ∀ r ∈ roads.val, roadT r = c)
    (k N : ℕ)
    (hk : IsMinEdgeCount roads.val n.val k)
    (hN : numWalksWithEdges roads.val n.val k = N) :
    ∃ r : Std.I64, count_paths n roads = Result.ok r ∧ r.val = (N : ℤ) % MOD := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hconst : roads.val ≠ [] → ∃ c : ℤ, 1 ≤ c ∧ c ≤ 1000000000 ∧
      ∀ r ∈ roads.val, roadT r = c)
    (k N : ℕ)
    (hk : IsMinEdgeCount roads.val n.val k)
    (hN : numWalksWithEdges roads.val n.val k = N), ∃ r : Std.I64, count_paths n roads = Result.ok r ∧ r.val = (N : ℤ) % MOD) := by
  sorry

/-- Let A be the time of the unique road whose endpoints are {0,1}, B the time of the unique road whose endpoints are {1,2}, and C the time of the unique road whose endpoints are {0,2}. Then count_paths(3, roads) returns Result.ok 2 if C = A + B, and returns Result.ok 1 if C != A + B.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected; and n = 3 and len(roads) = 3. -/
theorem spec_8 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hn : n.val = 3)
    (hlen : roads.val.length = 3)
    (A B C : ℤ)
    (hAB : ∃ r ∈ roads.val, Joins r 0 1 ∧ roadT r = A)
    (hAB_unique : ∀ r ∈ roads.val, Joins r 0 1 → roadT r = A)
    (hBC : ∃ r ∈ roads.val, Joins r 1 2 ∧ roadT r = B)
    (hBC_unique : ∀ r ∈ roads.val, Joins r 1 2 → roadT r = B)
    (hAC : ∃ r ∈ roads.val, Joins r 0 2 ∧ roadT r = C)
    (hAC_unique : ∀ r ∈ roads.val, Joins r 0 2 → roadT r = C) :
    (C = A + B → count_paths n roads = Result.ok (2#i64)) ∧
    (C ≠ A + B → count_paths n roads = Result.ok (1#i64)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hn : n.val = 3)
    (hlen : roads.val.length = 3)
    (A B C : ℤ)
    (hAB : ∃ r ∈ roads.val, Joins r 0 1 ∧ roadT r = A)
    (hAB_unique : ∀ r ∈ roads.val, Joins r 0 1 → roadT r = A)
    (hBC : ∃ r ∈ roads.val, Joins r 1 2 ∧ roadT r = B)
    (hBC_unique : ∀ r ∈ roads.val, Joins r 1 2 → roadT r = B)
    (hAC : ∃ r ∈ roads.val, Joins r 0 2 ∧ roadT r = C)
    (hAC_unique : ∀ r ∈ roads.val, Joins r 0 2 → roadT r = C), (C = A + B → count_paths n roads = Result.ok (2#i64)) ∧
    (C ≠ A + B → count_paths n roads = Result.ok (1#i64))) := by
  sorry

/-- Let N be the number of shortest paths from 0 to n-1, counted as in spec_1. Then N >= 1. Consequently, if count_paths(n, roads) returns Result.ok 0, then N is a positive multiple of 1000000007.
  Preconditions: n is an i64 with 1 <= n <= 200; roads is a slice of i64 vectors with length m satisfying n-1 <= m <= n*(n-1)/2; for every i with 0 <= i < m, roads[i] has length 3, and writing u_i=roads[i][0], v_i=roads[i][1], t_i=roads[i][2], we have 0 <= u_i < n, 0 <= v_i < n, u_i != v_i, and 1 <= t_i <= 1000000000; the unordered pairs {u_i,v_i} are pairwise distinct; and the undirected graph on vertices 0,...,n-1 with edges {u_i,v_i} is connected; and n > 1. -/
theorem spec_9 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hn : 1 < n.val)
    (D : ℤ) (N : ℕ)
    (hD : IsMinPathTime roads.val n.val D)
    (hN : numShortestPaths roads.val n.val D = N) :
    1 ≤ N ∧
      (count_paths n roads = Result.ok (0#i64) →
        ∃ k : ℕ, 1 ≤ k ∧ N = k * 1000000007) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 200)
    (hm_lo : n.val - 1 ≤ (roads.val.length : ℤ))
    (hm_hi : (roads.val.length : ℤ) ≤ n.val * (n.val - 1) / 2)
    (hrow : ∀ r ∈ roads.val, r.val.length = 3)
    (hu : ∀ r ∈ roads.val, 0 ≤ roadU r ∧ roadU r < n.val)
    (hv : ∀ r ∈ roads.val, 0 ≤ roadV r ∧ roadV r < n.val)
    (huv : ∀ r ∈ roads.val, roadU r ≠ roadV r)
    (ht : ∀ r ∈ roads.val, 1 ≤ roadT r ∧ roadT r ≤ 1000000000)
    (hpairs : (roads.val.map roadKey).Nodup)
    (hconn : GraphConnected roads.val n.val)
    (hn : 1 < n.val)
    (D : ℤ) (N : ℕ)
    (hD : IsMinPathTime roads.val n.val D)
    (hN : numShortestPaths roads.val n.val D = N), 1 ≤ N ∧
      (count_paths n roads = Result.ok (0#i64) →
        ∃ k : ℕ, 1 ≤ k ∧ N = k * 1000000007)) := by
  sorry

end AegisSpec.CountPaths
