import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `parallel-courses-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumTime

namespace AegisSpec.MinimumTime

def timeList (time : Slice I64) : List Int := time.val.map (fun x => x.val)

def relList (relations : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  relations.val.map (fun r => r.val.map (fun x => x.val))

def timeAt (time : List Int) (c : Int) : Int := time.getD (c - 1).toNat 0

def courses (n : Int) : List Int := (List.range n.toNat).map (fun i => (i : Int) + 1)

def maxOf : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr max x

def coursesMax (n : Int) (D : Int → Int) : Int := maxOf ((courses n).map D)

def IsEdge (relations : List (List Int)) (u v : Int) : Prop := [u, v] ∈ relations

def PathEdges (relations : List (List Int)) : List Int → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => IsEdge relations u v ∧ PathEdges relations (v :: rest)

def IsDirectedPath (n : Int) (relations : List (List Int)) (p : List Int) : Prop :=
  p ≠ [] ∧ (∀ v ∈ p, 1 ≤ v ∧ v ≤ n) ∧ PathEdges relations p

def pathWeight (time : List Int) (p : List Int) : Int := (p.map (timeAt time)).sum

def IsDirectedCycle (relations : List (List Int)) (p : List Int) : Prop :=
  2 ≤ p.length ∧ p.head? = p.getLast? ∧ PathEdges relations p

def Acyclic (relations : List (List Int)) : Prop := ∀ p, ¬ IsDirectedCycle relations p

def IsMaxPathWeight (n : Int) (relations : List (List Int)) (time : List Int)
    (M : Int) : Prop :=
  (∃ p, IsDirectedPath n relations p ∧ pathWeight time p = M) ∧
    ∀ p, IsDirectedPath n relations p → pathWeight time p ≤ M

def IsMaxEndingWeight (n : Int) (relations : List (List Int)) (time : List Int)
    (c D : Int) : Prop :=
  (∃ p, IsDirectedPath n relations p ∧ p.getLast? = some c ∧ pathWeight time p = D) ∧
    ∀ p, IsDirectedPath n relations p → p.getLast? = some c → pathWeight time p ≤ D

def predsOf (relations : List (List Int)) (c : Int) : List Int :=
  relations.filterMap fun r =>
    match r with
    | [u, v] => if v = c then some u else none
    | _ => none

def predMax (relations : List (List Int)) (D : Int → Int) (c : Int) : Int :=
  max (0 : Int) (maxOf ((predsOf relations c).map D))

def ValidInput (n : Int) (relations : List (List Int)) (time : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 50000 ∧
  time.length = n.toNat ∧
  (∀ t ∈ time, 1 ≤ t ∧ t ≤ 10000) ∧
  (∀ r ∈ relations, ∃ a b : Int,
    r = [a, b] ∧ 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ a ≠ b) ∧
  relations.Nodup ∧
  (relations.length : Int) ≤ min (n * (n - 1) / 2) 50000 ∧
  Acyclic relations

def ValidInputNoRelations (n : Int) (relations : List (List Int)) (time : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 50000 ∧
  time.length = n.toNat ∧
  (∀ t ∈ time, 1 ≤ t ∧ t ≤ 10000) ∧
  relations.length = 0 ∧
  relations.Nodup ∧
  Acyclic relations

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, `r` equals the maximum weight over all directed paths. A directed path is a sequence `(v_0, ..., v_k)` with `k >= 0`, each `v_i` in `{1,...,n}`, such that for every `i` with `0 <= i < k` the pair `[v_i, v_{i+1}]` occurs in `relations` (i.e., equals `relations[j]` for some `j`). Its weight is `sum_{i=0}^k time[v_i - 1]`. The maximum is well-defined because there is at least one directed path (the one-course path `(c)` for any `c`) and the graph is finite and acyclic.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_1 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    IsMaxPathWeight n.val (relList relations) (timeList time) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), IsMaxPathWeight n.val (relList relations) (timeList time) r.val) := by
  sorry

/-- The call `minimum_time(n, relations, time)` returns a result `r` (it does not fail).
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_2 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time)) :
    ∃ r : I64, minimum_time n relations time = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time)), ∃ r : I64, minimum_time n relations time = ok r) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, for every course `c` with `1 <= c <= n`, `r >= time[c-1]`. Equivalently, `r >= max_{0 <= i < n} time[i]`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_3 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    (∀ c : Int, 1 ≤ c → c ≤ n.val → timeAt (timeList time) c ≤ r.val) ∧
      maxOf (timeList time) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), (∀ c : Int, 1 ≤ c → c ≤ n.val → timeAt (timeList time) c ≤ r.val) ∧
      maxOf (timeList time) ≤ r.val) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, `r <= sum_{i=0}^{n-1} time[i]`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_4 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    r.val ≤ (timeList time).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), r.val ≤ (timeList time).sum) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, there exists a directed path `P = (v_0,...,v_k)` with `k >= 0`, each `v_i` in `1..n`, and each consecutive pair occurring in `relations`, whose weight `sum_{i=0}^k time[v_i-1]` is exactly `r`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_5 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    ∃ p : List Int, IsDirectedPath n.val (relList relations) p ∧
      pathWeight (timeList time) p = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), ∃ p : List Int, IsDirectedPath n.val (relList relations) p ∧
      pathWeight (timeList time) p = r.val) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, for every pair `[u,v]` that occurs in `relations`, `r >= time[u-1] + time[v-1]`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_6 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    ∀ u v : Int, IsEdge (relList relations) u v →
      timeAt (timeList time) u + timeAt (timeList time) v ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), ∀ u v : Int, IsEdge (relList relations) u v →
      timeAt (timeList time) u + timeAt (timeList time) v ≤ r.val) := by
  sorry

/-- For each course `c` with `1 <= c <= n`, let `D(c)` be the maximum weight of a directed path ending at `c` (the one-course path `(c)` is allowed). Whenever `minimum_time(n, relations, time)` returns a result `r`, (i) `r = max_{1 <= c <= n} D(c)`, and (ii) for every course `c`, `D(c) = time[c-1] + max(0, max{D(u) : [u,c] occurs in relations})`, where the maximum over an empty set of predecessors is defined to be `0`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_7 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (D : Int → Int)
    (hD : ∀ c : Int, 1 ≤ c → c ≤ n.val →
      IsMaxEndingWeight n.val (relList relations) (timeList time) c (D c))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    r.val = coursesMax n.val D ∧
      ∀ c : Int, 1 ≤ c → c ≤ n.val →
        D c = timeAt (timeList time) c + predMax (relList relations) D c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (D : Int → Int)
    (hD : ∀ c : Int, 1 ≤ c → c ≤ n.val →
      IsMaxEndingWeight n.val (relList relations) (timeList time) c (D c))
    (r : I64) (hres : minimum_time n relations time = ok r), r.val = coursesMax n.val D ∧
      ∀ c : Int, 1 ≤ c → c ≤ n.val →
        D c = timeAt (timeList time) c + predMax (relList relations) D c) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, `r = max_{0 <= i < n} time[i]`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; `len(relations) = 0`; all entries of `relations` are distinct pairs; and the directed graph on vertices `1..n` with edges given by `relations` is acyclic. -/
theorem spec_8 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInputNoRelations n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    r.val = maxOf (timeList time) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInputNoRelations n.val (relList relations) (timeList time))
    (r : I64) (hres : minimum_time n relations time = ok r), r.val = maxOf (timeList time)) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, `r = sum_{i=0}^{n-1} time[i]`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `len(time) = n`; for every `i` with `0 <= i < n`, `1 <= time[i] <= 10000`; every entry of `relations` is a pair `[a,b]` with `1 <= a,b <= n`, `a != b`; all such pairs are distinct; `len(relations) <= min(n*(n-1)/2, 50000)`; the directed graph on vertices `1..n` with edges given by `relations` is acyclic; and there exists a directed path that contains every course `1..n` exactly once (a Hamiltonian directed path). -/
theorem spec_9 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hham : ∃ p : List Int, IsDirectedPath n.val (relList relations) p ∧
      p.Perm (courses n.val))
    (r : I64) (hres : minimum_time n relations time = ok r) :
    r.val = (timeList time).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hham : ∃ p : List Int, IsDirectedPath n.val (relList relations) p ∧
      p.Perm (courses n.val))
    (r : I64) (hres : minimum_time n relations time = ok r), r.val = (timeList time).sum) := by
  sorry

/-- If `minimum_time(n, relations, time1)` returns `r1` and `minimum_time(n, relations, time2)` returns `r2`, then `r1 >= r2`.
  Preconditions: Let `time1` and `time2` be two arrays such that `(n, relations, time1)` and `(n, relations, time2)` both satisfy the problem constraints, and `time1[i] >= time2[i]` for every `0 <= i < n`. -/
theorem spec_10 (n : I64) (relations : Slice (alloc.vec.Vec I64))
    (time1 time2 : Slice I64)
    (hvalid1 : ValidInput n.val (relList relations) (timeList time1))
    (hvalid2 : ValidInput n.val (relList relations) (timeList time2))
    (hle : ∀ c : Int, 1 ≤ c → c ≤ n.val →
      timeAt (timeList time2) c ≤ timeAt (timeList time1) c)
    (r1 : I64) (hres1 : minimum_time n relations time1 = ok r1)
    (r2 : I64) (hres2 : minimum_time n relations time2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64))
    (time1 time2 : Slice I64)
    (hvalid1 : ValidInput n.val (relList relations) (timeList time1))
    (hvalid2 : ValidInput n.val (relList relations) (timeList time2))
    (hle : ∀ c : Int, 1 ≤ c → c ≤ n.val →
      timeAt (timeList time2) c ≤ timeAt (timeList time1) c)
    (r1 : I64) (hres1 : minimum_time n relations time1 = ok r1)
    (r2 : I64) (hres2 : minimum_time n relations time2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- If `minimum_time(n, relations, time)` returns `r` and `minimum_time(n, relations', time)` returns `r'`, then `r = r'`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `time` has length `n` with entries in `1..10000`; `relations` satisfies the problem constraints; and `relations'` is a permutation of the list `relations` (same length and same multiset of pairs) such that `(n, relations', time)` also satisfies the problem constraints. -/
theorem spec_11 (n : I64) (relations relations' : Slice (alloc.vec.Vec I64))
    (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hvalid' : ValidInput n.val (relList relations') (timeList time))
    (hperm : (relList relations').Perm (relList relations))
    (r : I64) (hres : minimum_time n relations time = ok r)
    (r' : I64) (hres' : minimum_time n relations' time = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (relations relations' : Slice (alloc.vec.Vec I64))
    (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hvalid' : ValidInput n.val (relList relations') (timeList time))
    (hperm : (relList relations').Perm (relList relations))
    (r : I64) (hres : minimum_time n relations time = ok r)
    (r' : I64) (hres' : minimum_time n relations' time = ok r'), r = r') := by
  sorry

/-- If `minimum_time(n, relations, time)` returns `r` and `minimum_time(n, relations', time)` returns `r'`, then `r' >= r`.
  Preconditions: `n` is an integer with `1 <= n <= 50000`; `time` has length `n` with entries in `1..10000`; `relations` and `relations'` are two prerequisite lists for the same `n` and `time`, both satisfying the problem constraints, and every pair occurring in `relations` also occurs in `relations'`. -/
theorem spec_12 (n : I64) (relations relations' : Slice (alloc.vec.Vec I64))
    (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hvalid' : ValidInput n.val (relList relations') (timeList time))
    (hsub : ∀ e ∈ relList relations, e ∈ relList relations')
    (r : I64) (hres : minimum_time n relations time = ok r)
    (r' : I64) (hres' : minimum_time n relations' time = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (relations relations' : Slice (alloc.vec.Vec I64))
    (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hvalid' : ValidInput n.val (relList relations') (timeList time))
    (hsub : ∀ e ∈ relList relations, e ∈ relList relations')
    (r : I64) (hres : minimum_time n relations time = ok r)
    (r' : I64) (hres' : minimum_time n relations' time = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever `minimum_time(n, relations, time)` returns a result `r`, `r = max( max_{0 <= i < n} time[i], time[u-1] + time[v-1] )`.
  Preconditions: The input satisfies the problem constraints, `n > 2`, `len(relations) = 1`, and the unique relation is `[u,v]`. -/
theorem spec_13 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hn : 2 < n.val)
    (u v : Int) (hlen : (relList relations).length = 1)
    (huv : [u, v] ∈ relList relations)
    (r : I64) (hres : minimum_time n relations time = ok r) :
    r.val = max (maxOf (timeList time))
      (timeAt (timeList time) u + timeAt (timeList time) v) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (time : Slice I64)
    (hvalid : ValidInput n.val (relList relations) (timeList time))
    (hn : 2 < n.val)
    (u v : Int) (hlen : (relList relations).length = 1)
    (huv : [u, v] ∈ relList relations)
    (r : I64) (hres : minimum_time n relations time = ok r), r.val = max (maxOf (timeList time))
      (timeAt (timeList time) u + timeAt (timeList time) v)) := by
  sorry

end AegisSpec.MinimumTime
