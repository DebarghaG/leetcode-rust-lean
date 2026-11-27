import Aegis.NetworkDelayTime.Code.Funs

/-!
# Specifications of `Aegis.NetworkDelayTime.network_delay_time`

LeetCode problem `network-delay-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NetworkDelayTime

structure Edge where
  src : Int
  tgt : Int
  weight : Int
  deriving DecidableEq, Repr

def edgeOfRow (row : alloc.vec.Vec Std.I64) : Edge :=
  match row.val with
  | [u, v, w] => ⟨u.val, v.val, w.val⟩
  | _ => ⟨0, 0, 0⟩

def rows (times : Slice (alloc.vec.Vec Std.I64)) : List Edge :=
  times.val.map edgeOfRow

inductive Walk (E : List Edge) : Int → Int → Int → Prop where
  | nil (a : Int) : Walk E a a 0
  | step {a b c w w' : Int} :
      (∃ e ∈ E, e.src = a ∧ e.tgt = b ∧ e.weight = w) →
      Walk E b c w' → Walk E a c (w + w')

def Reach (E : List Edge) (a b : Int) : Prop :=
  ∃ w : Int, Walk E a b w

def IsShortest (E : List Edge) (a b w : Int) : Prop :=
  Walk E a b w ∧ ∀ w' : Int, Walk E a b w' → w ≤ w'

def AllDistsDefined (E : List Edge) (k n : Int) : Prop :=
  ∀ v : Int, 1 ≤ v → v ≤ n → ∃ w : Int, IsShortest E k v w

def IsMaxDist (E : List Edge) (k n r : Int) : Prop :=
  (∀ v : Int, 1 ≤ v → v ≤ n → ∃ w : Int, IsShortest E k v w ∧ w ≤ r) ∧
  (∃ v : Int, 1 ≤ v ∧ v ≤ n ∧ IsShortest E k v r)

def AllPathsAbove (E : List Edge) (k v T : Int) : Prop :=
  ∀ w : Int, Walk E k v w → T < w

def ValidInput (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64) : Prop :=
  1 ≤ k.val ∧ k.val ≤ n.val ∧ n.val ≤ 100 ∧
  1 ≤ (times.val.length : Int) ∧ (times.val.length : Int) ≤ 6000 ∧
  (∀ (i : Nat) (hi : i < times.val.length),
    ∃ u v w : Std.I64,
      (times.val.get ⟨i, hi⟩).val = [u, v, w] ∧
      1 ≤ u.val ∧ u.val ≤ n.val ∧ 1 ≤ v.val ∧ v.val ≤ n.val ∧
      u.val ≠ v.val ∧ 0 ≤ w.val ∧ w.val ≤ 100) ∧
  (rows times).Pairwise (fun e₁ e₂ => ¬ (e₁.src = e₂.src ∧ e₁.tgt = e₂.tgt))

/-- Define, for any nodes a,b in {1,...,n}, d(a,b) to be the least value of the sum of weights over all finite sequences of edges e_1,...,e_m from times (m >= 0) such that e_1.source = a, e_m.target = b, and e_j.target = e_{j+1}.source for 1 <= j < m; when m=0 this sequence is allowed only if a=b and its sum is 0. If no such sequence exists, d(a,b) is undefined. The function returns a result r and: if d(k,v) is defined for every v in {1,...,n}, then r = max_{1 <= v <= n} d(k,v); otherwise r = -1.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_1
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (AllDistsDefined (rows times) k.val n.val →
        IsMaxDist (rows times) k.val n.val r.val) ∧
      (¬ AllDistsDefined (rows times) k.val n.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (AllDistsDefined (rows times) k.val n.val →
        IsMaxDist (rows times) k.val n.val r.val) ∧
      (¬ AllDistsDefined (rows times) k.val n.val → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_2
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r) := by
  sorry

/-- The function returns a result r and either r = -1 or 0 <= r <= 100*(n-1).
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_3
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = -1 ∨ 0 ≤ r.val ∧ r.val ≤ 100 * (n.val - 1)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = -1 ∨ 0 ≤ r.val ∧ r.val ≤ 100 * (n.val - 1))) := by
  sorry

/-- Let reach(a,b) mean that there exists a finite sequence of edges from times forming a directed path from a to b; reach(a,a) is true via the empty path. The function returns a result r and r = -1 if and only if there exists v in {1,...,n} such that reach(k,v) is false.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_4
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = -1 ↔
        ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ ¬ Reach (rows times) k.val v) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = -1 ↔
        ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ ¬ Reach (rows times) k.val v)) := by
  sorry

/-- The function returns a result r and if r != -1 then for every v in {1,...,n} there exists a finite sequence of edges from times forming a directed path from k to v whose total weight is at most r.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_5
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∀ v : Int, 1 ≤ v → v ≤ n.val →
          ∃ w : Int, Walk (rows times) k.val v w ∧ w ≤ r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∀ v : Int, 1 ≤ v → v ≤ n.val →
          ∃ w : Int, Walk (rows times) k.val v w ∧ w ≤ r.val)) := by
  sorry

/-- Let d(a,b) be the shortest-path distance from a to b using edges in times, defined as the minimum total weight of a directed path from a to b (empty path for a=b), or +infinity if no path exists. The function returns a result r and if r != -1 then there exists a node v in {1,...,n} with d(k,v) = r.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_6
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ IsShortest (rows times) k.val v r.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ IsShortest (rows times) k.val v r.val)) := by
  sorry

/-- The function returns a result r and if r != -1 then for every integer T with 0 <= T < r there exists a node v in {1,...,n} such that every directed path from k to v using edges in times has total weight strictly greater than T; equivalently, not all nodes can be reached from k within time T.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_7
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∀ T : Int, 0 ≤ T → T < r.val →
          ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ AllPathsAbove (rows times) k.val v T) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val ≠ -1 →
        ∀ T : Int, 0 ≤ T → T < r.val →
          ∃ v : Int, 1 ≤ v ∧ v ≤ n.val ∧ AllPathsAbove (rows times) k.val v T)) := by
  sorry

/-- The function returns a result r and for every integer T >= 0, if for every v in {1,...,n} there exists a directed path from k to v using edges in times with total weight at most T, then r != -1 and r <= T.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_8
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      ∀ T : Int, 0 ≤ T →
        (∀ v : Int, 1 ≤ v → v ≤ n.val →
          ∃ w : Int, Walk (rows times) k.val v w ∧ w ≤ T) →
        r.val ≠ -1 ∧ r.val ≤ T := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      ∀ T : Int, 0 ≤ T →
        (∀ v : Int, 1 ≤ v → v ≤ n.val →
          ∃ w : Int, Walk (rows times) k.val v w ∧ w ≤ T) →
        r.val ≠ -1 ∧ r.val ≤ T) := by
  sorry

/-- The function returns a result r and if n > 1 and no edge in times has source k, then r = -1.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_9
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (1 < n.val →
        (∀ e ∈ rows times, e.src ≠ k.val) →
        r.val = -1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (1 < n.val →
        (∀ e ∈ rows times, e.src ≠ k.val) →
        r.val = -1)) := by
  sorry

/-- For every slice times' that is a permutation of times (same length and same multiset of triples), if r = network_delay_time(times, n, k) and r' = network_delay_time(times', n, k), then r = r'.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_10
    (times times' : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k)
    (hperm : times'.val.Perm times.val) :
    ∀ r r' : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r →
      Aegis.NetworkDelayTime.network_delay_time times' n k = ok r' →
      r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (times times' : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k)
    (hperm : times'.val.Perm times.val), ∀ r r' : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r →
      Aegis.NetworkDelayTime.network_delay_time times' n k = ok r' →
      r = r') := by
  sorry

/-- The function returns a result r and r = 0 if and only if every node v in {1,...,n} is reachable from k by a directed path using edges in times whose total weight is 0.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_11
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = 0 ↔
        ∀ v : Int, 1 ≤ v → v ≤ n.val → Walk (rows times) k.val v 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      (r.val = 0 ↔
        ∀ v : Int, 1 ≤ v → v ≤ n.val → Walk (rows times) k.val v 0)) := by
  sorry

/-- The function returns a result r and for every triple e = [u,v,w] with 1 <= u,v <= n, u != v, 0 <= w <= 100, (u,v) not among the ordered pairs of times, and len(times) < 6000, let times' be the slice obtained by appending e to times and let r' be the result of network_delay_time(times', n, k). Then r != -1 implies r' != -1 and r' <= r.
  Preconditions: n and k denote the integer values of the corresponding arguments; 1 <= k <= n <= 100; len(times) is an integer with 1 <= len(times) <= 6000; for every i with 0 <= i < len(times), the Vec times[i] has length 3 and, writing times[i] = [u_i, v_i, w_i], we have 1 <= u_i, v_i <= n, u_i != v_i, and 0 <= w_i <= 100; all ordered pairs (u_i, v_i) are pairwise distinct. -/
theorem spec_12
    (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k) :
    ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      ∀ (row : alloc.vec.Vec Std.I64) (u v w : Std.I64),
        row.val = [u, v, w] →
        1 ≤ u.val → u.val ≤ n.val →
        1 ≤ v.val → v.val ≤ n.val →
        u.val ≠ v.val → 0 ≤ w.val → w.val ≤ 100 →
        (∀ e ∈ rows times, ¬ (e.src = u.val ∧ e.tgt = v.val)) →
        (times.val.length : Int) < 6000 →
        ∀ (times' : Slice (alloc.vec.Vec Std.I64)),
          times'.val = times.val ++ [row] →
          ∀ r' : Std.I64,
            Aegis.NetworkDelayTime.network_delay_time times' n k = ok r' →
            r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (times : Slice (alloc.vec.Vec Std.I64)) (n k : Std.I64)
    (hpre : ValidInput times n k), ∃ r : Std.I64,
      Aegis.NetworkDelayTime.network_delay_time times n k = ok r ∧
      ∀ (row : alloc.vec.Vec Std.I64) (u v w : Std.I64),
        row.val = [u, v, w] →
        1 ≤ u.val → u.val ≤ n.val →
        1 ≤ v.val → v.val ≤ n.val →
        u.val ≠ v.val → 0 ≤ w.val → w.val ≤ 100 →
        (∀ e ∈ rows times, ¬ (e.src = u.val ∧ e.tgt = v.val)) →
        (times.val.length : Int) < 6000 →
        ∀ (times' : Slice (alloc.vec.Vec Std.I64)),
          times'.val = times.val ++ [row] →
          ∀ r' : Std.I64,
            Aegis.NetworkDelayTime.network_delay_time times' n k = ok r' →
            r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
  sorry

end AegisSpec.NetworkDelayTime
