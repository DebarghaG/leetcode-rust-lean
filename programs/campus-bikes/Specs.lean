import Aegis.AssignBikes.Code.Funs

/-!
# Specifications of `Aegis.AssignBikes.assign_bikes`

LeetCode problem `campus-bikes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.AssignBikes

  open Aegis.AssignBikes

  def pt (s : Slice (alloc.vec.Vec I64)) (i : Nat) : alloc.vec.Vec I64 :=
    s.val.getD i (alloc.vec.Vec.new I64)

  def ptc (v : alloc.vec.Vec I64) (k : Nat) : ℤ := (v.val.getD k 0#i64).val

  def comp (s : Slice (alloc.vec.Vec I64)) (i : Nat) (k : Nat) : ℤ := ptc (pt s i) k

  def ent (r : alloc.vec.Vec I64) (i : Nat) : ℤ := (r.val.getD i 0#i64).val

  def entNat (r : alloc.vec.Vec I64) (i : Nat) : Nat := (ent r i).toNat

  def D (workers bikes : Slice (alloc.vec.Vec I64)) (i j : Nat) : ℤ :=
    |comp workers i 0 - comp bikes j 0| + |comp workers i 1 - comp bikes j 1|

  def keyLt (dist : Nat → Nat → ℤ) (p q : Nat × Nat) : Prop :=
    dist p.1 p.2 < dist q.1 q.2 ∨
      (dist p.1 p.2 = dist q.1 q.2 ∧ (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)))

  instance instDecidableKeyLt (dist : Nat → Nat → ℤ) (p q : Nat × Nat) :
      Decidable (keyLt dist p q) := by
    unfold keyLt
    infer_instance

  def keyLt2 (dist : Nat → Nat → ℤ) (p q : Nat × Nat) : Prop :=
    dist p.1 p.2 < dist q.1 q.2 ∨ (dist p.1 p.2 = dist q.1 q.2 ∧ p.2 < q.2)

  instance instDecidableKeyLt2 (dist : Nat → Nat → ℤ) (p q : Nat × Nat) :
      Decidable (keyLt2 dist p q) := by
    unfold keyLt2
    infer_instance

  def bestOf (dist : Nat → Nat → ℤ) (l : List (Nat × Nat)) : Option (Nat × Nat) :=
    l.foldl
      (fun acc p =>
        match acc with
        | none => some p
        | some q => if keyLt dist p q then some p else some q)
      none

  def allPairs (n m : Nat) : List (Nat × Nat) :=
    (List.range n).flatMap (fun i => (List.range m).map (fun j => (i, j)))

  def greedyAux (dist : Nat → Nat → ℤ) : Nat → List (Nat × Nat) → List (Nat × Nat)
    | 0, _ => []
    | fuel + 1, l =>
      match bestOf dist l with
      | none => []
      | some p =>
        p :: greedyAux dist fuel (l.filter (fun q => decide (q.1 ≠ p.1) && decide (q.2 ≠ p.2)))

  def greedy (dist : Nat → Nat → ℤ) (n m : Nat) : List (Nat × Nat) :=
    greedyAux dist n (allPairs n m)

  def order (workers bikes : Slice (alloc.vec.Vec I64)) : List Nat :=
    (greedy (D workers bikes) workers.val.length bikes.val.length).map (fun p => p.1)

  def before : List Nat → Nat → Nat → Prop
    | [], _, _ => False
    | x :: xs, a, b => (x = a ∧ b ∈ xs) ∨ (x ≠ a ∧ before xs a b)

  instance instDecidableBefore (l : List Nat) (a b : Nat) : Decidable (before l a b) := by
    induction l with
    | nil => exact isFalse (fun h => h)
    | cons x xs ih =>
      show Decidable ((x = a ∧ b ∈ xs) ∨ (x ≠ a ∧ before xs a b))
      infer_instance

  structure Pre (workers bikes : Slice (alloc.vec.Vec I64)) : Prop where

    n_pos : 1 ≤ workers.val.length

    n_le_m : workers.val.length ≤ bikes.val.length

    m_le : bikes.val.length ≤ 1000

    w_len : ∀ i : Nat, i < workers.val.length → (pt workers i).val.length = 2

    b_len : ∀ j : Nat, j < bikes.val.length → (pt bikes j).val.length = 2

    w_bnd : ∀ i k : Nat, i < workers.val.length → k < 2 →
      0 ≤ comp workers i k ∧ comp workers i k ≤ 1000

    b_bnd : ∀ j k : Nat, j < bikes.val.length → k < 2 →
      0 ≤ comp bikes j k ∧ comp bikes j k ≤ 1000

    w_distinct : ∀ i i' : Nat, i < workers.val.length → i' < workers.val.length → i ≠ i' →
      (comp workers i 0, comp workers i 1) ≠ (comp workers i' 0, comp workers i' 1)

    b_distinct : ∀ j j' : Nat, j < bikes.val.length → j' < bikes.val.length → j ≠ j' →
      (comp bikes j 0, comp bikes j 1) ≠ (comp bikes j' 0, comp bikes j' 1)

  /-- Whenever assign_bikes(workers, bikes) returns a result r, let n = len(workers), m = len(bikes), and for 0 <= i < n and 0 <= j < m define D(i,j) = |workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|. Start with U = {0,...,n-1} and V = {0,...,m-1}. For k = 0,1,...,n-1, choose the unique pair (i_k,j_k) in U x V for which the triple (D(i_k,j_k), i_k, j_k) is lexicographically smallest among all pairs in U x V; set r[i_k] = j_k; then remove i_k from U and j_k from V. The returned array r has exactly these entries, indexed by worker index (0-based).
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] is a vector of length 2; every coordinate is an integer with 0 <= coordinate <= 1000; the worker points workers[0],...,workers[n-1] are pairwise distinct and the bike points bikes[0],...,bikes[m-1] are pairwise distinct. -/
  theorem spec_1 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ k : Nat, k < workers.val.length → ∀ p : Nat × Nat,
        (greedy (D workers bikes) workers.val.length bikes.val.length)[k]? = some p →
        ent r p.1 = (p.2 : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ k : Nat, k < workers.val.length → ∀ p : Nat × Nat,
          (greedy (D workers bikes) workers.val.length bikes.val.length)[k]? = some p →
          ent r p.1 = (p.2 : ℤ)) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, len(r) = len(workers).
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_2 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      r.val.length = workers.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), r.val.length = workers.val.length) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, for every i with 0 <= i < len(workers), we have 0 <= r[i] < len(bikes).
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_3 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ i : Nat, i < workers.val.length →
        0 ≤ ent r i ∧ ent r i < (bikes.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ i : Nat, i < workers.val.length →
          0 ≤ ent r i ∧ ent r i < (bikes.val.length : ℤ)) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, for all i,k with 0 <= i < k < len(workers), we have r[i] != r[k].
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_4 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ i k : Nat, i < k → k < workers.val.length → ent r i ≠ ent r k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ i k : Nat, i < k → k < workers.val.length → ent r i ≠ ent r k) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, the set of values occurring in r is exactly {0,1,...,m-1}, where m = len(bikes); equivalently r is a permutation of all bike indices.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. Assume additionally n = m. -/
  theorem spec_5 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (h_eq : workers.val.length = bikes.val.length)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ b : ℤ, (∃ i : Nat, i < workers.val.length ∧ ent r i = b) ↔
        (0 ≤ b ∧ b < (bikes.val.length : ℤ)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (h_eq : workers.val.length = bikes.val.length)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ b : ℤ, (∃ i : Nat, i < workers.val.length ∧ ent r i = b) ↔
          (0 ≤ b ∧ b < (bikes.val.length : ℤ))) := by
    sorry

  /-- Define D(i,j) = |workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|. Let (i0,j0) be the unique pair with 0 <= i0 < len(workers) and 0 <= j0 < len(bikes) that lexicographically minimizes (D(i0,j0), i0, j0) over all worker-bike pairs. Whenever assign_bikes(workers, bikes) returns a result r, r[i0] = j0.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_6 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (i0 j0 : Nat) (hi0 : i0 < workers.val.length) (hj0 : j0 < bikes.val.length)
      (hmin : ∀ i j : Nat, i < workers.val.length → j < bikes.val.length →
        ¬ keyLt (D workers bikes) (i, j) (i0, j0))
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ent r i0 = (j0 : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (i0 j0 : Nat) (hi0 : i0 < workers.val.length) (hj0 : j0 < bikes.val.length)
        (hmin : ∀ i j : Nat, i < workers.val.length → j < bikes.val.length →
          ¬ keyLt (D workers bikes) (i, j) (i0, j0))
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ent r i0 = (j0 : ℤ)) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, for every worker i with 0 <= i < len(workers) and every bike k with 0 <= k < len(bikes) such that k is not equal to r[t] for any t with 0 <= t < len(workers), we have D(i,r[i]) <= D(i,k), where D(i,j) = |workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_7 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ i k : Nat, i < workers.val.length → k < bikes.val.length →
        (∀ t : Nat, t < workers.val.length → ent r t ≠ (k : ℤ)) →
        D workers bikes i (entNat r i) ≤ D workers bikes i k := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ i k : Nat, i < workers.val.length → k < bikes.val.length →
          (∀ t : Nat, t < workers.val.length → ent r t ≠ (k : ℤ)) →
          D workers bikes i (entNat r i) ≤ D workers bikes i k) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns a result r, for every worker i with 0 <= i < len(workers) and every bike k with 0 <= k < len(bikes) such that k is not equal to r[t] for any t with 0 <= t < len(workers), if D(i,r[i]) = D(i,k), then r[i] < k, where D(i,j) = |workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_8 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ i k : Nat, i < workers.val.length → k < bikes.val.length →
        (∀ t : Nat, t < workers.val.length → ent r t ≠ (k : ℤ)) →
        D workers bikes i (entNat r i) = D workers bikes i k → ent r i < (k : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ i k : Nat, i < workers.val.length → k < bikes.val.length →
          (∀ t : Nat, t < workers.val.length → ent r t ≠ (k : ℤ)) →
          D workers bikes i (entNat r i) = D workers bikes i k → ent r i < (k : ℤ)) := by
    sorry

  /-- Whenever assign_bikes(workers, bikes) returns r and assign_bikes(workers', bikes') returns r', we have r = r'.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] has length 2; every coordinate is in [0,1000]; worker positions are pairwise distinct and bike positions are pairwise distinct. Let a,b be integers and define workers'[i][0] = workers[i][0]+a, workers'[i][1] = workers[i][1]+b, bikes'[j][0] = bikes[j][0]+a, bikes'[j][1] = bikes[j][1]+b; assume workers' and bikes' also satisfy the same preconditions. -/
  theorem spec_9 (workers bikes workers' bikes' : Slice (alloc.vec.Vec I64))
      (hpre : Pre workers bikes) (hpre' : Pre workers' bikes') (a b : ℤ)
      (hlen_w : workers'.val.length = workers.val.length)
      (hlen_b : bikes'.val.length = bikes.val.length)
      (hx_w : ∀ i : Nat, i < workers.val.length → comp workers' i 0 = comp workers i 0 + a)
      (hy_w : ∀ i : Nat, i < workers.val.length → comp workers' i 1 = comp workers i 1 + b)
      (hx_b : ∀ j : Nat, j < bikes.val.length → comp bikes' j 0 = comp bikes j 0 + a)
      (hy_b : ∀ j : Nat, j < bikes.val.length → comp bikes' j 1 = comp bikes j 1 + b)
      (r r' : alloc.vec.Vec I64)
      (hr : assign_bikes workers bikes = ok r) (hr' : assign_bikes workers' bikes' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (workers bikes workers' bikes' : Slice (alloc.vec.Vec I64))
        (hpre : Pre workers bikes) (hpre' : Pre workers' bikes') (a b : ℤ)
        (hlen_w : workers'.val.length = workers.val.length)
        (hlen_b : bikes'.val.length = bikes.val.length)
        (hx_w : ∀ i : Nat, i < workers.val.length → comp workers' i 0 = comp workers i 0 + a)
        (hy_w : ∀ i : Nat, i < workers.val.length → comp workers' i 1 = comp workers i 1 + b)
        (hx_b : ∀ j : Nat, j < bikes.val.length → comp bikes' j 0 = comp bikes j 0 + a)
        (hy_b : ∀ j : Nat, j < bikes.val.length → comp bikes' j 1 = comp bikes j 1 + b)
        (r r' : alloc.vec.Vec I64)
        (hr : assign_bikes workers bikes = ok r) (hr' : assign_bikes workers' bikes' = ok r'), r.val = r'.val) := by
    sorry

  /-- For every workers and bikes satisfying the preconditions, assign_bikes(workers, bikes) returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] is a vector of length 2; every coordinate is an integer with 0 <= coordinate <= 1000; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_10 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes) :
      ∃ r : alloc.vec.Vec I64, assign_bikes workers bikes = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes), ∃ r : alloc.vec.Vec I64, assign_bikes workers bikes = ok r) := by
    sorry

  /-- Define D(i,j) = |workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|, and let i_0,...,i_{n-1} be the worker indices in the order selected by the greedy process of spec_1. Whenever assign_bikes(workers, bikes) returns a result r, for every worker i and every bike k such that r[t] = k for some t != i, if the pair (D(i,k), k) is lexicographically smaller than (D(i,r[i]), r[i]), then t occurs before i in the selection order.
    Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 1000; every workers[i] and bikes[j] is a vector of length 2; every coordinate is an integer with 0 <= coordinate <= 1000; worker positions are pairwise distinct and bike positions are pairwise distinct. -/
  theorem spec_11 (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
      (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r) :
      ∀ i k t : Nat, i < workers.val.length → k < bikes.val.length →
        t < workers.val.length → t ≠ i → ent r t = (k : ℤ) →
        keyLt2 (D workers bikes) (i, k) (i, entNat r i) →
        before (order workers bikes) t i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (workers bikes : Slice (alloc.vec.Vec I64)) (hpre : Pre workers bikes)
        (r : alloc.vec.Vec I64) (hr : assign_bikes workers bikes = ok r), ∀ i k t : Nat, i < workers.val.length → k < bikes.val.length →
          t < workers.val.length → t ≠ i → ent r t = (k : ℤ) →
          keyLt2 (D workers bikes) (i, k) (i, entNat r i) →
          before (order workers bikes) t i) := by
    sorry

  end AegisSpec.AssignBikes
