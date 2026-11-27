import Aegis.EarliestAcq.Code.Funs

/-!
# Specifications of `Aegis.EarliestAcq.earliest_acq`

LeetCode problem `the-earliest-moment-when-everyone-become-friends`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.EarliestAcq

  abbrev Row : Type := alloc.vec.Vec Std.I64

  abbrev Logs : Type := Slice (alloc.vec.Vec Std.I64)

  def rowVals (r : Row) : List Int := r.val.map (fun s => s.val)

  def rows (logs : Logs) (i : Nat) : List Int :=
    match logs.val[i]? with
    | none => []
    | some r => rowVals r

  def len (logs : Logs) : Nat := logs.val.length

  def ts (logs : Logs) (i : Nat) : Int := (rows logs i).getD 0 0

  def x (logs : Logs) (i : Nat) : Int := (rows logs i).getD 1 0

  def y (logs : Logs) (i : Nat) : Int := (rows logs i).getD 2 0

  def RowsTriples (logs : Logs) : Prop :=
    ∀ i, i < len logs → (rows logs i).length = 3

  def TsInRange (logs : Logs) : Prop :=
    ∀ i, i < len logs → 0 ≤ ts logs i ∧ ts logs i ≤ 1000000000

  def EndpointsInRange (logs : Logs) (n : Int) : Prop :=
    ∀ i, i < len logs →
      0 ≤ x logs i ∧ x logs i < n ∧ 0 ≤ y logs i ∧ y logs i < n ∧ x logs i ≠ y logs i

  def TsPairwiseDistinct (logs : Logs) : Prop :=
    ∀ i j, i < len logs → j < len logs → ts logs i = ts logs j → i = j

  def SameEndpointPair (logs : Logs) (i j : Nat) : Prop :=
    (x logs i = x logs j ∧ y logs i = y logs j) ∨ (x logs i = y logs j ∧ y logs i = x logs j)

  def EdgesPairwiseDistinct (logs : Logs) : Prop :=
    ∀ i j, i < len logs → j < len logs → i ≠ j → ¬ SameEndpointPair logs i j

  def Pre (logs : Logs) (n : Int) : Prop :=
    1 ≤ len logs ∧ len logs ≤ 10000 ∧ 2 ≤ n ∧ n ≤ 100 ∧
      RowsTriples logs ∧ TsInRange logs ∧ EndpointsInRange logs n ∧
        TsPairwiseDistinct logs ∧ EdgesPairwiseDistinct logs

  def EdgeAt (logs : Logs) (t : Int) (u v : Int) : Prop :=
    ∃ i, i < len logs ∧ ts logs i ≤ t ∧
      ((x logs i = u ∧ y logs i = v) ∨ (x logs i = v ∧ y logs i = u))

  def EdgeBefore (logs : Logs) (t : Int) (u v : Int) : Prop :=
    ∃ i, i < len logs ∧ ts logs i < t ∧
      ((x logs i = u ∧ y logs i = v) ∨ (x logs i = v ∧ y logs i = u))

  def EdgeAll (logs : Logs) (u v : Int) : Prop :=
    ∃ i, i < len logs ∧ ((x logs i = u ∧ y logs i = v) ∨ (x logs i = v ∧ y logs i = u))

  def ReachesAt (logs : Logs) (t : Int) (a b : Int) : Prop :=
    Relation.ReflTransGen (EdgeAt logs t) a b

  def ReachesBefore (logs : Logs) (t : Int) (a b : Int) : Prop :=
    Relation.ReflTransGen (EdgeBefore logs t) a b

  def ReachesAll (logs : Logs) (a b : Int) : Prop :=
    Relation.ReflTransGen (EdgeAll logs) a b

  def ConnectedAt (logs : Logs) (n : Int) (t : Int) : Prop :=
    ∀ a b, 0 ≤ a → a < n → 0 ≤ b → b < n → ReachesAt logs t a b

  def ConnectedAll (logs : Logs) (n : Int) : Prop :=
    ∀ a b, 0 ≤ a → a < n → 0 ≤ b → b < n → ReachesAll logs a b

  def tsFinset (logs : Logs) : Finset Int := (Finset.range (len logs)).image (ts logs)

  def minTs (logs : Logs) : Int :=
    if h : (tsFinset logs).Nonempty then (tsFinset logs).min' h else 0

  def maxTs (logs : Logs) : Int :=
    if h : (tsFinset logs).Nonempty then (tsFinset logs).max' h else 0

  def IsCut (logs : Logs) (n : Int) (S : Set Int) : Prop :=
    (∀ v, v ∈ S → 0 ≤ v ∧ v < n) ∧
      (∃ v, 0 ≤ v ∧ v < n ∧ v ∈ S) ∧
        (∃ v, 0 ≤ v ∧ v < n ∧ v ∉ S) ∧
          (∀ i, i < len logs → (x logs i ∈ S ↔ y logs i ∈ S))

  theorem edgeAt_symm (logs : Logs) (t u v : Int) : EdgeAt logs t u v → EdgeAt logs t v u := by
    rintro ⟨i, hi, ht, h | h⟩
    · exact ⟨i, hi, ht, Or.inr h⟩
    · exact ⟨i, hi, ht, Or.inl h⟩

  theorem reachesAt_refl (logs : Logs) (t a : Int) : ReachesAt logs t a a :=
    Relation.ReflTransGen.refl

  theorem reachesAt_edge (logs : Logs) (t u v : Int) : EdgeAt logs t u v → ReachesAt logs t u v :=
    Relation.ReflTransGen.single

  theorem reachesAll_edge (logs : Logs) (u v : Int) : EdgeAll logs u v → ReachesAll logs u v :=
    Relation.ReflTransGen.single

  /-- Whenever the function returns a result r, the following holds. For a time t, let G(t) be the undirected graph on vertices {0,1,...,n-1} whose edges are exactly the unordered pairs {x(i),y(i)} for all i with ts(i) <= t. If there exists a timestamp t equal to some ts(i) such that G(t) is connected, then r is the least such timestamp. If no timestamp t equal to some ts(i) makes G(t) connected, then r = -1. Equivalently, r is the earliest time at which every pair of people is in one connected acquaintance component using all friendship events with timestamp <= r, or -1 if no such time exists.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_1 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r →
        ((∃ i, i < len logs ∧ ConnectedAt logs n.val (ts logs i)) →
            ((∃ i, i < len logs ∧ ts logs i = r.val) ∧ ConnectedAt logs n.val r.val) ∧
              (∀ t, (∃ i, i < len logs ∧ ts logs i = t) → ConnectedAt logs n.val t →
                r.val ≤ t)) ∧
          ((¬ ∃ i, i < len logs ∧ ConnectedAt logs n.val (ts logs i)) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r →
          ((∃ i, i < len logs ∧ ConnectedAt logs n.val (ts logs i)) →
              ((∃ i, i < len logs ∧ ts logs i = r.val) ∧ ConnectedAt logs n.val r.val) ∧
                (∀ t, (∃ i, i < len logs ∧ ts logs i = t) → ConnectedAt logs n.val t →
                  r.val ≤ t)) ∧
            ((¬ ∃ i, i < len logs ∧ ConnectedAt logs n.val (ts logs i)) → r.val = -1)) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result r; it does not fail, panic, or report overflow.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_2 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∃ r, Aegis.EarliestAcq.earliest_acq logs n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∃ r, Aegis.EarliestAcq.earliest_acq logs n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or there exists an index i with 0 <= i < len(logs) such that r = ts(i).
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_3 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r →
        (r.val = -1 ∨ ∃ i, i < len logs ∧ r.val = ts logs i) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r →
          (r.val = -1 ∨ ∃ i, i < len logs ∧ r.val = ts logs i)) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, min_{0 <= i < len(logs)} ts(i) <= r <= max_{0 <= i < len(logs)} ts(i).
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_4 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
        minTs logs ≤ r.val ∧ r.val ≤ maxTs logs := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
          minTs logs ≤ r.val ∧ r.val ≤ maxTs logs) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, let G(r) be the undirected graph on vertices {0,1,...,n-1} with an edge {x(i),y(i)} for every i with ts(i) <= r. Then G(r) is connected: for every two people a and b with 0 <= a < n and 0 <= b < n, there is a sequence of people starting at a and ending at b in which every consecutive pair appears as such an edge.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_5 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
        ConnectedAt logs n.val r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
          ConnectedAt logs n.val r.val) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, for every integer t with 0 <= t < r, the graph G(t) on vertices {0,1,...,n-1} with edges {x(i),y(i)} for all i with ts(i) <= t is not connected.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_6 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
        ∀ t, 0 ≤ t → t < r.val → ¬ ConnectedAt logs n.val t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
          ∀ t, 0 ≤ t → t < r.val → ¬ ConnectedAt logs n.val t) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if the graph on vertices {0,1,...,n-1} containing an edge {x(i),y(i)} for every log entry i with 0 <= i < len(logs) is not connected.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_7 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → (r.val = -1 ↔ ¬ ConnectedAll logs n.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → (r.val = -1 ↔ ¬ ConnectedAll logs n.val)) := by
    sorry

  /-- Whenever the function returns a result r and r = -1, there exists a nonempty proper subset S of {0,1,...,n-1} such that for every i with 0 <= i < len(logs), x(i) is in S if and only if y(i) is in S; thus no friendship log crosses the cut between S and its complement.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_8 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val = -1 →
        ∃ S : Set Int, IsCut logs n.val S := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val = -1 →
          ∃ S : Set Int, IsCut logs n.val S) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, let j be the unique index with ts(j) = r. In the graph G_<r on vertices {0,1,...,n-1} with edges {x(i),y(i)} for all i with ts(i) < r, the vertices x(j) and y(j) are in different connected components.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_9 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
        ∀ j, j < len logs → ts logs j = r.val →
          ¬ ReachesBefore logs r.val (x logs j) (y logs j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
          ∀ j, j < len logs → ts logs j = r.val →
            ¬ ReachesBefore logs r.val (x logs j) (y logs j)) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, for every integer t with r <= t <= 10^9, the graph G(t) on vertices {0,1,...,n-1} with edges {x(i),y(i)} for all i with ts(i) <= t is connected.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct. -/
  theorem spec_10 (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val) :
      ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
        ∀ t, r.val ≤ t → t ≤ 1000000000 → ConnectedAt logs n.val t := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (logs : Logs) (n : Std.I64) (hpre : Pre logs n.val), ∀ r, Aegis.EarliestAcq.earliest_acq logs n = ok r → r.val ≠ -1 →
          ∀ t, r.val ≤ t → t ≤ 1000000000 → ConnectedAt logs n.val t) := by
    sorry

  /-- Whenever the function returns r on (logs,n) and returns r' on (logs',n), we have r = r'.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct; logs' is any slice satisfying the same constraints whose entries are a permutation of the entries of logs. -/
  theorem spec_11 (logs logs' : Logs) (n : Std.I64)
      (hpre : Pre logs n.val) (hpre' : Pre logs' n.val) (hperm : logs'.val.Perm logs.val) :
      ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
        Aegis.EarliestAcq.earliest_acq logs' n = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (logs logs' : Logs) (n : Std.I64)
        (hpre : Pre logs n.val) (hpre' : Pre logs' n.val) (hperm : logs'.val.Perm logs.val), ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
          Aegis.EarliestAcq.earliest_acq logs' n = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on (logs,n) and returns r' on (logs',n), if r = -1 then r' = -1, and if r != -1 then r' = r + c.
    Preconditions: len(logs) >= 1 and len(logs) <= 10000; for every i with 0 <= i < len(logs), len(logs[i]) = 3; write ts(i) = logs[i][0], x(i) = logs[i][1], y(i) = logs[i][2]; then 2 <= n <= 100, 0 <= ts(i) <= 10^9, 0 <= x(i) < n, 0 <= y(i) < n, x(i) != y(i); the values ts(i) are pairwise distinct; for i != j the unordered pairs {x(i),y(i)} and {x(j),y(j)} are distinct; c is an integer and logs' is obtained from logs by replacing each entry [ts(i),x(i),y(i)] with [ts(i)+c,x(i),y(i)], with 0 <= ts(i)+c <= 10^9 for every i and all constraints still holding. -/
  theorem spec_12 (logs logs' : Logs) (n : Std.I64) (c : Int)
      (hpre : Pre logs n.val) (hpre' : Pre logs' n.val)
      (hlen : len logs' = len logs)
      (hrow : ∀ i, i < len logs →
        ts logs' i = ts logs i + c ∧ x logs' i = x logs i ∧ y logs' i = y logs i)
      (hshift : ∀ i, i < len logs → 0 ≤ ts logs i + c ∧ ts logs i + c ≤ 1000000000) :
      ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
        Aegis.EarliestAcq.earliest_acq logs' n = ok r' →
          (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val = r.val + c) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (logs logs' : Logs) (n : Std.I64) (c : Int)
        (hpre : Pre logs n.val) (hpre' : Pre logs' n.val)
        (hlen : len logs' = len logs)
        (hrow : ∀ i, i < len logs →
          ts logs' i = ts logs i + c ∧ x logs' i = x logs i ∧ y logs' i = y logs i)
        (hshift : ∀ i, i < len logs → 0 ≤ ts logs i + c ∧ ts logs i + c ≤ 1000000000), ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
          Aegis.EarliestAcq.earliest_acq logs' n = ok r' →
            (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val = r.val + c)) := by
    sorry

  /-- Whenever the function returns r on (logs,n) with r != -1, and returns r' on (logs',n), and every additional entry of logs' not present in logs has first component greater than r, then r' = r.
    Preconditions: All constraints hold for (logs,n) and for (logs',n); the multiset of entries of logs' consists of all entries of logs plus finitely many additional valid log entries. -/
  theorem spec_13 (logs logs' : Logs) (n : Std.I64) (extra : List Row)
      (hpre : Pre logs n.val) (hpre' : Pre logs' n.val)
      (hperm : logs'.val.Perm (logs.val ++ extra)) :
      ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
        Aegis.EarliestAcq.earliest_acq logs' n = ok r' → r.val ≠ -1 →
          (∀ e, e ∈ extra → r.val < (rowVals e).getD 0 0) → r = r' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (logs logs' : Logs) (n : Std.I64) (extra : List Row)
        (hpre : Pre logs n.val) (hpre' : Pre logs' n.val)
        (hperm : logs'.val.Perm (logs.val ++ extra)), ∀ r r', Aegis.EarliestAcq.earliest_acq logs n = ok r →
          Aegis.EarliestAcq.earliest_acq logs' n = ok r' → r.val ≠ -1 →
            (∀ e, e ∈ extra → r.val < (rowVals e).getD 0 0) → r = r') := by
    sorry

  end AegisSpec.EarliestAcq
