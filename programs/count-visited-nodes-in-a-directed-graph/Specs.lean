import Aegis.CountVisitedNodes.Code.Funs

/-!
# Specifications of `Aegis.CountVisitedNodes.count_visited_nodes`

LeetCode problem `count-visited-nodes-in-a-directed-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountVisitedNodes

  open Aegis.CountVisitedNodes

  def nxt (edges : Slice I64) (i : ℕ) : ℕ :=
    ((edges.val[i]!).val).toNat

  def orbit (edges : Slice I64) (i : ℕ) : ℕ → ℕ
    | 0 => i
    | k + 1 => nxt edges (orbit edges i k)

  def firstRepeatSet (edges : Slice I64) (i : ℕ) : Set ℕ :=
    {m | 0 < m ∧ ∃ j, j < m ∧ orbit edges i m = orbit edges i j}

  def returnSet (edges : Slice I64) (i : ℕ) : Set ℕ :=
    {k | 1 ≤ k ∧ orbit edges i k = i}

  def neverReturns (edges : Slice I64) (i : ℕ) : Prop :=
    ∀ k, 1 ≤ k → orbit edges i k ≠ i

  def distinctPrefix (edges : Slice I64) (i m : ℕ) : ℕ :=
    ((List.range m).map (orbit edges i)).dedup.length

  def Pre (edges : Slice I64) (n : ℕ) : Prop :=
    n = edges.length ∧ 2 ≤ n ∧ n ≤ 100000 ∧
      ∀ i, i < n → 0 ≤ (edges.val[i]!).val ∧ (edges.val[i]!).val < (n : ℤ)

  /-- Whenever count_visited_nodes returns a result r, we have len(r) = n, and for every start i with 0 <= i < n the following holds. Define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. Let m_i be the least positive integer m for which there exists j with 0 <= j < m and x_m(i)=x_j(i). Then r[i] = m_i. Equivalently, r[i] is the number of distinct nodes in the initial segment x_0(i), x_1(i), ..., x_{m_i-1}(i), i.e. the number visited before the first repeated node.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. Self-loops are allowed; see the note. -/
  theorem spec_1 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      r.val.length = n ∧
        (∀ i, i < n → ∀ m, IsLeast (firstRepeatSet edges i) m →
          (r.val[i]!).val = (m : ℤ)) ∧
        (∀ i, i < n → ∀ m, IsLeast (firstRepeatSet edges i) m →
          (r.val[i]!).val = ((distinctPrefix edges i m : ℕ) : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), r.val.length = n ∧
          (∀ i, i < n → ∀ m, IsLeast (firstRepeatSet edges i) m →
            (r.val[i]!).val = (m : ℤ)) ∧
          (∀ i, i < n → ∀ m, IsLeast (firstRepeatSet edges i) m →
            (r.val[i]!).val = ((distinctPrefix edges i m : ℕ) : ℤ))) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, len(r) = len(edges).
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_2 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      r.val.length = edges.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), r.val.length = edges.length) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, 1 <= r[i] <= n.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_3 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → 1 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ (n : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → 1 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ (n : ℤ)) := by
    sorry

  /-- Under these preconditions, count_visited_nodes returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_4 (edges : Slice I64) (n : ℕ) (hn : Pre edges n) :
      ∃ r, count_visited_nodes edges = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n), ∃ r, count_visited_nodes edges = ok r) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, if edges[i] = i then r[i] = 1.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_5 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → (edges.val[i]!).val = (i : ℤ) → (r.val[i]!).val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → (edges.val[i]!).val = (i : ℤ) → (r.val[i]!).val = 1) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for all i and j with 0 <= i < n and 0 <= j < n, if i != j, edges[i] = j, and edges[j] = i, then r[i] = 2 and r[j] = 2.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_6 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → ∀ j, j < n → i ≠ j →
        (edges.val[i]!).val = (j : ℤ) → (edges.val[j]!).val = (i : ℤ) →
          (r.val[i]!).val = 2 ∧ (r.val[j]!).val = 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → ∀ j, j < n → i ≠ j →
          (edges.val[i]!).val = (j : ℤ) → (edges.val[j]!).val = (i : ℤ) →
            (r.val[i]!).val = 2 ∧ (r.val[j]!).val = 2) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If there exists k >= 1 with x_k(i)=i, then r[i] equals the least such k.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_7 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → ∀ k, IsLeast (returnSet edges i) k → (r.val[i]!).val = (k : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → ∀ k, IsLeast (returnSet edges i) k → (r.val[i]!).val = (k : ℤ)) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If for all k >= 1, x_k(i) != i, then r[i] = r[edges[i]] + 1.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_8 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → neverReturns edges i →
        (r.val[i]!).val = (r.val[nxt edges i]!).val + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → neverReturns edges i →
          (r.val[i]!).val = (r.val[nxt edges i]!).val + 1) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If there exists k >= 1 with x_k(edges[i]) = i, then r[i] = r[edges[i]]; otherwise r[i] = r[edges[i]] + 1.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_9 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n →
        ((∃ k, 1 ≤ k ∧ orbit edges (nxt edges i) k = i) →
          (r.val[i]!).val = (r.val[nxt edges i]!).val) ∧
        (¬ (∃ k, 1 ≤ k ∧ orbit edges (nxt edges i) k = i) →
          (r.val[i]!).val = (r.val[nxt edges i]!).val + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n →
          ((∃ k, 1 ≤ k ∧ orbit edges (nxt edges i) k = i) →
            (r.val[i]!).val = (r.val[nxt edges i]!).val) ∧
          (¬ (∃ k, 1 ≤ k ∧ orbit edges (nxt edges i) k = i) →
            (r.val[i]!).val = (r.val[nxt edges i]!).val + 1)) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for all i and j with 0 <= i < n and 0 <= j < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If there exist a >= 0 and b >= 0 such that x_a(i)=j and x_b(j)=i, then r[i] = r[j].
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_10 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → ∀ j, j < n →
        (∃ a, orbit edges i a = j) → (∃ b, orbit edges j b = i) →
          (r.val[i]!).val = (r.val[j]!).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → ∀ j, j < n →
          (∃ a, orbit edges i a = j) → (∃ b, orbit edges j b = i) →
            (r.val[i]!).val = (r.val[j]!).val) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If for all k >= 1, x_k(i) != i, then r[i] > r[edges[i]].
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_11 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → neverReturns edges i →
        (r.val[nxt edges i]!).val < (r.val[i]!).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → neverReturns edges i →
          (r.val[nxt edges i]!).val < (r.val[i]!).val) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If for every i with 0 <= i < n the least positive k satisfying x_k(i)=i exists and equals n, then r[i] = n for every i with 0 <= i < n.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_12 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (hcycle : ∀ i, i < n → IsLeast (returnSet edges i) n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → (r.val[i]!).val = (n : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (hcycle : ∀ i, i < n → IsLeast (returnSet edges i) n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → (r.val[i]!).val = (n : ℤ)) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, r[i] >= 2.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. Suppose additionally that edges[i] != i for every i with 0 <= i < n. -/
  theorem spec_13 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (hno_self : ∀ i, i < n → (edges.val[i]!).val ≠ (i : ℤ))
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → 2 ≤ (r.val[i]!).val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (hno_self : ∀ i, i < n → (edges.val[i]!).val ≠ (i : ℤ))
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → 2 ≤ (r.val[i]!).val) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for every i with 0 <= i < n, if r[i] = 1 then edges[i] = i.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_14 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → (r.val[i]!).val = 1 → (edges.val[i]!).val = (i : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → (r.val[i]!).val = 1 → (edges.val[i]!).val = (i : ℤ)) := by
    sorry

  /-- Whenever count_visited_nodes returns a result r, for all i and j with 0 <= i < n and 0 <= j < n, define x_0(i)=i and x_{k+1}(i)=edges[x_k(i)] for k >= 0. If there exists a >= 0 with x_a(i)=j, then r[i] >= r[j]. Moreover, equality holds for distinct i and j exactly when there also exists b >= 0 with x_b(j)=i.
    Preconditions: Let n = len(edges). Assume 2 <= n <= 100000 and for every index i with 0 <= i < n, 0 <= edges[i] < n. -/
  theorem spec_15 (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
      (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r) :
      ∀ i, i < n → ∀ j, j < n → (∃ a, orbit edges i a = j) →
        (r.val[j]!).val ≤ (r.val[i]!).val ∧
          (i ≠ j → ((r.val[i]!).val = (r.val[j]!).val ↔ ∃ b, orbit edges j b = i)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (edges : Slice I64) (n : ℕ) (hn : Pre edges n)
        (r : alloc.vec.Vec I64) (hr : count_visited_nodes edges = ok r), ∀ i, i < n → ∀ j, j < n → (∃ a, orbit edges i a = j) →
          (r.val[j]!).val ≤ (r.val[i]!).val ∧
            (i ≠ j → ((r.val[i]!).val = (r.val[j]!).val ↔ ∃ b, orbit edges j b = i))) := by
    sorry

  end AegisSpec.CountVisitedNodes
