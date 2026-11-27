import Aegis.MinimumScore.Code.Funs

/-!
# Specifications of `Aegis.MinimumScore.minimum_score`

LeetCode problem `minimum-score-after-removals-on-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumScore

open Aegis.MinimumScore (minimum_score)

def numsVal (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x : Std.I64 => x.val)

def nVerts (nums : Slice Std.I64) : ℕ := nums.val.length

def vertVal (nums : Slice Std.I64) (v : ℕ) : ℤ := (numsVal nums).getD v 0

def vertValNat (nums : Slice Std.I64) (v : ℕ) : ℕ := (vertVal nums v).toNat

def edgePair (e : alloc.vec.Vec Std.I64) : ℕ × ℕ :=
  ((e.val.map (fun x : Std.I64 => x.val.toNat)).getD 0 0,
    (e.val.map (fun x : Std.I64 => x.val.toNat)).getD 1 0)

def edgeL (edges : Slice (alloc.vec.Vec Std.I64)) : List (ℕ × ℕ) := edges.val.map edgePair

def Adj (E : List (ℕ × ℕ)) (u v : ℕ) : Prop := (u, v) ∈ E ∨ (v, u) ∈ E

def Reach (E : List (ℕ × ℕ)) (u v : ℕ) : Prop := Relation.ReflTransGen (Adj E) u v

def ConnectedOn (E : List (ℕ × ℕ)) (n : ℕ) : Prop :=
  ∀ u, u < n → ∀ v, v < n → Reach E u v

def HasCycle (E : List (ℕ × ℕ)) : Prop :=
  ∃ c : List ℕ, 3 ≤ c.length ∧ c.Nodup ∧ ∀ p ∈ c.zip (c.rotate 1), Adj E p.1 p.2

def IsTree (E : List (ℕ × ℕ)) (n : ℕ) : Prop :=
  (∀ p ∈ E, p.1 < n ∧ p.2 < n) ∧ ConnectedOn E n ∧ ¬ HasCycle E

def removeTwo (E : List (ℕ × ℕ)) (i j : ℕ) : List (ℕ × ℕ) := (E.eraseIdx i).eraseIdx (j - 1)

noncomputable def compOf (E : List (ℕ × ℕ)) (n v : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun u => Reach E v u)

def IsComponent (E : List (ℕ × ℕ)) (n : ℕ) (C : Finset ℕ) : Prop :=
  ∃ v, v < n ∧ C = compOf E n v

def IsComponentTriple (E : List (ℕ × ℕ)) (n : ℕ) (C1 C2 C3 : Finset ℕ) : Prop :=
  IsComponent E n C1 ∧ IsComponent E n C2 ∧ IsComponent E n C3 ∧
    C1.Nonempty ∧ C2.Nonempty ∧ C3.Nonempty ∧
    C1 ∪ C2 ∪ C3 = Finset.range n ∧ C1 ∩ C2 = ∅ ∧ C1 ∩ C3 = ∅ ∧ C2 ∩ C3 = ∅

def xorSet (nums : Slice Std.I64) (n : ℕ) (C : Finset ℕ) : ℕ :=
  ((List.range n).filter (fun v => v ∈ C)).foldl (fun acc v => Nat.xor acc (vertValNat nums v)) 0

def ScoreOf (nums : Slice Std.I64) (n : ℕ) (E : List (ℕ × ℕ)) (i j : ℕ) (s : ℤ) : Prop :=
  ∃ C1 C2 C3 : Finset ℕ,
    IsComponentTriple (removeTwo E i j) n C1 C2 C3 ∧
      s = ((max (xorSet nums n C1) (max (xorSet nums n C2) (xorSet nums n C3)) : ℤ) -
        (min (xorSet nums n C1) (min (xorSet nums n C2) (xorSet nums n C3)) : ℤ))

def Score (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) (s : ℤ) : Prop :=
  ScoreOf nums (nVerts nums) (edgeL edges) i j s

def EqualComponentXors (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Prop :=
  ∃ C1 C2 C3 : Finset ℕ,
    IsComponentTriple (removeTwo (edgeL edges) i j) (nVerts nums) C1 C2 C3 ∧
      xorSet nums (nVerts nums) C1 = xorSet nums (nVerts nums) C2 ∧
        xorSet nums (nVerts nums) C1 = xorSet nums (nVerts nums) C3

def IsPermOn (n : ℕ) (pi : ℕ → ℕ) : Prop :=
  (∀ v, v < n → pi v < n) ∧ (∀ v, v < n → ∀ w, w < n → pi v = pi w → v = w) ∧
    (∀ w, w < n → ∃ v, v < n ∧ pi v = w)

/-- Let n = len(nums). For every pair of distinct edge indices i,j with 0 <= i < j < len(edges), deleting edges[i] and edges[j] from the tree splits the vertex set {0,...,n-1} into three nonempty connected components C1,C2,C3. For such a pair define score(i,j) = max(xor(C1), xor(C2), xor(C3)) - min(xor(C1), xor(C2), xor(C3)), where xor(C) is the bitwise XOR of nums[v] over all vertices v in C. The function returns a result r and r = min { score(i,j) : 0 <= i < j < len(edges) }.
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_1 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∃ r : Std.I64, minimum_score nums edges = ok r ∧
      (∀ i j : ℕ, i < j → j < (edgeL edges).length →
        ∀ s : ℤ, Score nums edges i j s → r.val ≤ s) ∧
      (∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧ Score nums edges i j r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∃ r : Std.I64, minimum_score nums edges = ok r ∧
      (∀ i j : ℕ, i < j → j < (edgeL edges).length →
        ∀ s : ℤ, Score nums edges i j s → r.val ≤ s) ∧
      (∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧ Score nums edges i j r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, panic, or out-of-bounds).
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_2 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∃ r : Std.I64, minimum_score nums edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∃ r : Std.I64, minimum_score nums edges = ok r) := by
  sorry

/-- Whenever the function returns a result r on such an input, 0 <= r.
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_3 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∀ r : Std.I64, minimum_score nums edges = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∀ r : Std.I64, minimum_score nums edges = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on such an input, r <= 134217727.
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_4 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∀ r : Std.I64, minimum_score nums edges = ok r → r.val ≤ 134217727 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∀ r : Std.I64, minimum_score nums edges = ok r → r.val ≤ 134217727) := by
  sorry

/-- Whenever the function returns a result r on such an input, there exist indices i,j with 0 <= i < j < len(edges) such that r equals the score of deleting edges[i] and edges[j], namely max(xor(C1), xor(C2), xor(C3)) - min(xor(C1), xor(C2), xor(C3)), where C1,C2,C3 are the three connected components left after deleting those two edges and xor(C) is the bitwise XOR of nums[v] over v in C.
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_5 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∀ r : Std.I64, minimum_score nums edges = ok r →
      ∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧ Score nums edges i j r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∀ r : Std.I64, minimum_score nums edges = ok r →
      ∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧ Score nums edges i j r.val) := by
  sorry

/-- Whenever the function returns a result r on such an input, for every pair of indices i,j with 0 <= i < j < len(edges), r <= score(i,j), where score(i,j) is the max-minus-min of the three component XORs after deleting edges[i] and edges[j] (with component XOR defined as in spec_1).
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_6 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∀ r : Std.I64, minimum_score nums edges = ok r →
      ∀ i j : ℕ, i < j → j < (edgeL edges).length →
        ∀ s : ℤ, Score nums edges i j s → r.val ≤ s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∀ r : Std.I64, minimum_score nums edges = ok r →
      ∀ i j : ℕ, i < j → j < (edgeL edges).length →
        ∀ s : ℤ, Score nums edges i j s → r.val ≤ s) := by
  sorry

/-- Whenever the function returns a result r on such an input, r = 0 if and only if there exist indices i,j with 0 <= i < j < len(edges) such that, after deleting edges[i] and edges[j], the three resulting connected components C1,C2,C3 satisfy xor(C1) = xor(C2) = xor(C3), where xor(C) is the bitwise XOR of nums[v] over v in C.
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). -/
theorem spec_7 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)) :
    ∀ r : Std.I64, minimum_score nums edges = ok r →
      (r.val = 0 ↔ ∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧
        EqualComponentXors nums edges i j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums)), ∀ r : Std.I64, minimum_score nums edges = ok r →
      (r.val = 0 ↔ ∃ i j : ℕ, i < j ∧ j < (edgeL edges).length ∧
        EqualComponentXors nums edges i j)) := by
  sorry

/-- For every such edges', the value returned by minimum_score on (nums, edges') equals the value returned by minimum_score on (nums, edges).
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). Also, edges' is another list of length n-1, each entry has length 2 with entries in [0,n), and the set of unordered pairs {edges[k][0], edges[k][1]} for 0 <= k < n-1 equals the set of unordered pairs {edges'[k][0], edges'[k][1]} for 0 <= k < n-1. -/
theorem spec_8 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (edges' : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums))
    (h_cases' : (edgeL edges').length = nVerts nums - 1)
    (h_entry_len' : ∀ e ∈ edges'.val, e.val.length = 2)
    (h_endpts' : ∀ p ∈ edgeL edges', p.1 < nVerts nums ∧ p.2 < nVerts nums)
    (h_same : ∀ u v : ℕ, Adj (edgeL edges) u v ↔ Adj (edgeL edges') u v) :
    ∃ r : Std.I64, minimum_score nums edges = ok r ∧ minimum_score nums edges' = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (edges' : Slice (alloc.vec.Vec Std.I64))
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums))
    (h_cases' : (edgeL edges').length = nVerts nums - 1)
    (h_entry_len' : ∀ e ∈ edges'.val, e.val.length = 2)
    (h_endpts' : ∀ p ∈ edgeL edges', p.1 < nVerts nums ∧ p.2 < nVerts nums)
    (h_same : ∀ u v : ℕ, Adj (edgeL edges) u v ↔ Adj (edgeL edges') u v), ∃ r : Std.I64, minimum_score nums edges = ok r ∧ minimum_score nums edges' = ok r) := by
  sorry

/-- The value returned by minimum_score on (nums', edges') equals the value returned by minimum_score on (nums, edges).
  Preconditions: n = len(nums); 3 <= n <= 1000; 1 <= nums[i] <= 100000000 for every 0 <= i < n; len(edges) = n - 1; each edges[k] is a list of length 2 for 0 <= k < n - 1; edges[k][0] and edges[k][1] are distinct indices in [0,n); and the undirected simple graph on vertices 0,...,n-1 with edge set { {edges[k][0], edges[k][1]} : 0 <= k < n-1 } is a tree (connected and acyclic). Let pi be any permutation of {0,...,n-1}; let nums' be any length-n integer array with nums'[pi(v)] = nums[v] for every v; and let edges' be the length-(n-1) edge list with edges'[k] = [pi(edges[k][0]), pi(edges[k][1])] for every k. -/
theorem spec_9 (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (nums' : Slice Std.I64) (edges' : Slice (alloc.vec.Vec Std.I64)) (pi : ℕ → ℕ)
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums))
    (h_perm : IsPermOn (nVerts nums) pi)
    (h_nums'_len : nVerts nums' = nVerts nums)
    (h_nums' : ∀ v, v < nVerts nums → vertVal nums' (pi v) = vertVal nums v)
    (h_edges' : edgeL edges' = (edgeL edges).map (fun p => (pi p.1, pi p.2))) :
    ∃ r : Std.I64, minimum_score nums edges = ok r ∧ minimum_score nums' edges' = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (nums' : Slice Std.I64) (edges' : Slice (alloc.vec.Vec Std.I64)) (pi : ℕ → ℕ)
    (h_n_lo : 3 ≤ nVerts nums) (h_n_hi : nVerts nums ≤ 1000)
    (h_vals : ∀ v, v < nVerts nums → 1 ≤ vertVal nums v ∧ vertVal nums v ≤ 100000000)
    (h_cases : (edgeL edges).length = nVerts nums - 1)
    (h_entry_len : ∀ e ∈ edges.val, e.val.length = 2)
    (h_endpts : ∀ p ∈ edgeL edges, p.1 < nVerts nums ∧ p.2 < nVerts nums ∧ p.1 ≠ p.2)
    (h_tree : IsTree (edgeL edges) (nVerts nums))
    (h_perm : IsPermOn (nVerts nums) pi)
    (h_nums'_len : nVerts nums' = nVerts nums)
    (h_nums' : ∀ v, v < nVerts nums → vertVal nums' (pi v) = vertVal nums v)
    (h_edges' : edgeL edges' = (edgeL edges).map (fun p => (pi p.1, pi p.2))), ∃ r : Std.I64, minimum_score nums edges = ok r ∧ minimum_score nums' edges' = ok r) := by
  sorry

  end AegisSpec.MinimumScore
