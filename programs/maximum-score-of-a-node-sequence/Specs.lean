import Aegis.MaximumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumScore.maximum_score`

LeetCode problem `maximum-score-of-a-node-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumScore (maximum_score)

namespace AegisSpec.MaximumScore

def scoreAt (scores : Slice Std.I64) (i : ℕ) : ℤ := (scores.val[i]!).val

def edgeEnds (e : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
  match e.val with
  | [x, y] => some (x.val, y.val)
  | _ => none

def edgePair (e : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
  match e.val with
  | [x, y] => some (min x.val y.val, max x.val y.val)
  | _ => none

def HasEdge (edges : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : Prop :=
  ∃ j : ℕ, ∃ e : alloc.vec.Vec Std.I64, edges.val[j]? = some e ∧
    (edgeEnds e = some ((u : ℤ), (v : ℤ)) ∨ edgeEnds e = some ((v : ℤ), (u : ℤ)))

def IsValidPath4 (edges : Slice (alloc.vec.Vec Std.I64)) (n v0 v1 v2 v3 : ℕ) : Prop :=
  v0 < n ∧ v1 < n ∧ v2 < n ∧ v3 < n ∧
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    HasEdge edges v0 v1 ∧ HasEdge edges v1 v2 ∧ HasEdge edges v2 v3

def pathScore4 (scores : Slice Std.I64) (v0 v1 v2 v3 : ℕ) : ℤ :=
  scoreAt scores v0 + scoreAt scores v1 + scoreAt scores v2 + scoreAt scores v3

def scoreSet (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Set ℤ :=
  {s | ∃ v0 v1 v2 v3 : ℕ, IsValidPath4 edges n v0 v1 v2 v3 ∧ pathScore4 scores v0 v1 v2 v3 = s}

def HasValidPath4 (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Prop :=
  ∃ v0 v1 v2 v3 : ℕ, IsValidPath4 edges n v0 v1 v2 v3

def IsPerm0123 (a b c d : ℕ) : Prop := [a, b, c, d].Perm [0, 1, 2, 3]

def IsPermOn (L : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i < L → p i < L) ∧
    (∀ i j : ℕ, i < L → j < L → p i = p j → i = j) ∧
      (∀ j : ℕ, j < L → ∃ i : ℕ, i < L ∧ p i = j)

def IsEdgeReindex (edges edges' : Slice (alloc.vec.Vec Std.I64)) (p : ℕ → ℕ) : Prop :=
  edges'.val.length = edges.val.length ∧
    ∀ i : ℕ, i < edges.val.length → edges'.val[i]? = edges.val[p i]?

def IsEdgeFlipped (edges edges' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  edges'.val.length = edges.val.length ∧
    ∀ j : ℕ, j < edges.val.length →
      ∀ e e' : alloc.vec.Vec Std.I64, edges.val[j]? = some e → edges'.val[j]? = some e' →
        ∀ x y : Std.I64, e.val = [x, y] → e'.val = [y, x]

def IsTopFourSum (l : List ℤ) (M : ℤ) : Prop :=
  ∃ I : Finset (Fin l.length), I.card = 4 ∧ M = ∑ i ∈ I, l[i] ∧
    ∀ J : Finset (Fin l.length), J.card = 4 → (∑ i ∈ J, l[i]) ≤ M

def ScoresValid (scores : Slice Std.I64) (n : ℕ) : Prop :=
  n = scores.val.length ∧ 4 ≤ n ∧ n ≤ 50000 ∧
    ∀ i : ℕ, i < n → 1 ≤ scoreAt scores i ∧ scoreAt scores i ≤ 100000000

def EdgesValid (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Prop :=
  edges.val.length ≤ 50000 ∧
    (∀ j : ℕ, j < edges.val.length → ∀ e : alloc.vec.Vec Std.I64, edges.val[j]? = some e →
      ∃ x y : Std.I64, e.val = [x, y] ∧ 0 ≤ x.val ∧ x.val < (n : ℤ) ∧
        0 ≤ y.val ∧ y.val < (n : ℤ) ∧ x.val ≠ y.val) ∧
      (∀ j k : ℕ, j < k → k < edges.val.length →
        ∀ e f : alloc.vec.Vec Std.I64, edges.val[j]? = some e → edges.val[k]? = some f →
          edgePair e ≠ edgePair f)

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]; a valid length-4 node sequence is an ordered tuple (v0,v1,v2,v3) of four pairwise distinct indices in [0,n) such that edges are present between v0 and v1, between v1 and v2, and between v2 and v3; its score is scores[v0]+scores[v1]+scores[v2]+scores[v3]. The function returns a result r. Let S be the set of all scores of valid length-4 node sequences. If S is nonempty then r = max(S); if S is empty then r = -1.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_1 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ((scoreSet scores edges n).Nonempty → IsGreatest (scoreSet scores edges n) r.val) ∧
        (scoreSet scores edges n = ∅ → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ((scoreSet scores edges n).Nonempty → IsGreatest (scoreSet scores edges n) r.val) ∧
        (scoreSet scores edges n = ∅ → r.val = -1)) := by
  sorry

/-- The function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow) for every input satisfying the preconditions.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_2 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∃ r : Std.I64, maximum_score scores edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∃ r : Std.I64, maximum_score scores edges = ok r) := by
  sorry

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]; a valid length-4 node sequence is an ordered tuple (v0,v1,v2,v3) of four pairwise distinct indices in [0,n) such that edges are present between v0 and v1, between v1 and v2, and between v2 and v3. The function returns a result r, and r = -1 if and only if no valid length-4 node sequence exists.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_3 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧ (r.val = -1 ↔ ¬ HasValidPath4 edges n) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧ (r.val = -1 ↔ ¬ HasValidPath4 edges n)) := by
  sorry

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]. The function returns a result r. Whenever r != -1, there exist indices v0,v1,v2,v3 with 0 <= v0,v1,v2,v3 < n that are pairwise distinct, edges are present between v0 and v1, between v1 and v2, and between v2 and v3, and r = scores[v0]+scores[v1]+scores[v2]+scores[v3].
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_4 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (r.val ≠ -1 →
          ∃ v0 v1 v2 v3 : ℕ,
            IsValidPath4 edges n v0 v1 v2 v3 ∧ r.val = pathScore4 scores v0 v1 v2 v3) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (r.val ≠ -1 →
          ∃ v0 v1 v2 v3 : ℕ,
            IsValidPath4 edges n v0 v1 v2 v3 ∧ r.val = pathScore4 scores v0 v1 v2 v3)) := by
  sorry

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]; a valid length-4 node sequence is an ordered tuple (v0,v1,v2,v3) of four pairwise distinct indices in [0,n) such that edges are present between v0 and v1, between v1 and v2, and between v2 and v3. The function returns a result r. Whenever r != -1, for every valid length-4 node sequence (v0,v1,v2,v3), scores[v0]+scores[v1]+scores[v2]+scores[v3] <= r.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_5 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (r.val ≠ -1 →
          ∀ v0 v1 v2 v3 : ℕ,
            IsValidPath4 edges n v0 v1 v2 v3 → pathScore4 scores v0 v1 v2 v3 ≤ r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (r.val ≠ -1 →
          ∀ v0 v1 v2 v3 : ℕ,
            IsValidPath4 edges n v0 v1 v2 v3 → pathScore4 scores v0 v1 v2 v3 ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 4 <= r <= 400000000.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_6 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) :
    ∀ r : Std.I64,
      maximum_score scores edges = ok r → (r.val = -1 ∨ (4 ≤ r.val ∧ r.val ≤ 400000000)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n), ∀ r : Std.I64,
      maximum_score scores edges = ok r → (r.val = -1 ∨ (4 ≤ r.val ∧ r.val ≤ 400000000))) := by
  sorry

/-- The function returns -1.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; len(edges) = 0. -/
theorem spec_7 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hempty : edges.val.length = 0) :
    ∃ r : Std.I64, maximum_score scores edges = ok r ∧ r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hempty : edges.val.length = 0), ∃ r : Std.I64, maximum_score scores edges = ok r ∧ r.val = -1) := by
  sorry

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]. The function returns a result r. If there is a permutation (a,b,c,d) of {0,1,2,3} such that edges are present between a and b, between b and c, and between c and d, then r = scores[0]+scores[1]+scores[2]+scores[3]; otherwise r = -1.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; n = 4. -/
theorem spec_8 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hn : n = 4) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ((∃ a b c d : ℕ,
            IsPerm0123 a b c d ∧ HasEdge edges a b ∧ HasEdge edges b c ∧
              HasEdge edges c d) →
          r.val = pathScore4 scores 0 1 2 3) ∧
        (¬ (∃ a b c d : ℕ,
            IsPerm0123 a b c d ∧ HasEdge edges a b ∧ HasEdge edges b c ∧
              HasEdge edges c d) →
          r.val = -1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hn : n = 4), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ((∃ a b c d : ℕ,
            IsPerm0123 a b c d ∧ HasEdge edges a b ∧ HasEdge edges b c ∧
              HasEdge edges c d) →
          r.val = pathScore4 scores 0 1 2 3) ∧
        (¬ (∃ a b c d : ℕ,
            IsPerm0123 a b c d ∧ HasEdge edges a b ∧ HasEdge edges b c ∧
              HasEdge edges c d) →
          r.val = -1)) := by
  sorry

/-- Here an edge is present between two nodes u and v when the unordered pair {u,v} occurs as the two entries of some edges[j]; a valid length-4 node sequence is an ordered tuple of four pairwise distinct indices in [0,n) such that edges are present between each consecutive pair. The function returns a result r. If there exists a valid length-4 node sequence, then r = 4*c; otherwise r = -1.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; c is an integer with 1 <= c <= 100000000 and for every i with 0 <= i < n, scores[i] = c. -/
theorem spec_9 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ) (hc₁ : 1 ≤ c)
    (hc₂ : c ≤ 100000000) (hscores : ∀ i : ℕ, i < n → scoreAt scores i = c) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (HasValidPath4 edges n → r.val = 4 * c) ∧
        (¬ HasValidPath4 edges n → r.val = -1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ) (hc₁ : 1 ≤ c)
    (hc₂ : c ≤ 100000000) (hscores : ∀ i : ℕ, i < n → scoreAt scores i = c), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        (HasValidPath4 edges n → r.val = 4 * c) ∧
        (¬ HasValidPath4 edges n → r.val = -1)) := by
  sorry

/-- Let M be the sum of the four largest values in the multiset {scores[0],...,scores[n-1]}, counting equal values separately. The function returns a result r and r = M.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; for every u,v with 0 <= u < v < n, the unordered pair {u,v} occurs as the two entries of some edges[j]. -/
theorem spec_10 (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n)
    (hcomplete : ∀ u v : ℕ, u < v → v < n → HasEdge edges u v) :
    ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ∃ M : ℤ, IsTopFourSum (scores.val.map (fun x => x.val)) M ∧ r.val = M := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n)
    (hcomplete : ∀ u v : ℕ, u < v → v < n → HasEdge edges u v), ∃ r : Std.I64,
      maximum_score scores edges = ok r ∧
        ∃ M : ℤ, IsTopFourSum (scores.val.map (fun x => x.val)) M ∧ r.val = M) := by
  sorry

/-- Let p be any permutation of the index set {0,...,len(edges)-1} (empty when len(edges)=0), and let edges' be the list of length len(edges) with edges'[i] = edges[p(i)] for every i. The edge list edges' also satisfies the edge constraints above. The function returns a result r when called with (scores,edges) and a result r' when called with (scores,edges'), and r = r'.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_11 (scores : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (p : ℕ → ℕ)
    (hp : IsPermOn edges.val.length p) (hedges' : IsEdgeReindex edges edges' p) :
    ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores edges' = ok r' ∧
        EdgesValid edges' n ∧ r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (p : ℕ → ℕ)
    (hp : IsPermOn edges.val.length p) (hedges' : IsEdgeReindex edges edges' p), ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores edges' = ok r' ∧
        EdgesValid edges' n ∧ r.val = r'.val) := by
  sorry

/-- Let edges' be the list of length len(edges) such that for every j, edges'[j] is the two-element vector with edges'[j][0] = edges[j][1] and edges'[j][1] = edges[j][0]. The edge list edges' also satisfies the edge constraints above. The function returns a result r when called with (scores,edges) and a result r' when called with (scores,edges'), and r = r'.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different. -/
theorem spec_12 (scores : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hedges' : IsEdgeFlipped edges edges') :
    ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores edges' = ok r' ∧
        EdgesValid edges' n ∧ r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (scores : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hedges' : IsEdgeFlipped edges edges'), ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores edges' = ok r' ∧
        EdgesValid edges' n ∧ r.val = r'.val) := by
  sorry

/-- Let scores' be the array of length n with scores'[i] = c * scores[i] for 0 <= i < n. The array scores' also satisfies the score constraints above. The function returns a result r when called with (scores,edges) and a result r' when called with (scores',edges). If r = -1 then r' = -1; if r != -1 then r' = c * r.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; c is an integer with 1 <= c and for every i with 0 <= i < n, 1 <= c * scores[i] <= 100000000. -/
theorem spec_13 (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ) (hc : 1 ≤ c)
    (hbound : ∀ i : ℕ, i < n → 1 ≤ c * scoreAt scores i ∧ c * scoreAt scores i ≤ 100000000)
    (hlen : scores'.val.length = n)
    (hpoint : ∀ i : ℕ, i < n → scoreAt scores' i = c * scoreAt scores i) :
    ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        ScoresValid scores' n ∧ (r.val = -1 → r'.val = -1) ∧
          (r.val ≠ -1 → r'.val = c * r.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ) (hc : 1 ≤ c)
    (hbound : ∀ i : ℕ, i < n → 1 ≤ c * scoreAt scores i ∧ c * scoreAt scores i ≤ 100000000)
    (hlen : scores'.val.length = n)
    (hpoint : ∀ i : ℕ, i < n → scoreAt scores' i = c * scoreAt scores i), ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        ScoresValid scores' n ∧ (r.val = -1 → r'.val = -1) ∧
          (r.val ≠ -1 → r'.val = c * r.val)) := by
  sorry

/-- Let scores' be the array of length n with scores'[i] = scores[i] + c for 0 <= i < n. The array scores' also satisfies the score constraints above. The function returns a result r when called with (scores,edges) and a result r' when called with (scores',edges). If r = -1 then r' = -1; if r != -1 then r' = r + 4 * c.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; c is an integer and for every i with 0 <= i < n, 1 <= scores[i] + c <= 100000000. -/
theorem spec_14 (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ)
    (hbound : ∀ i : ℕ, i < n → 1 ≤ scoreAt scores i + c ∧ scoreAt scores i + c ≤ 100000000)
    (hlen : scores'.val.length = n)
    (hpoint : ∀ i : ℕ, i < n → scoreAt scores' i = scoreAt scores i + c) :
    ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        ScoresValid scores' n ∧ (r.val = -1 → r'.val = -1) ∧
          (r.val ≠ -1 → r'.val = r.val + 4 * c) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (c : ℤ)
    (hbound : ∀ i : ℕ, i < n → 1 ≤ scoreAt scores i + c ∧ scoreAt scores i + c ≤ 100000000)
    (hlen : scores'.val.length = n)
    (hpoint : ∀ i : ℕ, i < n → scoreAt scores' i = scoreAt scores i + c), ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        ScoresValid scores' n ∧ (r.val = -1 → r'.val = -1) ∧
          (r.val ≠ -1 → r'.val = r.val + 4 * c)) := by
  sorry

/-- The function returns a result r when called with (scores,edges) and a result r' when called with (scores',edges). If r = -1 then r' = -1; if r != -1 then r' != -1 and r' >= r.
  Preconditions: n = len(scores); 4 <= n <= 50000; for every i with 0 <= i < n, 1 <= scores[i] <= 100000000; len(edges) <= 50000; for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]; for distinct j,k with 0 <= j < k < len(edges), the unordered pairs {edges[j][0],edges[j][1]} and {edges[k][0],edges[k][1]} are different; scores' is an array of length n such that for every i with 0 <= i < n, 1 <= scores'[i] <= 100000000 and scores'[i] >= scores[i]. -/
theorem spec_15 (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hs' : ScoresValid scores' n)
    (hmono : ∀ i : ℕ, i < n → scoreAt scores i ≤ scoreAt scores' i) :
    ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val ≠ -1 ∧ r.val ≤ r'.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (scores scores' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hs : ScoresValid scores n) (he : EdgesValid edges n) (hs' : ScoresValid scores' n)
    (hmono : ∀ i : ℕ, i < n → scoreAt scores i ≤ scoreAt scores' i), ∃ r r' : Std.I64,
      maximum_score scores edges = ok r ∧ maximum_score scores' edges = ok r' ∧
        (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val ≠ -1 ∧ r.val ≤ r'.val)) := by
  sorry

end AegisSpec.MaximumScore
