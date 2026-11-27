import Aegis.FindTheCity.Code.Funs

/-!
# Specifications of `Aegis.FindTheCity.find_the_city`

LeetCode problem `find-the-city-with-the-smallest-number-of-neighbors-at-a-threshold-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindTheCity

def edgeVectors (edges : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  edges.val.map (fun v => v.val.map (fun x => x.val))

def IsEdgeVector (n : ℤ) (l : List ℤ) : Prop :=
  ∃ a b w : ℤ, l = [a, b, w] ∧ 0 ≤ a ∧ a < b ∧ b < n ∧ 1 ≤ w ∧ w ≤ 10000

def InputOK (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) : Prop :=
  2 ≤ n.val ∧ n.val ≤ 100 ∧
  1 ≤ T.val ∧ T.val ≤ 10000 ∧
  1 ≤ ((edgeVectors edges).length : ℤ) ∧
  ((edgeVectors edges).length : ℤ) ≤ n.val * (n.val - 1) / 2 ∧
  (∀ l ∈ edgeVectors edges, IsEdgeVector n.val l) ∧
  (∀ a b w₁ w₂ : ℤ,
    [a, b, w₁] ∈ edgeVectors edges → [a, b, w₂] ∈ edgeVectors edges → w₁ = w₂)

def HasEdge (E : List (List ℤ)) (a b : ℤ) (w : ℕ) : Prop :=
  [a, b, (w : ℤ)] ∈ E ∨ [b, a, (w : ℤ)] ∈ E

inductive WeightedPath (E : List (List ℤ)) : ℤ → ℤ → ℕ → Prop where
  | nil (u : ℤ) : WeightedPath E u u 0
  | step {u v w : ℤ} {s t : ℕ} :
      HasEdge E u v s → WeightedPath E v w t → WeightedPath E u w (s + t)

noncomputable def shortestDist (E : List (List ℤ)) (u v : ℤ) : ℕ∞ :=
  ⨅ (h : {s : ℕ // WeightedPath E u v s}), ((h : ℕ) : ℕ∞)

noncomputable def count (E : List (List ℤ)) (T : ℤ) (n c : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter
    (fun j => j ≠ c ∧ shortestDist E (c : ℤ) (j : ℤ) ≤ (T.toNat : ℕ∞))).card

noncomputable def degT (E : List (List ℤ)) (T : ℤ) (n c : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter
    (fun b => b ≠ c ∧ ∃ w : ℕ, HasEdge E (c : ℤ) (b : ℤ) w ∧ (w : ℤ) ≤ T)).card

def IsGreatestMin (f : ℕ → ℕ) (n : ℕ) (r : ℤ) : Prop :=
  (∀ c : ℕ, c < n → f r.toNat ≤ f c) ∧
  (∀ c : ℕ, c < n → f c = f r.toNat → (c : ℤ) ≤ r)

/-- Let d(u,v) be the minimum total weight of a finite path from city u to city v in the undirected weighted graph given by edges, with d(u,v)=infinity if no path exists. Let count(c) = |{ j : 0 <= j < n, j != c, d(c,j) <= distanceThreshold }|. The function returns a result r and 0 <= r < n, and for every city c with 0 <= c < n, count(r) <= count(c); moreover, for every city c with count(c)=count(r), c <= r. Equivalently, r is the greatest-indexed city among all cities whose count is minimal.
  Preconditions: n and distanceThreshold are i64 values with 2 <= n <= 100 and 1 <= distanceThreshold <= 10000. edges is a slice of i64 vectors of length m with 1 <= m <= n*(n-1)/2. Each edges[k] has length 3 and equals [a,b,w] with 0 <= a < b < n and 1 <= w <= 10000. All unordered pairs {a,b} occurring in edges are distinct. -/
theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T) :
    ∃ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r ∧
        0 ≤ r.val ∧ r.val < n.val ∧
        IsGreatestMin (count (edgeVectors edges) T.val n.val.toNat) n.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T), ∃ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r ∧
        0 ≤ r.val ∧ r.val < n.val ∧
        IsGreatestMin (count (edgeVectors edges) T.val n.val.toNat) n.val.toNat r.val) := by
  sorry

/-- The function returns a result (it does not fail, panic, overflow, or index out of bounds) on every input satisfying the preconditions.
  Preconditions: n and distanceThreshold are i64 values with 2 <= n <= 100 and 1 <= distanceThreshold <= 10000. edges is a slice of i64 vectors of length m with 1 <= m <= n*(n-1)/2. Each edges[k] has length 3 and equals [a,b,w] with 0 <= a < b < n and 1 <= w <= 10000. All unordered pairs {a,b} occurring in edges are distinct. -/
theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T) :
    ∃ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T), ∃ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r) := by
  sorry

/-- Let count and count' be the counts defined from edges and edges' respectively as in spec_1. Whenever the function returns r on (n, edges, distanceThreshold) and r' on (n, edges', distanceThreshold), we have r = r'.
  Preconditions: Both (n, edges, distanceThreshold) and (n, edges', distanceThreshold) satisfy the constraints listed in spec_1, and edges' is a permutation of edges (the same multiset of three-element vectors). -/
theorem spec_3 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (T : I64)
    (h : InputOK n edges T) (h' : InputOK n edges' T) (hperm : edges.val.Perm edges'.val) :
    ∀ r r' : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        Aegis.FindTheCity.find_the_city n edges' T = ok r' → r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (T : I64)
    (h : InputOK n edges T) (h' : InputOK n edges' T) (hperm : edges.val.Perm edges'.val), ∀ r r' : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        Aegis.FindTheCity.find_the_city n edges' T = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, count(r)=0 and for every city c with 0 <= c < n and count(c)=0, we have c <= r. Thus r is the greatest city with no other city at distance at most distanceThreshold.
  Preconditions: The input satisfies the constraints listed in spec_1. Additionally, at least one city c with 0 <= c < n has count(c)=0, where count is defined from edges and distanceThreshold as in spec_1. -/
theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (h0 : ∃ c : ℕ, c < n.val.toNat ∧ count (edgeVectors edges) T.val n.val.toNat c = 0) :
    ∀ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        count (edgeVectors edges) T.val n.val.toNat r.val.toNat = 0 ∧
          ∀ c : ℕ,
            c < n.val.toNat →
              count (edgeVectors edges) T.val n.val.toNat c = 0 → (c : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (h0 : ∃ c : ℕ, c < n.val.toNat ∧ count (edgeVectors edges) T.val n.val.toNat c = 0), ∀ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        count (edgeVectors edges) T.val n.val.toNat r.val.toNat = 0 ∧
          ∀ c : ℕ,
            c < n.val.toNat →
              count (edgeVectors edges) T.val n.val.toNat c = 0 → (c : ℤ) ≤ r.val) := by
  sorry

/-- For each city c with 0 <= c < n, let degT(c) be the number of cities b with 0 <= b < n, b != c, such that edges contains an edge between c and b whose weight is at most distanceThreshold (i.e. [c,b,w] with w <= distanceThreshold if c < b, or [b,c,w] with w <= distanceThreshold if b < c). Whenever the function returns a result r, r is the greatest-indexed city minimizing degT: for every city c with 0 <= c < n, degT(r) <= degT(c), and for every city c with degT(c)=degT(r), c <= r.
  Preconditions: The input satisfies the constraints listed in spec_1. Additionally, for every edge [a,b,w] appearing in edges, 2*w > distanceThreshold. -/
theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (hT : ∀ l ∈ edgeVectors edges, ∀ a b w : ℤ, l = [a, b, w] → 2 * w > T.val) :
    ∀ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        IsGreatestMin (degT (edgeVectors edges) T.val n.val.toNat) n.val.toNat r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (hT : ∀ l ∈ edgeVectors edges, ∀ a b w : ℤ, l = [a, b, w] → 2 * w > T.val), ∀ r : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        IsGreatestMin (degT (edgeVectors edges) T.val n.val.toNat) n.val.toNat r.val) := by
  sorry

/-- Whenever the function returns r on (n, edges, distanceThreshold) and r' on (n, edges, distanceThreshold'), we have r = r'.
  Preconditions: Both (n, edges, distanceThreshold) and (n, edges, distanceThreshold') satisfy the constraints listed in S1 (so 1 <= distanceThreshold, distanceThreshold' <= 10000), with the same n and the same edge slice. Let d be the shortest-path distance defined from edges as in spec_1. For every pair of cities u,v with 0 <= u < n and 0 <= v < n, d(u,v) <= distanceThreshold if and only if d(u,v) <= distanceThreshold'. -/
theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T T' : I64)
    (h : InputOK n edges T) (h' : InputOK n edges T')
    (hd : ∀ u : ℕ, u < n.val.toNat → ∀ v : ℕ, v < n.val.toNat →
      (shortestDist (edgeVectors edges) (u : ℤ) (v : ℤ) ≤ (T.val.toNat : ℕ∞) ↔
        shortestDist (edgeVectors edges) (u : ℤ) (v : ℤ) ≤ (T'.val.toNat : ℕ∞))) :
    ∀ r r' : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        Aegis.FindTheCity.find_the_city n edges T' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T T' : I64)
    (h : InputOK n edges T) (h' : InputOK n edges T')
    (hd : ∀ u : ℕ, u < n.val.toNat → ∀ v : ℕ, v < n.val.toNat →
      (shortestDist (edgeVectors edges) (u : ℤ) (v : ℤ) ≤ (T.val.toNat : ℕ∞) ↔
        shortestDist (edgeVectors edges) (u : ℤ) (v : ℤ) ≤ (T'.val.toNat : ℕ∞))), ∀ r r' : I64,
      Aegis.FindTheCity.find_the_city n edges T = ok r →
        Aegis.FindTheCity.find_the_city n edges T' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, r = c.
  Preconditions: The input satisfies the constraints listed in spec_1. Additionally, there exists a city c with 0 <= c < n such that for every city d with 0 <= d < n and d != c, count(c) < count(d), where count is defined from edges and distanceThreshold as in spec_1. -/
theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (c : ℕ) (hc : c < n.val.toNat)
    (hmin : ∀ d : ℕ, d < n.val.toNat → d ≠ c →
      count (edgeVectors edges) T.val n.val.toNat c <
        count (edgeVectors edges) T.val n.val.toNat d) :
    ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = (c : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (c : ℕ) (hc : c < n.val.toNat)
    (hmin : ∀ d : ℕ, d < n.val.toNat → d ≠ c →
      count (edgeVectors edges) T.val n.val.toNat c <
        count (edgeVectors edges) T.val n.val.toNat d), ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = (c : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = d.
  Preconditions: The input satisfies the constraints listed in spec_1. Additionally, there exist two cities c and d with 0 <= c < d < n such that count(c)=count(d), and for every city e with 0 <= e < n and e not in {c,d}, count(c) < count(e), where count is defined as in spec_1. -/
theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (c d : ℕ) (hcd : c < d) (hd : d < n.val.toNat)
    (hcount : count (edgeVectors edges) T.val n.val.toNat c =
      count (edgeVectors edges) T.val n.val.toNat d)
    (hmin : ∀ e : ℕ, e < n.val.toNat → e ≠ c → e ≠ d →
      count (edgeVectors edges) T.val n.val.toNat c <
        count (edgeVectors edges) T.val n.val.toNat e) :
    ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = (d : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (c d : ℕ) (hcd : c < d) (hd : d < n.val.toNat)
    (hcount : count (edgeVectors edges) T.val n.val.toNat c =
      count (edgeVectors edges) T.val n.val.toNat d)
    (hmin : ∀ e : ℕ, e < n.val.toNat → e ≠ c → e ≠ d →
      count (edgeVectors edges) T.val n.val.toNat c <
        count (edgeVectors edges) T.val n.val.toNat e), ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = (d : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = n-1.
  Preconditions: The input satisfies the constraints listed in spec_1. Additionally, city n-1 has minimum count: for every city c with 0 <= c < n, count(n-1) <= count(c), where count is defined from edges and distanceThreshold as in spec_1. -/
theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (hmin : ∀ c : ℕ, c < n.val.toNat →
      count (edgeVectors edges) T.val n.val.toNat (n.val.toNat - 1) ≤
        count (edgeVectors edges) T.val n.val.toNat c) :
    ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = n.val - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (T : I64) (h : InputOK n edges T)
    (hmin : ∀ c : ℕ, c < n.val.toNat →
      count (edgeVectors edges) T.val n.val.toNat (n.val.toNat - 1) ≤
        count (edgeVectors edges) T.val n.val.toNat c), ∀ r : I64, Aegis.FindTheCity.find_the_city n edges T = ok r → r.val = n.val - 1) := by
  sorry

end AegisSpec.FindTheCity
