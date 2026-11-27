import Aegis.PossibleBipartition.Code.Funs

/-!
# Specifications of `Aegis.PossibleBipartition.possible_bipartition`

LeetCode problem `possible-bipartition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PossibleBipartition

  def entries (dislikes : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    dislikes.val.map (fun v => v.val.map (fun x => x.val))

  def Constraints (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ n ∧ n ≤ 2000 ∧
    dislikes.val.length ≤ 10000 ∧
    (∀ e ∈ entries dislikes, e.length = 2) ∧
    (∀ e ∈ entries dislikes, ∃ a b : ℤ, e = [a, b] ∧ 1 ≤ a ∧ a < b ∧ b ≤ n) ∧
    (entries dislikes).Nodup

  def PairOccurs (dislikes : Slice (alloc.vec.Vec I64)) (a b : ℤ) : Prop :=
    ∃ e ∈ entries dislikes, e = [a, b] ∨ e = [b, a]

  def IsEndpoint (dislikes : Slice (alloc.vec.Vec I64)) (x : ℤ) : Prop :=
    ∃ e ∈ entries dislikes, ∃ y : ℤ, e = [x, y] ∨ e = [y, x]

  def CycleOfLength (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) (k : ℕ) : Prop :=
    3 ≤ k ∧ ∃ v : ℕ → ℤ,
      (∀ j : ℕ, j < k → 1 ≤ v j ∧ v j ≤ n) ∧
      (∀ i : ℕ, i < k → ∀ j : ℕ, j < k → v i = v j → i = j) ∧
      (∀ j : ℕ, j < k → PairOccurs dislikes (v j) (v ((j + 1) % k)))

  def HasCycle (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ k : ℕ, CycleOfLength n dislikes k

  def HasOddCycle (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ k : ℕ, Odd k ∧ CycleOfLength n dislikes k

  def IsTwoColoring (n : ℤ) (c : ℤ → ℤ) : Prop :=
    ∀ x : ℤ, 1 ≤ x → x ≤ n → c x = 0 ∨ c x = 1

  def IsValidSplit (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) (c : ℤ → ℤ) : Prop :=
    IsTwoColoring n c ∧
      ∀ e ∈ entries dislikes, ∀ a b : ℤ, e = [a, b] → c a ≠ c b

  def Bipartite (n : ℤ) (dislikes : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ c : ℤ → ℤ, IsValidSplit n dislikes c

  /-- Whenever possible_bipartition n dislikes returns a result r, r = true if and only if there exists a function c from {1,...,n} to {0,1} such that for every i with 0 <= i < len(dislikes), c(dislikes[i][0]) != c(dislikes[i][1]).
    Preconditions: n and dislikes satisfy the problem constraints: 1 <= n <= 2000; 0 <= len(dislikes) <= 10000; every dislikes[i] has length 2; for every i with 0 <= i < len(dislikes), 1 <= dislikes[i][0] < dislikes[i][1] <= n; and all ordered pairs (dislikes[i][0], dislikes[i][1]) are pairwise distinct. -/
  theorem spec_1 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) :
      ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
        (r = true ↔ Bipartite n.val dislikes) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes), ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
          (r = true ↔ Bipartite n.val dislikes)) := by
    sorry

  /-- The function possible_bipartition n dislikes returns a result r; in particular, it does not fail by overflow, out-of-bounds indexing, or panic on any input satisfying the constraints.
    Preconditions: n and dislikes satisfy the problem constraints: 1 <= n <= 2000; 0 <= len(dislikes) <= 10000; every dislikes[i] has length 2; for every i with 0 <= i < len(dislikes), 1 <= dislikes[i][0] < dislikes[i][1] <= n; and all ordered pairs (dislikes[i][0], dislikes[i][1]) are pairwise distinct. -/
  theorem spec_2 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) :
      ∃ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes), ∃ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns a result r, r = false.
    Preconditions: n and dislikes satisfy the problem constraints, and there exist an odd integer k >= 3 and pairwise distinct labels v_0,...,v_{k-1} in {1,...,n} such that for every j with 0 <= j < k, the unordered pair {v_j, v_{(j+1) mod k}} occurs among the dislike pairs. -/
  theorem spec_3 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) (hcyc : HasOddCycle n.val dislikes) :
      ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes) (hcyc : HasOddCycle n.val dislikes), ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r → r = false) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns a result r and r = false, there exist an odd integer k >= 3 and pairwise distinct labels v_0,...,v_{k-1} in {1,...,n} such that for every j with 0 <= j < k, the unordered pair {v_j, v_{(j+1) mod k}} occurs among the dislike pairs.
    Preconditions: n and dislikes satisfy the problem constraints. -/
  theorem spec_4 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) :
      ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r → r = false →
        HasOddCycle n.val dislikes := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes), ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r → r = false →
          HasOddCycle n.val dislikes) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: n and dislikes satisfy the problem constraints, and the undirected graph G with vertex set {1,...,n} and an edge between a and b exactly when some dislike pair equals {a,b} contains no cycle of length at least 3. -/
  theorem spec_5 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) (hforest : ¬ HasCycle n.val dislikes) :
      ∃ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes) (hforest : ¬ HasCycle n.val dislikes), ∃ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r ∧ r = true) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns a result r and possible_bipartition n dislikes' returns a result r', we have r = r'.
    Preconditions: n, dislikes, and dislikes' all satisfy the problem constraints over the same n, and dislikes' is a permutation of dislikes (the same multiset of ordered pairs, possibly in a different order). -/
  theorem spec_6 (n : I64) (dislikes dislikes' : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) (h' : Constraints n.val dislikes')
      (hperm : (entries dislikes').Perm (entries dislikes)) :
      ∀ r r' : Bool,
        Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
        Aegis.PossibleBipartition.possible_bipartition n dislikes' = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (dislikes dislikes' : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes) (h' : Constraints n.val dislikes')
        (hperm : (entries dislikes').Perm (entries dislikes)), ∀ r r' : Bool,
          Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
          Aegis.PossibleBipartition.possible_bipartition n dislikes' = ok r' → r = r') := by
    sorry

  /-- Whenever possible_bipartition n1 dislikes returns a result r1 and possible_bipartition n2 dislikes returns a result r2, we have r1 = r2.
    Preconditions: 1 <= n1 <= n2 <= 2000, and dislikes satisfies the problem constraints with n = n1; hence dislikes also satisfies the problem constraints with n = n2 because all its entries lie in 1..n1. -/
  theorem spec_7 (n1 n2 : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n1.val dislikes) (h12 : n1.val ≤ n2.val) (h2 : n2.val ≤ 2000) :
      ∀ r1 r2 : Bool,
        Aegis.PossibleBipartition.possible_bipartition n1 dislikes = ok r1 →
        Aegis.PossibleBipartition.possible_bipartition n2 dislikes = ok r2 → r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n1 n2 : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n1.val dislikes) (h12 : n1.val ≤ n2.val) (h2 : n2.val ≤ 2000), ∀ r1 r2 : Bool,
          Aegis.PossibleBipartition.possible_bipartition n1 dislikes = ok r1 →
          Aegis.PossibleBipartition.possible_bipartition n2 dislikes = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns a result r and possible_bipartition n dislikes' returns a result r', if r = true then r' = true.
    Preconditions: n, dislikes, and dislikes' satisfy the problem constraints, and every dislike pair of dislikes' also occurs as a dislike pair of dislikes (so dislikes' has a subset of the edges of dislikes). -/
  theorem spec_8 (n : I64) (dislikes dislikes' : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) (h' : Constraints n.val dislikes')
      (hsub : ∀ e ∈ entries dislikes', e ∈ entries dislikes) :
      ∀ r r' : Bool,
        Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
        Aegis.PossibleBipartition.possible_bipartition n dislikes' = ok r' →
        r = true → r' = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (dislikes dislikes' : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes) (h' : Constraints n.val dislikes')
        (hsub : ∀ e ∈ entries dislikes', e ∈ entries dislikes), ∀ r r' : Bool,
          Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
          Aegis.PossibleBipartition.possible_bipartition n dislikes' = ok r' →
          r = true → r' = true) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns r, possible_bipartition n dislikes1 returns r1, and possible_bipartition n dislikes2 returns r2, we have r = true if and only if (r1 = true and r2 = true).
    Preconditions: n, dislikes, dislikes1, and dislikes2 satisfy the problem constraints; no person label occurs as an endpoint in both dislikes1 and dislikes2; and dislikes is a permutation of the concatenation of dislikes1 and dislikes2 (the dislike pairs of dislikes are exactly the disjoint union of those of dislikes1 and dislikes2). -/
  theorem spec_9 (n : I64)
      (dislikes dislikes1 dislikes2 : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) (h1 : Constraints n.val dislikes1)
      (h2 : Constraints n.val dislikes2)
      (hdisj : ∀ x : ℤ, ¬ (IsEndpoint dislikes1 x ∧ IsEndpoint dislikes2 x))
      (hcat : (entries dislikes).Perm (entries dislikes1 ++ entries dislikes2)) :
      ∀ r r1 r2 : Bool,
        Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
        Aegis.PossibleBipartition.possible_bipartition n dislikes1 = ok r1 →
        Aegis.PossibleBipartition.possible_bipartition n dislikes2 = ok r2 →
        (r = true ↔ (r1 = true ∧ r2 = true)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64)
        (dislikes dislikes1 dislikes2 : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes) (h1 : Constraints n.val dislikes1)
        (h2 : Constraints n.val dislikes2)
        (hdisj : ∀ x : ℤ, ¬ (IsEndpoint dislikes1 x ∧ IsEndpoint dislikes2 x))
        (hcat : (entries dislikes).Perm (entries dislikes1 ++ entries dislikes2)), ∀ r r1 r2 : Bool,
          Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
          Aegis.PossibleBipartition.possible_bipartition n dislikes1 = ok r1 →
          Aegis.PossibleBipartition.possible_bipartition n dislikes2 = ok r2 →
          (r = true ↔ (r1 = true ∧ r2 = true))) := by
    sorry

  /-- Whenever possible_bipartition n dislikes returns a result r with r = true, there exists a valid split c : {1,...,n} -> {0,1} (meaning c(dislikes[i][0]) != c(dislikes[i][1]) for every dislike pair), and for every such valid split c, every two labels u and v in {1,...,n}, every integer L >= 0, and every sequence u = w_0, w_1, ..., w_L = v of labels such that for each j with 0 <= j < L the unordered pair {w_j, w_{j+1}} occurs among the dislike pairs, we have: if L is odd then c(u) != c(v), and if L is even then c(u) = c(v).
    Preconditions: n and dislikes satisfy the problem constraints. -/
  theorem spec_10 (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
      (h : Constraints n.val dislikes) :
      ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
        r = true →
        (∃ c : ℤ → ℤ, IsValidSplit n.val dislikes c) ∧
          ∀ c : ℤ → ℤ, IsValidSplit n.val dislikes c →
            ∀ (u v : ℤ) (L : ℕ) (w : ℕ → ℤ),
              1 ≤ u → u ≤ n.val → 1 ≤ v → v ≤ n.val →
              w 0 = u → w L = v →
              (∀ j : ℕ, j < L → PairOccurs dislikes (w j) (w (j + 1))) →
              ((Odd L → c u ≠ c v) ∧ (Even L → c u = c v)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (dislikes : Slice (alloc.vec.Vec I64))
        (h : Constraints n.val dislikes), ∀ r : Bool, Aegis.PossibleBipartition.possible_bipartition n dislikes = ok r →
          r = true →
          (∃ c : ℤ → ℤ, IsValidSplit n.val dislikes c) ∧
            ∀ c : ℤ → ℤ, IsValidSplit n.val dislikes c →
              ∀ (u v : ℤ) (L : ℕ) (w : ℕ → ℤ),
                1 ≤ u → u ≤ n.val → 1 ≤ v → v ≤ n.val →
                w 0 = u → w L = v →
                (∀ j : ℕ, j < L → PairOccurs dislikes (w j) (w (j + 1))) →
                ((Odd L → c u ≠ c v) ∧ (Even L → c u = c v))) := by
    sorry

  end AegisSpec.PossibleBipartition
