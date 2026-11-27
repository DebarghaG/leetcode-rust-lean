import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-points-tourist-can-earn`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

def rowOf (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  match s.val[i]? with
  | some row => row.val.map (fun v => v.val)
  | none => []

def entry (s : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (rowOf s i)[j]?.getD 0

def maxList (l : List Int) : Int :=
  l.foldl (fun acc x => max acc x) 0

def moveScore (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (day src dst : Nat) : Int :=
  if dst = src then entry stayScore day src else entry travelScore src dst

def journeyScore (stayScore travelScore : Slice (alloc.vec.Vec Std.I64)) (k : Nat)
    (c : Nat → Nat) : Int :=
  ∑ i ∈ Finset.range k, moveScore stayScore travelScore i (c i) (c (i + 1))

def IsJourney (n k : Nat) (c : Nat → Nat) : Prop :=
  ∀ i, i ≤ k → c i < n

def stepBest (stayScore travelScore : Slice (alloc.vec.Vec Std.I64)) (n day : Nat) : Int :=
  maxList ((List.range n).flatMap (fun c =>
    entry stayScore day c ::
      ((List.range n).filter (fun d => d != c)).map (fun d => entry travelScore c d)))

def InputInvariant (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 200 ∧
  1 ≤ k.val ∧ k.val ≤ 200 ∧
  stayScore.val.length = k.val.toNat ∧
  travelScore.val.length = n.val.toNat ∧
  (∀ i, i < k.val.toNat → (rowOf stayScore i).length = n.val.toNat) ∧
  (∀ a, a < n.val.toNat → (rowOf travelScore a).length = n.val.toNat) ∧
  (∀ i j, i < k.val.toNat → j < n.val.toNat →
    1 ≤ entry stayScore i j ∧ entry stayScore i j ≤ 100) ∧
  (∀ a b, a < n.val.toNat → b < n.val.toNat →
    0 ≤ entry travelScore a b ∧ entry travelScore a b ≤ 100) ∧
  (∀ a, a < n.val.toNat → entry travelScore a a = 0)

/-- Define a journey to be a sequence c_0, c_1, ..., c_k of cities with 0 <= c_i < n for every i with 0 <= i <= k. Its score is the sum over i = 0,...,k-1 of stayScore[i][c_i] if c_{i+1} = c_i, and travelScore[c_i][c_{i+1}] if c_{i+1} != c_i. The function returns a result r and r is the maximum score over all journeys.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_1 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      (∀ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c →
        journeyScore stayScore travelScore k.val.toNat c ≤ r.val) ∧
      (∃ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c ∧
        journeyScore stayScore travelScore k.val.toNat c = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      (∀ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c →
        journeyScore stayScore travelScore k.val.toNat c ≤ r.val) ∧
      (∃ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c ∧
        journeyScore stayScore travelScore k.val.toNat c = r.val)) := by
  sorry

/-- The function returns a result r; it does not panic, perform an out-of-bounds access, or overflow i64.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_2 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64, Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64, Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r) := by
  sorry

/-- The function returns a result r and k <= r <= 100*k.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_3 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      k.val ≤ r.val ∧ r.val ≤ 100 * k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      k.val ≤ r.val ∧ r.val ≤ 100 * k.val) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{k-1} stayScore[i][0].
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. Also n = 1. All indices are 0-based. -/
theorem spec_4 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hn : n.val = 1) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val = ∑ i ∈ Finset.range k.val.toNat, entry stayScore i 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hn : n.val = 1), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val = ∑ i ∈ Finset.range k.val.toNat, entry stayScore i 0) := by
  sorry

/-- The function returns a result r and r = max( { stayScore[0][j] | 0 <= j < n } union { travelScore[a][b] | 0 <= a < n, 0 <= b < n, a != b } ). If n = 1, the second set is empty.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. Also k = 1. All indices are 0-based. -/
theorem spec_5 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hk : k.val = 1) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      (∀ j, j < n.val.toNat → entry stayScore 0 j ≤ r.val) ∧
      (∀ a b, a < n.val.toNat → b < n.val.toNat → a ≠ b →
        entry travelScore a b ≤ r.val) ∧
      ((∃ j, j < n.val.toNat ∧ entry stayScore 0 j = r.val) ∨
        (∃ a b, a < n.val.toNat ∧ b < n.val.toNat ∧ a ≠ b ∧
          entry travelScore a b = r.val)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hk : k.val = 1), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      (∀ j, j < n.val.toNat → entry stayScore 0 j ≤ r.val) ∧
      (∀ a b, a < n.val.toNat → b < n.val.toNat → a ≠ b →
        entry travelScore a b ≤ r.val) ∧
      ((∃ j, j < n.val.toNat ∧ entry stayScore 0 j = r.val) ∨
        (∃ a b, a < n.val.toNat ∧ b < n.val.toNat ∧ a ≠ b ∧
          entry travelScore a b = r.val))) := by
  sorry

/-- The function returns a result r and for every city c with 0 <= c < n, r >= sum_{i=0}^{k-1} stayScore[i][c].
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_6 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ c, c < n.val.toNat →
        (∑ i ∈ Finset.range k.val.toNat, entry stayScore i c) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ c, c < n.val.toNat →
        (∑ i ∈ Finset.range k.val.toNat, entry stayScore i c) ≤ r.val) := by
  sorry

/-- The function returns a result r and r >= max_{0 <= a < n, 0 <= b < n, a != b} ( travelScore[a][b] + (k-1) ).
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. Also n >= 2. All indices are 0-based. -/
theorem spec_7 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hn : 2 ≤ n.val) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ a b, a < n.val.toNat → b < n.val.toNat → a ≠ b →
        entry travelScore a b + (k.val - 1) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) (hn : 2 ≤ n.val), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ a b, a < n.val.toNat → b < n.val.toNat → a ≠ b →
        entry travelScore a b + (k.val - 1) ≤ r.val) := by
  sorry

/-- Let r = max_score(n,k,stayScore,travelScore) and r2 = max_score(n,k,stayScore2,travelScore2). The function returns r and r2, and r <= r2.
  Preconditions: Let P(n,k,stayScore,travelScore) mean: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. Both P(n,k,stayScore,travelScore) and P(n,k,stayScore2,travelScore2) hold. Also stayScore[i][j] <= stayScore2[i][j] for every 0 <= i < k and 0 <= j < n, and travelScore[a][b] <= travelScore2[a][b] for every 0 <= a < n and 0 <= b < n. All indices are 0-based. -/
theorem spec_8 (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore i j ≤ entry stayScore2 i j)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore a b ≤ entry travelScore2 a b) :
    ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore i j ≤ entry stayScore2 i j)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore a b ≤ entry travelScore2 a b), ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r.val ≤ r2.val) := by
  sorry

/-- Let r1 = max_score(n,k1,stayScore1,travelScore1) and r2 = max_score(n,k2,stayScore2,travelScore2). The function returns r1 and r2, and r2 >= r1.
  Preconditions: Let P(n,k,stayScore,travelScore) mean: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. Both P(n,k1,stayScore1,travelScore1) and P(n,k2,stayScore2,travelScore2) hold. Also k2 >= k1, travelScore1[a][b] = travelScore2[a][b] for every 0 <= a < n and 0 <= b < n, and stayScore1[i][j] = stayScore2[i][j] for every 0 <= i < k1 and 0 <= j < n. All indices are 0-based. -/
theorem spec_9 (n k1 k2 : Std.I64)
    (stayScore1 travelScore1 stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : InputInvariant n k1 stayScore1 travelScore1)
    (h2 : InputInvariant n k2 stayScore2 travelScore2)
    (hk : k1.val ≤ k2.val)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore1 a b = entry travelScore2 a b)
    (hstay : ∀ i j, i < k1.val.toNat → j < n.val.toNat →
      entry stayScore1 i j = entry stayScore2 i j) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaxScore.max_score n k1 stayScore1 travelScore1 = Result.ok r1 ∧
      Aegis.MaxScore.max_score n k2 stayScore2 travelScore2 = Result.ok r2 ∧
      r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k1 k2 : Std.I64)
    (stayScore1 travelScore1 stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : InputInvariant n k1 stayScore1 travelScore1)
    (h2 : InputInvariant n k2 stayScore2 travelScore2)
    (hk : k1.val ≤ k2.val)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore1 a b = entry travelScore2 a b)
    (hstay : ∀ i j, i < k1.val.toNat → j < n.val.toNat →
      entry stayScore1 i j = entry stayScore2 i j), ∃ r1 r2 : Std.I64,
      Aegis.MaxScore.max_score n k1 stayScore1 travelScore1 = Result.ok r1 ∧
      Aegis.MaxScore.max_score n k2 stayScore2 travelScore2 = Result.ok r2 ∧
      r1.val ≤ r2.val) := by
  sorry

/-- Let r = max_score(n,k,stayScore,travelScore) and r2 = max_score(n,k,stayScore2,travelScore2). The function returns r and r2, and r2 = r.
  Preconditions: Let P(n,k,stayScore,travelScore) mean: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. P(n,k,stayScore,travelScore) holds. Let pi be a permutation of {0,...,n-1}. Define stayScore2[i][j] = stayScore[i][pi(j)] for every 0 <= i < k and 0 <= j < n, and travelScore2[a][b] = travelScore[pi(a)][pi(b)] for every 0 <= a < n and 0 <= b < n. Then P(n,k,stayScore2,travelScore2) also holds. All indices are 0-based. -/
theorem spec_10 (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (pi : Nat → Nat)
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hpi : ∀ a, a < n.val.toNat → pi a < n.val.toNat)
    (hpi_inj : ∀ a b, a < n.val.toNat → b < n.val.toNat → pi a = pi b → a = b)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore2 i j = entry stayScore i (pi j))
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore2 a b = entry travelScore (pi a) (pi b)) :
    ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r2.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (pi : Nat → Nat)
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hpi : ∀ a, a < n.val.toNat → pi a < n.val.toNat)
    (hpi_inj : ∀ a b, a < n.val.toNat → b < n.val.toNat → pi a = pi b → a = b)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore2 i j = entry stayScore i (pi j))
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore2 a b = entry travelScore (pi a) (pi b)), ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r2.val = r.val) := by
  sorry

/-- Let r = max_score(n,k,stayScore,travelScore) and r2 = max_score(n,k,stayScore2,travelScore2). The function returns r and r2, and r2 = c * r.
  Preconditions: Let P(n,k,stayScore,travelScore) mean: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. P(n,k,stayScore,travelScore) holds. Let c be a positive integer. Define stayScore2[i][j] = c * stayScore[i][j] and travelScore2[a][b] = c * travelScore[a][b]. Assume P(n,k,stayScore2,travelScore2) holds. All indices are 0-based. -/
theorem spec_11 (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (c : Nat) (hc : 0 < c)
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore2 i j = (c : Int) * entry stayScore i j)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore2 a b = (c : Int) * entry travelScore a b) :
    ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r2.val = (c : Int) * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : Std.I64)
    (stayScore travelScore stayScore2 travelScore2 : Slice (alloc.vec.Vec Std.I64))
    (c : Nat) (hc : 0 < c)
    (h : InputInvariant n k stayScore travelScore)
    (h2 : InputInvariant n k stayScore2 travelScore2)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore2 i j = (c : Int) * entry stayScore i j)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat →
      entry travelScore2 a b = (c : Int) * entry travelScore a b), ∃ r r2 : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      Aegis.MaxScore.max_score n k stayScore2 travelScore2 = Result.ok r2 ∧
      r2.val = (c : Int) * r.val) := by
  sorry

/-- The function returns a result r and there exist cities c_0, c_1, ..., c_k with 0 <= c_i < n for every 0 <= i <= k such that r = sum_{i=0}^{k-1} g_i, where g_i = stayScore[i][c_i] if c_{i+1} = c_i, and g_i = travelScore[c_i][c_{i+1}] if c_{i+1} != c_i.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_12 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∃ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c ∧
        journeyScore stayScore travelScore k.val.toNat c = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∃ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c ∧
        journeyScore stayScore travelScore k.val.toNat c = r.val) := by
  sorry

/-- The function returns a result r and for every sequence c_0, c_1, ..., c_k of cities with 0 <= c_i < n for every 0 <= i <= k, if g_i = stayScore[i][c_i] when c_{i+1} = c_i and g_i = travelScore[c_i][c_{i+1}] when c_{i+1} != c_i, then sum_{i=0}^{k-1} g_i <= r.
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_13 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c →
        journeyScore stayScore travelScore k.val.toNat c ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      ∀ c : Nat → Nat, IsJourney n.val.toNat k.val.toNat c →
        journeyScore stayScore travelScore k.val.toNat c ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{k-1} B_i, where for each i with 0 <= i < k, B_i = max_{0 <= c < n} max( stayScore[i][c], max_{0 <= d < n, d != c} travelScore[c][d] ), with the inner maximum over d != c omitted when n = 1 (so B_i = stayScore[i][0]).
  Preconditions: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. All indices are 0-based. -/
theorem spec_14 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val ≤ ∑ i ∈ Finset.range k.val.toNat,
        stepBest stayScore travelScore n.val.toNat i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val ≤ ∑ i ∈ Finset.range k.val.toNat,
        stepBest stayScore travelScore n.val.toNat i) := by
  sorry

/-- The function returns a result r and r = sum_{i=0}^{k-1} stayScore[i][c0].
  Preconditions: Let P(n,k,stayScore,travelScore) mean: 1 <= n <= 200, 1 <= k <= 200, len(stayScore) = k, len(travelScore) = n, len(stayScore[i]) = n for every 0 <= i < k, len(travelScore[a]) = n for every 0 <= a < n, 1 <= stayScore[i][j] <= 100 for every 0 <= i < k and 0 <= j < n, 0 <= travelScore[a][b] <= 100 for every 0 <= a < n and 0 <= b < n, and travelScore[a][a] = 0 for every 0 <= a < n. P(n,k,stayScore,travelScore) holds. Also travelScore[a][b] = 0 for every 0 <= a < n and 0 <= b < n, and there exists a city c0 with 0 <= c0 < n such that stayScore[i][j] <= stayScore[i][c0] for every 0 <= i < k and 0 <= j < n. All indices are 0-based. -/
theorem spec_15 (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore)
    (c0 : Nat) (hc0 : c0 < n.val.toNat)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat → entry travelScore a b = 0)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore i j ≤ entry stayScore i c0) :
    ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val = ∑ i ∈ Finset.range k.val.toNat, entry stayScore i c0 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n k : Std.I64) (stayScore travelScore : Slice (alloc.vec.Vec Std.I64))
    (h : InputInvariant n k stayScore travelScore)
    (c0 : Nat) (hc0 : c0 < n.val.toNat)
    (htravel : ∀ a b, a < n.val.toNat → b < n.val.toNat → entry travelScore a b = 0)
    (hstay : ∀ i j, i < k.val.toNat → j < n.val.toNat →
      entry stayScore i j ≤ entry stayScore i c0), ∃ r : Std.I64,
      Aegis.MaxScore.max_score n k stayScore travelScore = Result.ok r ∧
      r.val = ∑ i ∈ Finset.range k.val.toNat, entry stayScore i c0) := by
  sorry

end AegisSpec.MaxScore
