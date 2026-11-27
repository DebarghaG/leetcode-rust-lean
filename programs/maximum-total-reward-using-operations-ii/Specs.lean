import Aegis.MaxTotalReward.Code.Funs

/-!
# Specifications of `Aegis.MaxTotalReward.max_total_reward`

LeetCode problem `maximum-total-reward-using-operations-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxTotalReward

namespace AegisSpec.MaxTotalReward

def values (rv : Slice Std.I64) : List ℤ := rv.val.map (fun x => x.val)

def ValidInput (rv : Slice Std.I64) : Prop :=
  1 ≤ rv.val.length ∧ rv.val.length ≤ 50000 ∧
    ∀ i : Fin rv.val.length, 1 ≤ (rv.val.get i).val ∧ (rv.val.get i).val ≤ 50000

def listMax (l : List ℤ) : ℤ := l.foldr max 0

def maxBelow (l : List ℤ) (M : ℤ) : ℤ := listMax (l.filter (fun v => v < M))

def distinctSum (l : List ℤ) : ℤ := l.toFinset.sum (fun v => v)

def prefixSum {n : ℕ} (vals : List ℤ) (idx : Fin n → Fin vals.length) (t : Fin n) : ℤ :=
  (Finset.univ.filter (fun p : Fin n => p < t)).sum (fun p => vals.get (idx p))

def totalSum {n : ℕ} (vals : List ℤ) (idx : Fin n → Fin vals.length) : ℤ :=
  Finset.univ.sum (fun t : Fin n => vals.get (idx t))

def AchievableSum (vals : List ℤ) (s : ℤ) : Prop :=
  ∃ (k : ℕ) (idx : Fin k → Fin vals.length),
    Function.Injective idx ∧
      (∀ t : Fin k, vals.get (idx t) > prefixSum vals idx t) ∧
      s = totalSum vals idx

def IsRewardChain (vals : List ℤ) (k : ℕ) (idx : Fin (k + 1) → Fin vals.length) : Prop :=
  Function.Injective idx ∧
    ∀ t : Fin (k + 1), vals.get (idx t) > prefixSum vals idx t

def IsInserted (l l' : List ℤ) (v : ℤ) : Prop :=
  ∃ k : ℕ, k ≤ l.length ∧ l' = l.take k ++ v :: l.drop k

def IsAscendingDistinctValues (vals cs : List ℤ) : Prop :=
  cs.Pairwise (· < ·) ∧ cs.toFinset = vals.toFinset

/-- The function returns a result r, and r is the maximum total reward in the following exact sense. Let A be the set of all integers s for which there exist an integer k with 0 <= k <= len(rewardValues) and pairwise distinct indices i_0, ..., i_{k-1} in [0, len(rewardValues)) such that, for every t with 0 <= t < k, rewardValues[i_t] > sum_{p=0}^{t-1} rewardValues[i_p], and s = sum_{t=0}^{k-1} rewardValues[i_t]. Then r is an element of A and s <= r for every s in A. Indices are 0-based; the empty choice k = 0 is allowed and has sum 0, and every empty sum above is 0.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_1 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧
      AchievableSum (values rv) r.val ∧
      ∀ s : ℤ, AchievableSum (values rv) s → s ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧
      AchievableSum (values rv) r.val ∧
      ∀ s : ℤ, AchievableSum (values rv) s → s ≤ r.val) := by
  sorry

/-- For every rewardValues satisfying the preconditions, the function returns a result r; it does not fail.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_2 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r) := by
  sorry

/-- The returned value r satisfies r >= max_{0 <= i < len(rewardValues)} rewardValues[i].
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_3 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧ listMax (values rv) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧ listMax (values rv) ≤ r.val) := by
  sorry

/-- Let D be the set of distinct integers that occur as entries of rewardValues, that is, D = { v | there exists i with 0 <= i < len(rewardValues) and rewardValues[i] = v }. Then r <= sum_{v in D} v.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_4 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧ r.val ≤ distinctSum (values rv) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧ r.val ≤ distinctSum (values rv)) := by
  sorry

/-- Let M = max_{0 <= i < len(rewardValues)} rewardValues[i]. Then r <= 2*M - 1.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_5 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧ r.val ≤ 2 * listMax (values rv) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧ r.val ≤ 2 * listMax (values rv) - 1) := by
  sorry

/-- r = rewardValues[0].
  Preconditions: 1 <= len(rewardValues) <= 50000, for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000, and len(rewardValues) = 1. -/
theorem spec_6 (rv : Slice Std.I64) (hrv : ValidInput rv) (hlen : rv.val.length = 1) :
    ∃ r, max_total_reward rv = ok r ∧ r.val = (rv.val.get ⟨0, by omega⟩).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv) (hlen : rv.val.length = 1), ∃ r, max_total_reward rv = ok r ∧ r.val = (rv.val.get ⟨0, by omega⟩).val) := by
  sorry

/-- Let M = max_{0 <= i < len(rewardValues)} rewardValues[i]. Then r = M if and only if for every i with 0 <= i < len(rewardValues), rewardValues[i] = M.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_7 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧
      (r.val = listMax (values rv) ↔
        ∀ i : Fin rv.val.length, (rv.val.get i).val = listMax (values rv)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧
      (r.val = listMax (values rv) ↔
        ∀ i : Fin rv.val.length, (rv.val.get i).val = listMax (values rv))) := by
  sorry

/-- Let M = max_{0 <= i < len(rewardValues)} rewardValues[i], and let L = max{ rewardValues[i] | 0 <= i < len(rewardValues) and rewardValues[i] < M }. Then r >= M + L.
  Preconditions: 1 <= len(rewardValues) <= 50000, for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000, and there exists an index i with rewardValues[i] < max_{0 <= j < len(rewardValues)} rewardValues[j]. -/
theorem spec_8 (rv : Slice Std.I64) (hrv : ValidInput rv)
    (h : ∃ i : Fin rv.val.length, (rv.val.get i).val < listMax (values rv)) :
    ∃ r, max_total_reward rv = ok r ∧
      listMax (values rv) + maxBelow (values rv) (listMax (values rv)) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv)
    (h : ∃ i : Fin rv.val.length, (rv.val.get i).val < listMax (values rv)), ∃ r, max_total_reward rv = ok r ∧
      listMax (values rv) + maxBelow (values rv) (listMax (values rv)) ≤ r.val) := by
  sorry

/-- If r is the result for rewardValues and r' is the result for otherRewards, then r' >= r.
  Preconditions: rewardValues and otherRewards both satisfy 1 <= len <= 50000 and all their entries lie in [1, 50000], and otherRewards is obtained from rewardValues by inserting one additional entry v with 1 <= v <= 50000, so len(otherRewards) = len(rewardValues) + 1. -/
theorem spec_9 (rv other : Slice Std.I64) (hrv : ValidInput rv) (hother : ValidInput other)
    (hins : ∃ v : Std.I64, 1 ≤ v.val ∧ v.val ≤ 50000 ∧ IsInserted (values rv) (values other) v.val) :
    ∀ r r', max_total_reward rv = ok r → max_total_reward other = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rv other : Slice Std.I64) (hrv : ValidInput rv) (hother : ValidInput other)
    (hins : ∃ v : Std.I64, 1 ≤ v.val ∧ v.val ≤ 50000 ∧ IsInserted (values rv) (values other) v.val), ∀ r r', max_total_reward rv = ok r → max_total_reward other = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If r is the result for rewardValues and r_perm is the result for perm, then r = r_perm.
  Preconditions: rewardValues and perm both satisfy 1 <= len <= 50000 and all their entries lie in [1, 50000], and perm is a reordering of rewardValues: len(perm) = len(rewardValues) and there is a bijection f from {0, ..., len(rewardValues)-1} to itself such that perm[j] = rewardValues[f(j)] for every j with 0 <= j < len(rewardValues). -/
theorem spec_10 (rv perm : Slice Std.I64) (hrv : ValidInput rv) (hperm : ValidInput perm)
    (hlen : perm.val.length = rv.val.length)
    (hbij : ∃ f : Fin rv.val.length → Fin rv.val.length,
      Function.Bijective f ∧
        ∀ j : Fin perm.val.length, perm.val.get j = rv.val.get (f (Fin.cast hlen j))) :
    ∀ r rp, max_total_reward rv = ok r → max_total_reward perm = ok rp → r.val = rp.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rv perm : Slice Std.I64) (hrv : ValidInput rv) (hperm : ValidInput perm)
    (hlen : perm.val.length = rv.val.length)
    (hbij : ∃ f : Fin rv.val.length → Fin rv.val.length,
      Function.Bijective f ∧
        ∀ j : Fin perm.val.length, perm.val.get j = rv.val.get (f (Fin.cast hlen j))), ∀ r rp, max_total_reward rv = ok r → max_total_reward perm = ok rp → r.val = rp.val) := by
  sorry

/-- If r is the result for rewardValues and r2 is the result for rewardValues2, then r = r2.
  Preconditions: rewardValues satisfies 1 <= len(rewardValues) <= 50000 and all entries lie in [1, 50000]; there exist distinct indices p and q with rewardValues[p] = rewardValues[q]; rewardValues2 satisfies 1 <= len(rewardValues2) <= 50000 and all entries lie in [1, 50000], and rewardValues2 is obtained from rewardValues by deleting exactly one occurrence of that repeated value, keeping all other entries in their original order. -/
theorem spec_11 (rv rv2 : Slice Std.I64) (hrv : ValidInput rv) (hrv2 : ValidInput rv2)
    (hdel : ∃ p q : Fin rv.val.length, p ≠ q ∧ (rv.val.get p).val = (rv.val.get q).val ∧
      rv2.val = rv.val.eraseIdx p.val) :
    ∀ r r2, max_total_reward rv = ok r → max_total_reward rv2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rv rv2 : Slice Std.I64) (hrv : ValidInput rv) (hrv2 : ValidInput rv2)
    (hdel : ∃ p q : Fin rv.val.length, p ≠ q ∧ (rv.val.get p).val = (rv.val.get q).val ∧
      rv2.val = rv.val.eraseIdx p.val), ∀ r r2, max_total_reward rv = ok r → max_total_reward rv2 = ok r2 → r.val = r2.val) := by
  sorry

/-- There exists a subset S of {0, 1, ..., len(rewardValues)-1} such that sum_{i in S} rewardValues[i] = r and, for all i and j in S with i != j, rewardValues[i] != rewardValues[j].
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_12 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧
      ∃ S : Finset (Fin rv.val.length),
        S.sum (fun i => (rv.val.get i).val) = r.val ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rv.val.get i).val ≠ (rv.val.get j).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧
      ∃ S : Finset (Fin rv.val.length),
        S.sum (fun i => (rv.val.get i).val) = r.val ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rv.val.get i).val ≠ (rv.val.get j).val) := by
  sorry

/-- There exist an integer k with 1 <= k <= len(rewardValues) and pairwise distinct indices i_0, ..., i_{k-1} in [0, len(rewardValues)) such that, for every t with 0 <= t < k, rewardValues[i_t] > sum_{p=0}^{t-1} rewardValues[i_p], the total sum_{t=0}^{k-1} rewardValues[i_t] equals r, and, letting v = rewardValues[i_{k-1}] be the last chosen value, 2*v > r.
  Preconditions: 1 <= len(rewardValues) <= 50000, and for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000. -/
theorem spec_13 (rv : Slice Std.I64) (hrv : ValidInput rv) :
    ∃ r, max_total_reward rv = ok r ∧
      ∃ (k : ℕ) (idx : Fin (k + 1) → Fin (values rv).length),
        IsRewardChain (values rv) k idx ∧
          r.val = totalSum (values rv) idx ∧
          2 * (values rv).get (idx (Fin.last k)) > r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv), ∃ r, max_total_reward rv = ok r ∧
      ∃ (k : ℕ) (idx : Fin (k + 1) → Fin (values rv).length),
        IsRewardChain (values rv) k idx ∧
          r.val = totalSum (values rv) idx ∧
          2 * (values rv).get (idx (Fin.last k)) > r.val) := by
  sorry

/-- r = sum_{p=0}^{m-1} c_p.
  Preconditions: 1 <= len(rewardValues) <= 50000, for every i with 0 <= i < len(rewardValues), 1 <= rewardValues[i] <= 50000; let c_0 < c_1 < ... < c_{m-1} be the distinct values occurring in rewardValues, with m >= 2, and suppose that for every j with 1 <= j < m, c_j > sum_{p=0}^{j-1} c_p. -/
theorem spec_14 (rv : Slice Std.I64) (hrv : ValidInput rv) (cs : List ℤ)
    (hcs : IsAscendingDistinctValues (values rv) cs) (hm : 2 ≤ cs.length)
    (hcond : ∀ (j : ℕ) (hj : j < cs.length), 1 ≤ j → cs.get ⟨j, hj⟩ > (cs.take j).sum) :
    ∃ r, max_total_reward rv = ok r ∧ r.val = cs.sum := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (rv : Slice Std.I64) (hrv : ValidInput rv) (cs : List ℤ)
    (hcs : IsAscendingDistinctValues (values rv) cs) (hm : 2 ≤ cs.length)
    (hcond : ∀ (j : ℕ) (hj : j < cs.length), 1 ≤ j → cs.get ⟨j, hj⟩ > (cs.take j).sum), ∃ r, max_total_reward rv = ok r ∧ r.val = cs.sum) := by
  sorry

end AegisSpec.MaxTotalReward
