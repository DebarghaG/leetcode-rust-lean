import Aegis.MaxTotalReward.Code.Funs

/-!
# Specifications of `Aegis.MaxTotalReward.max_total_reward`

LeetCode problem `maximum-total-reward-using-operations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxTotalReward

  def rv (a : Slice Std.I64) : List ℤ := a.val.map IScalar.val

  def valAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def InBounds (l : List ℤ) : Prop := ∀ v ∈ l, 1 ≤ v ∧ v ≤ 2000

  def Pre (a : Slice Std.I64) : Prop :=
    InBounds (rv a) ∧ 1 ≤ (rv a).length ∧ (rv a).length ≤ 2000

  def maxOf (l : List ℤ) : ℤ := l.foldr max 0

  def maxBelow (l : List ℤ) (M : ℤ) : ℤ :=
    l.foldr (fun v acc => if v < M then max v acc else acc) 0

  def total (l : List ℤ) (s : List ℕ) : ℤ := (s.map (fun i => valAt l i)).sum

  def IsAdmissible (l : List ℤ) (s : List ℕ) : Prop :=
    (∀ i ∈ s, i < l.length) ∧
      s.Nodup ∧
      ∀ (j : ℕ) (hj : j < s.length),
        valAt l (s.get ⟨j, hj⟩) > ((List.take j s).map (fun i => valAt l i)).sum

  /-- Let an admissible sequence be a finite sequence of indices i_1, ..., i_k (k >= 0) with each index in [0, n-1], all indices pairwise distinct, and for every j with 1 <= j <= k, rewardValues[i_j] > rewardValues[i_1] + ... + rewardValues[i_{j-1}]. The function returns a result r, and r is the greatest attainable total: there exists an admissible sequence whose total rewardValues[i_1] + ... + rewardValues[i_k] equals r, and every admissible sequence has total at most r.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_1 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          (∃ s : List ℕ,
            IsAdmissible (rv rewardValues) s ∧ total (rv rewardValues) s = r.val) ∧
          (∀ s : List ℕ,
            IsAdmissible (rv rewardValues) s → total (rv rewardValues) s ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            (∃ s : List ℕ,
              IsAdmissible (rv rewardValues) s ∧ total (rv rewardValues) s = r.val) ∧
            (∀ s : List ℕ,
              IsAdmissible (rv rewardValues) s → total (rv rewardValues) s ≤ r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, no out-of-bounds access, and no 64-bit overflow) for any rewardValues satisfying the preconditions.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_2 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues) :
      ∃ r : Std.I64, Aegis.MaxTotalReward.max_total_reward rewardValues = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues), ∃ r : Std.I64, Aegis.MaxTotalReward.max_total_reward rewardValues = ok r) := by
    sorry

  /-- Let M = max_{0 <= i < n} rewardValues[i]. The function returns a result r, and r >= M.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_3 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          maxOf (rv rewardValues) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            maxOf (rv rewardValues) ≤ r.val) := by
    sorry

  /-- Let M = max_{0 <= i < n} rewardValues[i]. The function returns a result r, and r <= 2 * M - 1.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_4 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          r.val ≤ 2 * maxOf (rv rewardValues) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            r.val ≤ 2 * maxOf (rv rewardValues) - 1) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} rewardValues[i]. The function returns a result r, and r <= S.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_5 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          r.val ≤ (rv rewardValues).sum := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            r.val ≤ (rv rewardValues).sum) := by
    sorry

  /-- The function returns a result r, and r = rewardValues[0].
    Preconditions: Let n = len(rewardValues). n = 1 and 1 <= rewardValues[0] <= 2000. -/
  theorem spec_6 (rewardValues : Slice Std.I64)
      (hlen : (rv rewardValues).length = 1)
      (h0 : 1 ≤ valAt (rv rewardValues) 0 ∧ valAt (rv rewardValues) 0 ≤ 2000) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          r.val = valAt (rv rewardValues) 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rewardValues : Slice Std.I64)
        (hlen : (rv rewardValues).length = 1)
        (h0 : 1 ≤ valAt (rv rewardValues) 0 ∧ valAt (rv rewardValues) 0 ≤ 2000), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            r.val = valAt (rv rewardValues) 0) := by
    sorry

  /-- The function returns a result r, and r = v.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, every rewardValues[i] satisfies 1 <= rewardValues[i] <= 2000, and there exists an integer v such that rewardValues[i] = v for every i with 0 <= i < n. -/
  theorem spec_7 (rewardValues : Slice Std.I64) (v : ℤ)
      (hpre : Pre rewardValues) (hconst : ∀ x ∈ rv rewardValues, x = v) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧ r.val = v := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (v : ℤ)
        (hpre : Pre rewardValues) (hconst : ∀ x ∈ rv rewardValues, x = v), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧ r.val = v) := by
    sorry

  /-- Let a = rewardValues[0] and b = rewardValues[1]. The function returns a result r, and r = a + b.
    Preconditions: Let n = len(rewardValues). n = 2, 1 <= rewardValues[0] <= 2000, 1 <= rewardValues[1] <= 2000, and rewardValues[0] != rewardValues[1]. -/
  theorem spec_8 (rewardValues : Slice Std.I64)
      (hlen : (rv rewardValues).length = 2)
      (h0 : 1 ≤ valAt (rv rewardValues) 0 ∧ valAt (rv rewardValues) 0 ≤ 2000)
      (h1 : 1 ≤ valAt (rv rewardValues) 1 ∧ valAt (rv rewardValues) 1 ≤ 2000)
      (hne : valAt (rv rewardValues) 0 ≠ valAt (rv rewardValues) 1) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          r.val = valAt (rv rewardValues) 0 + valAt (rv rewardValues) 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rewardValues : Slice Std.I64)
        (hlen : (rv rewardValues).length = 2)
        (h0 : 1 ≤ valAt (rv rewardValues) 0 ∧ valAt (rv rewardValues) 0 ≤ 2000)
        (h1 : 1 ≤ valAt (rv rewardValues) 1 ∧ valAt (rv rewardValues) 1 ≤ 2000)
        (hne : valAt (rv rewardValues) 0 ≠ valAt (rv rewardValues) 1), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            r.val = valAt (rv rewardValues) 0 + valAt (rv rewardValues) 1) := by
    sorry

  /-- Let M = max_{0 <= j < n} rewardValues[j] and let L = max{ rewardValues[i] | 0 <= i < n and rewardValues[i] < M }. The function returns a result r, and r >= M + L.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, every rewardValues[i] satisfies 1 <= rewardValues[i] <= 2000, and there exists an index i with rewardValues[i] < M, where M = max_{0 <= j < n} rewardValues[j]. -/
  theorem spec_9 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues)
      (hlt : ∃ i, i < (rv rewardValues).length ∧
        valAt (rv rewardValues) i < maxOf (rv rewardValues)) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          maxOf (rv rewardValues) + maxBelow (rv rewardValues) (maxOf (rv rewardValues)) ≤
            r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues)
        (hlt : ∃ i, i < (rv rewardValues).length ∧
          valAt (rv rewardValues) i < maxOf (rv rewardValues)), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            maxOf (rv rewardValues) + maxBelow (rv rewardValues) (maxOf (rv rewardValues)) ≤
              r.val) := by
    sorry

  /-- The function returns a result r, and r = sum_{t=0}^{n-1} rewardValues[t].
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, every rewardValues[i] satisfies 1 <= rewardValues[i] <= 2000, rewardValues is nondecreasing (rewardValues[i] <= rewardValues[i+1] for every 0 <= i < n-1), and for every j with 1 <= j < n, rewardValues[j] > sum_{t=0}^{j-1} rewardValues[t]. -/
  theorem spec_10 (rewardValues : Slice Std.I64) (hpre : Pre rewardValues)
      (hmono : ∀ i, i + 1 < (rv rewardValues).length →
        valAt (rv rewardValues) i ≤ valAt (rv rewardValues) (i + 1))
      (hstep : ∀ j, 1 ≤ j → j < (rv rewardValues).length →
        valAt (rv rewardValues) j >
          ((List.range j).map (fun t => valAt (rv rewardValues) t)).sum) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          r.val = (rv rewardValues).sum := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (hpre : Pre rewardValues)
        (hmono : ∀ i, i + 1 < (rv rewardValues).length →
          valAt (rv rewardValues) i ≤ valAt (rv rewardValues) (i + 1))
        (hstep : ∀ j, 1 ≤ j → j < (rv rewardValues).length →
          valAt (rv rewardValues) j >
            ((List.range j).map (fun t => valAt (rv rewardValues) t)).sum), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            r.val = (rv rewardValues).sum) := by
    sorry

  /-- Let ys be the array obtained by deleting index m from rewardValues. The function returns a result r on rewardValues and a result s on ys, and r = M + s.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, every rewardValues[i] satisfies 1 <= rewardValues[i] <= 2000, n >= 2, and there is an index m with rewardValues[m] = M where M = max_{0 <= i < n} rewardValues[i] and M > sum_{0 <= i < n, i != m} rewardValues[i]. -/
  theorem spec_11 (rewardValues ys : Slice Std.I64) (m : ℕ)
      (hpre : Pre rewardValues)
      (hlen : 2 ≤ (rv rewardValues).length)
      (hm : m < (rv rewardValues).length)
      (hM : valAt (rv rewardValues) m = maxOf (rv rewardValues))
      (hbig : maxOf (rv rewardValues) > ((rv rewardValues).eraseIdx m).sum)
      (hys : rv ys = (rv rewardValues).eraseIdx m) :
      ∃ r s : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          Aegis.MaxTotalReward.max_total_reward ys = ok s ∧
            r.val = maxOf (rv rewardValues) + s.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rewardValues ys : Slice Std.I64) (m : ℕ)
        (hpre : Pre rewardValues)
        (hlen : 2 ≤ (rv rewardValues).length)
        (hm : m < (rv rewardValues).length)
        (hM : valAt (rv rewardValues) m = maxOf (rv rewardValues))
        (hbig : maxOf (rv rewardValues) > ((rv rewardValues).eraseIdx m).sum)
        (hys : rv ys = (rv rewardValues).eraseIdx m), ∃ r s : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            Aegis.MaxTotalReward.max_total_reward ys = ok s ∧
              r.val = maxOf (rv rewardValues) + s.val) := by
    sorry

  /-- The function returns a result r. For every array ys of i64 with 1 <= len(ys) <= 2000 and 1 <= ys[k] <= 2000 for every valid k, if the set of values occurring in ys equals the set of values occurring in rewardValues, then the function returns a result r_ys on ys and r = r_ys.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_12 (rewardValues ys : Slice Std.I64)
      (hpre : Pre rewardValues) (hpre_ys : Pre ys)
      (hset : ∀ v : ℤ, v ∈ rv ys ↔ v ∈ rv rewardValues) :
      ∃ r r_ys : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          Aegis.MaxTotalReward.max_total_reward ys = ok r_ys ∧ r.val = r_ys.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rewardValues ys : Slice Std.I64)
        (hpre : Pre rewardValues) (hpre_ys : Pre ys)
        (hset : ∀ v : ℤ, v ∈ rv ys ↔ v ∈ rv rewardValues), ∃ r r_ys : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            Aegis.MaxTotalReward.max_total_reward ys = ok r_ys ∧ r.val = r_ys.val) := by
    sorry

  /-- The function returns a result r on rewardValues. For every integer v with 1 <= v <= 2000 and len(rewardValues) + 1 <= 2000, let a be the array obtained by appending v to rewardValues; the function returns a result r_v on a and r <= r_v.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= rewardValues[i] <= 2000. -/
  theorem spec_13 (rewardValues a : Slice Std.I64) (v : ℤ)
      (hpre : Pre rewardValues)
      (hlen : (rv rewardValues).length + 1 ≤ 2000)
      (hv : 1 ≤ v ∧ v ≤ 2000)
      (ha : rv a = rv rewardValues ++ [v]) :
      ∃ r r_v : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
          Aegis.MaxTotalReward.max_total_reward a = ok r_v ∧ r.val ≤ r_v.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (rewardValues a : Slice Std.I64) (v : ℤ)
        (hpre : Pre rewardValues)
        (hlen : (rv rewardValues).length + 1 ≤ 2000)
        (hv : 1 ≤ v ∧ v ≤ 2000)
        (ha : rv a = rv rewardValues ++ [v]), ∃ r r_v : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧
            Aegis.MaxTotalReward.max_total_reward a = ok r_v ∧ r.val ≤ r_v.val) := by
    sorry

  /-- The function returns a result r, and r = M + 1.
    Preconditions: Let n = len(rewardValues). 1 <= n <= 2000, every rewardValues[i] satisfies 1 <= rewardValues[i] <= 2000, and there exists an integer M > 1 such that every element of rewardValues is either 1 or M, with at least one element equal to 1 and at least one element equal to M. -/
  theorem spec_14 (rewardValues : Slice Std.I64) (M : ℤ)
      (hpre : Pre rewardValues)
      (hM : 1 < M)
      (hall : ∀ x ∈ rv rewardValues, x = 1 ∨ x = M)
      (h1 : ∃ x ∈ rv rewardValues, x = 1)
      (hMocc : ∃ x ∈ rv rewardValues, x = M) :
      ∃ r : Std.I64,
        Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧ r.val = M + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (rewardValues : Slice Std.I64) (M : ℤ)
        (hpre : Pre rewardValues)
        (hM : 1 < M)
        (hall : ∀ x ∈ rv rewardValues, x = 1 ∨ x = M)
        (h1 : ∃ x ∈ rv rewardValues, x = 1)
        (hMocc : ∃ x ∈ rv rewardValues, x = M), ∃ r : Std.I64,
          Aegis.MaxTotalReward.max_total_reward rewardValues = ok r ∧ r.val = M + 1) := by
    sorry

  end AegisSpec.MaxTotalReward
