import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-remove-all-cars-containing-illegal-goods`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTime

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat := ((s.val[i]?).map (fun b => b.val)).getD 0

  def IsBinary (s : Slice Std.U8) : Prop :=
    ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49

  def UniqueIndexOf (s : Slice Std.U8) (b : Nat) : Prop :=
    ∃ p, p < s.val.length ∧ byteAt s p = b ∧ ∀ q, q < s.val.length → byteAt s q = b → q = p

  def onesIn (s : Slice Std.U8) (L R : Nat) : Nat :=
    ((Finset.Ico L (s.val.length - R)).filter (fun i => byteAt s i = 49)).card

  def onesCount (s : Slice Std.U8) : Nat := onesIn s 0 0

  def cost (s : Slice Std.U8) (L R : Nat) : Int :=
    (L : Int) + (R : Int) + 2 * (onesIn s L R : Int)

  def Admissible (s : Slice Std.U8) (L R : Nat) : Prop := L + R ≤ s.val.length

  def costs (s : Slice Std.U8) : Finset Int :=
    ((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1)) |>.filter
        (fun p : Nat × Nat => p.1 + p.2 ≤ s.val.length)) |>.image
      (fun p : Nat × Nat => cost s p.1 p.2)

  lemma costs_nonempty (s : Slice Std.U8) : (costs s).Nonempty := by
    refine ⟨cost s 0 0, Finset.mem_image.mpr ⟨(0, 0), ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨by simp [Finset.mem_product], by simp⟩

  def minCost (s : Slice Std.U8) : Int := (costs s).min' (costs_nonempty s)

  def weight (s : Slice Std.U8) (i : Nat) : Int := if byteAt s i = 48 then 1 else -1

  def prefixWeight (s : Slice Std.U8) (j : Nat) : Int :=
    (Finset.range j).sum (fun i => weight s i)

  def intervalSums (s : Slice Std.U8) : Finset Int :=
    ((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1)) |>.filter
        (fun p : Nat × Nat => p.1 ≤ p.2)) |>.image
      (fun p : Nat × Nat => prefixWeight s p.2 - prefixWeight s p.1)

  lemma intervalSums_nonempty (s : Slice Std.U8) : (intervalSums s).Nonempty := by
    refine ⟨prefixWeight s 0 - prefixWeight s 0, Finset.mem_image.mpr ⟨(0, 0), ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨by simp [Finset.mem_product], by simp⟩

  def maxIntervalSum (s : Slice Std.U8) : Int := (intervalSums s).max' (intervalSums_nonempty s)

  def IsReverse (t s : Slice Std.U8) : Prop :=
    t.val.length = s.val.length ∧
      ∀ i, i < s.val.length → byteAt t i = byteAt s (s.val.length - 1 - i)

  def IsFlipToOneAt (t s : Slice Std.U8) (q : Nat) : Prop :=
    t.val.length = s.val.length ∧ byteAt t q = 49 ∧
      ∀ i, i < s.val.length → i ≠ q → byteAt t i = byteAt s i

  /-- Let n = len(s). For each pair of integers (L,R) with 0 <= L, 0 <= R, and L+R <= n, let C(L,R) be the number of indices i such that L <= i < n-R and s[i] = 49. Define cost(L,R) = L + R + 2*C(L,R). The function returns an I64 result r, and r = min { cost(L,R) | 0 <= L, 0 <= R, L+R <= n }.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = minCost s := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = minCost s) := by
    sorry

  /-- Let k be the number of indices i with 0 <= i < len(s) and s[i] = 49. The function returns an I64 result r and r >= k.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ (onesCount s : Int) ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ (onesCount s : Int) ≤ r.val) := by
    sorry

  /-- The function returns an I64 result r and r <= len(s).
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Let k be the number of indices i with 0 <= i < len(s) and s[i] = 49. The function returns an I64 result r and r <= 2*k.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ 2 * (onesCount s : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ 2 * (onesCount s : Int)) := by
    sorry

  /-- The function returns an I64 result r and r = len(s).
    Preconditions: 1 <= len(s) <= 200000, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and for every i with 0 <= i < len(s), s[i] = 49. -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
      (hall_ones : ∀ i, i < s.val.length → byteAt s i = 49) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = (s.val.length : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
        (hall_ones : ∀ i, i < s.val.length → byteAt s i = 49), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = (s.val.length : Int)) := by
    sorry

  /-- Let n = len(s) and let p be the unique index with 0 <= p < n and s[p] = 49. The function returns an I64 result r and r = min(p+1, n-p, 2).
    Preconditions: 1 <= len(s) <= 200000, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and there is exactly one index p with 0 <= p < len(s) and s[p] = 49. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
      (huniq : UniqueIndexOf s 49) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
        ∀ p, p < s.val.length → byteAt s p = 49 →
          r.val = min ((p : Int) + 1) (min ((s.val.length : Int) - (p : Int)) 2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
        (huniq : UniqueIndexOf s 49), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
          ∀ p, p < s.val.length → byteAt s p = 49 →
            r.val = min ((p : Int) + 1) (min ((s.val.length : Int) - (p : Int)) 2)) := by
    sorry

  /-- The function returns some I64 result r; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r) := by
    sorry

  /-- Let n = len(s) and let t be the length-n byte array defined by t[i] = s[n-1-i] for 0 <= i < n. Define, for 0 <= L, 0 <= R, L+R <= n, C_t(L,R) as the number of indices i with L <= i < n-R and t[i] = 49. The function returns an I64 result r, and r = min { L + R + 2*C_t(L,R) | 0 <= L, 0 <= R, L+R <= n }.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_8 (s t : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
      (hrev : IsReverse t s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = minCost t := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
        (hrev : IsReverse t s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = minCost t) := by
    sorry

  /-- Let n = len(s). For 0 <= L, 0 <= R with L+R <= n, let C(L,R) be the number of indices i with L <= i < n-R and s[i] = 49. The function returns an I64 result r, and there exist integers L and R with 0 <= L, 0 <= R, L+R <= n such that r = L + R + 2*C(L,R).
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
        ∃ L R, Admissible s L R ∧ r.val = cost s L R := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
          ∃ L R, Admissible s L R ∧ r.val = cost s L R) := by
    sorry

  /-- Let n = len(s). For every pair of integers L and R with 0 <= L, 0 <= R, L+R <= n, let C(L,R) be the number of indices i with L <= i < n-R and s[i] = 49. The function returns an I64 result r, and for every such L and R, r <= L + R + 2*C(L,R).
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
        ∀ L R, Admissible s L R → r.val ≤ cost s L R := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
          ∀ L R, Admissible s L R → r.val ≤ cost s L R) := by
    sorry

  /-- The function returns an I64 result r, and r = 0 if and only if for every i with 0 <= i < len(s), s[i] = 48.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
        (r.val = 0 ↔ ∀ i, i < s.val.length → byteAt s i = 48) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
          (r.val = 0 ↔ ∀ i, i < s.val.length → byteAt s i = 48)) := by
    sorry

  /-- Let n = len(s) and suppose there is exactly one index q with 0 <= q < n and s[q] = 48. The function returns an I64 result r and r = n - 1.
    Preconditions: 1 <= len(s) <= 200000, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and there is exactly one index q with 0 <= q < len(s) and s[q] = 48. -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
      (huniq : UniqueIndexOf s 48) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = (s.val.length : Int) - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
        (huniq : UniqueIndexOf s 48), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val = (s.val.length : Int) - 1) := by
    sorry

  /-- Let n = len(s). For every index q with 0 <= q < n and s[q] = 48, define a byte array t_q of length n by t_q[i] = s[i] for i != q and t_q[q] = 49. For 0 <= L, 0 <= R with L+R <= n, let C_q(L,R) be the number of indices i with L <= i < n-R and t_q[i] = 49. The function returns an I64 result r, and r <= min { L + R + 2*C_q(L,R) | 0 <= L, 0 <= R, L+R <= n }.
    Preconditions: 1 <= len(s) <= 200000, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and there exists an index q with 0 <= q < len(s) and s[q] = 48. -/
  theorem spec_13 (s t : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
      (hexists_zero : ∃ q, q < s.val.length ∧ byteAt s q = 48)
      (q : Nat) (hq : q < s.val.length) (hq_zero : byteAt s q = 48)
      (hflip : IsFlipToOneAt t s q) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ minCost t := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s)
        (hexists_zero : ∃ q, q < s.val.length ∧ byteAt s q = 48)
        (q : Nat) (hq : q < s.val.length) (hq_zero : byteAt s q = 48)
        (hflip : IsFlipToOneAt t s q), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧ r.val ≤ minCost t) := by
    sorry

  /-- Let r_s be the result of minimum_time(s) and r_t be the result of minimum_time(t). Then r_s <= r_t. That is, adding illegal cars (changing 48s to 49s) cannot decrease the minimum time.
    Preconditions: 1 <= len(s) <= 200000, 1 <= len(t) <= 200000, len(s)=len(t), for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, for every i with 0 <= i < len(t), t[i] = 48 or t[i] = 49, and for every i with 0 <= i < len(s), if s[i]=49 then t[i]=49. -/
  theorem spec_14 (s t : Slice Std.U8)
      (hlen_pos_s : 1 ≤ s.val.length) (hlen_max_s : s.val.length ≤ 200000) (hbin_s : IsBinary s)
      (hlen_pos_t : 1 ≤ t.val.length) (hlen_max_t : t.val.length ≤ 200000) (hbin_t : IsBinary t)
      (hlen_eq : s.val.length = t.val.length)
      (hmono : ∀ i, i < s.val.length → byteAt s i = 49 → byteAt t i = 49) :
      ∃ rs rt : Std.I64, Aegis.MinimumTime.minimum_time s = ok rs ∧
        Aegis.MinimumTime.minimum_time t = ok rt ∧ rs.val ≤ rt.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_pos_s : 1 ≤ s.val.length) (hlen_max_s : s.val.length ≤ 200000) (hbin_s : IsBinary s)
        (hlen_pos_t : 1 ≤ t.val.length) (hlen_max_t : t.val.length ≤ 200000) (hbin_t : IsBinary t)
        (hlen_eq : s.val.length = t.val.length)
        (hmono : ∀ i, i < s.val.length → byteAt s i = 49 → byteAt t i = 49), ∃ rs rt : Std.I64, Aegis.MinimumTime.minimum_time s = ok rs ∧
          Aegis.MinimumTime.minimum_time t = ok rt ∧ rs.val ≤ rt.val) := by
    sorry

  /-- Let n = len(s). For 0 <= i < n define a_i = 1 if s[i]=48 and a_i = -1 if s[i]=49. The function returns an I64 result r, and r = n - max { sum_{i=L}^{R-1} a_i | 0 <= L <= R <= n }, where the empty sum is 0.
    Preconditions: 1 <= len(s) <= 200000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_15 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
        r.val = (s.val.length : Int) - maxIntervalSum s := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 200000) (hbin : IsBinary s), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time s = ok r ∧
          r.val = (s.val.length : Int) - maxIntervalSum s) := by
    sorry

  end AegisSpec.MinimumTime
