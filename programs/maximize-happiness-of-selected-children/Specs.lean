import Aegis.MaximumHappinessSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumHappinessSum.maximum_happiness_sum`

LeetCode problem `maximize-happiness-of-selected-children`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumHappinessSum

  def SortedDesc (l : List Std.I64) : Prop :=
    l.Pairwise (fun a b => b.val ≤ a.val)

  def nthVal (l : List Std.I64) (j : Nat) : Int :=
    (l.getD j 0#i64).val

  def subIdxSum (l : List Std.I64) (K : Nat) : Int :=
    ((l.take K).zipWith (fun x j => max (x.val - (j : Int)) 0) (List.range K)).sum

  def prefixSum (l : List Std.I64) (K : Nat) : Int :=
    ((l.take K).map (fun x => x.val)).sum

  def selVals (l : List Std.I64) (idxs : List Nat) : List Std.I64 :=
    idxs.map (fun i => l.getD i 0#i64)

  def selSum (l : List Std.I64) (idxs : List Nat) : Int :=
    (idxs.zipWith (fun i j => max (nthVal l i - (j : Int)) 0) (List.range idxs.length)).sum

  def maxEntry (happiness : Slice Std.I64) : Int :=
    happiness.val.foldr (fun x acc => max x.val acc) 0

  /-- Let H be the non-increasingly sorted list of the entries of happiness: H has length n, the multiset of its entries equals the multiset of the entries of happiness, and H[0] >= H[1] >= ... >= H[n-1]. The function returns a result r and r = sum_{j=0}^{k-1} max(H[j] - j, 0), where max(a,0) denotes the larger of a and 0.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_1 (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        r.val = subIdxSum H k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          r.val = subIdxSum H k.val.toNat) := by
    sorry

  /-- The function returns a result r and, for every ordered list i_0, i_1, ..., i_{k-1} of pairwise distinct indices with 0 <= i_j < n, the sum sum_{j=0}^{k-1} max(happiness[i_j] - j, 0) is at most r, where max(a,0) denotes the larger of a and 0.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_2 (happiness : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int)) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        ∀ idxs : List Nat, idxs.length = k.val.toNat → idxs.Nodup →
          (∀ i ∈ idxs, i < happiness.val.length) →
          selSum happiness.val idxs ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int)), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          ∀ idxs : List Nat, idxs.length = k.val.toNat → idxs.Nodup →
            (∀ i ∈ idxs, i < happiness.val.length) →
            selSum happiness.val idxs ≤ r.val) := by
    sorry

  /-- Under the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_3 (happiness : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int)) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int)), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r) := by
    sorry

  /-- The function returns a result r and r >= max_{0 <= i < n} happiness[i].
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_4 (happiness : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int)) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        maxEntry happiness ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int)), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          maxEntry happiness ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= sum_{j=0}^{k-1} H[j], where H is the non-increasingly sorted list of the entries of happiness.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_5 (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        r.val ≤ prefixSum H k.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          r.val ≤ prefixSum H k.val.toNat) := by
    sorry

  /-- The function returns a result r and r >= (sum_{j=0}^{k-1} H[j]) - k*(k-1)/2, where H is the non-increasingly sorted list of the entries of happiness.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_6 (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        prefixSum H k.val.toNat - (k.val * (k.val - 1)) / 2 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          prefixSum H k.val.toNat - (k.val * (k.val - 1)) / 2 ≤ r.val) := by
    sorry

  /-- Let happiness' be any slice of length n whose entries are a permutation of the entries of happiness. Whenever the function returns r on (happiness, k) and r' on (happiness', k), r' = r.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_7 (happiness happiness' : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hperm : happiness'.val.Perm happiness.val)
      (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
      (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r') :
      r' = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (happiness happiness' : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hperm : happiness'.val.Perm happiness.val)
        (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
        (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r'), r' = r) := by
    sorry

  /-- Whenever the function returns r1 on (happiness, k1) and r2 on (happiness, k2), r1 <= r2.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000. Let k1 and k2 be integers with 1 <= k1 <= k2 <= n. All indices are 0-based. -/
  theorem spec_8 (happiness : Slice Std.I64) (k1 k2 : Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1₁ : 1 ≤ k1.val)
      (hk12 : k1.val ≤ k2.val)
      (hk2₂ : k2.val ≤ (happiness.val.length : Int))
      (r1 : Std.I64) (hr1 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k1 = ok r1)
      (r2 : Std.I64) (hr2 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k1 k2 : Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1₁ : 1 ≤ k1.val)
        (hk12 : k1.val ≤ k2.val)
        (hk2₂ : k2.val ≤ (happiness.val.length : Int))
        (r1 : Std.I64) (hr1 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k1 = ok r1)
        (r2 : Std.I64) (hr2 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Let H be the non-increasingly sorted list of the entries of happiness. Whenever the function returns r_m on (happiness, m) and r_{m+1} on (happiness, m+1), r_{m+1} - r_m = max(H[m] - m, 0), where max(a,0) denotes the larger of a and 0.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000. Let m be an integer with 1 <= m < n. All indices are 0-based. -/
  theorem spec_9 (happiness : Slice Std.I64) (m : Nat) (km km1 : Std.I64)
      (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hm1 : 1 ≤ m)
      (hm2 : m < happiness.val.length)
      (hkm : km.val = (m : Int))
      (hkm1 : km1.val = (m : Int) + 1)
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H)
      (rm : Std.I64) (hrm : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness km = ok rm)
      (rm1 : Std.I64) (hrm1 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness km1 = ok rm1) :
      rm1.val - rm.val = max (nthVal H m - (m : Int)) 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (happiness : Slice Std.I64) (m : Nat) (km km1 : Std.I64)
        (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hm1 : 1 ≤ m)
        (hm2 : m < happiness.val.length)
        (hkm : km.val = (m : Int))
        (hkm1 : km1.val = (m : Int) + 1)
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H)
        (rm : Std.I64) (hrm : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness km = ok rm)
        (rm1 : Std.I64) (hrm1 : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness km1 = ok rm1), rm1.val - rm.val = max (nthVal H m - (m : Int)) 0) := by
    sorry

  /-- Let H be the non-increasingly sorted list of the entries of happiness. If H[k-1] >= k-1, then the function returns a result r and r = (sum_{j=0}^{k-1} H[j]) - k*(k-1)/2.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_10 (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H)
      (hkH : k.val - 1 ≤ nthVal H (k.val.toNat - 1)) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        r.val = prefixSum H k.val.toNat - (k.val * (k.val - 1)) / 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H)
        (hkH : k.val - 1 ≤ nthVal H (k.val.toNat - 1)), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          r.val = prefixSum H k.val.toNat - (k.val * (k.val - 1)) / 2) := by
    sorry

  /-- Let H be the non-increasingly sorted list of the entries of happiness. If k < n and happiness' is any slice of length n-1 obtained by deleting one entry x from happiness with x <= H[k], then whenever the function returns r on (happiness, k) and r' on (happiness', k), r' = r.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_11 (happiness happiness' : Slice Std.I64) (k : Std.I64)
      (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H)
      (hklt : k.val < (happiness.val.length : Int))
      (hdel : ∃ (l1 l2 : List Std.I64) (x : Std.I64),
        happiness.val = l1 ++ x :: l2 ∧ happiness'.val = l1 ++ l2 ∧
          x.val ≤ nthVal H k.val.toNat)
      (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
      (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r') :
      r' = r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (happiness happiness' : Slice Std.I64) (k : Std.I64)
        (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H)
        (hklt : k.val < (happiness.val.length : Int))
        (hdel : ∃ (l1 l2 : List Std.I64) (x : Std.I64),
          happiness.val = l1 ++ x :: l2 ∧ happiness'.val = l1 ++ l2 ∧
            x.val ≤ nthVal H k.val.toNat)
        (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
        (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r'), r' = r) := by
    sorry

  /-- Let H be the non-increasingly sorted list of the entries of happiness. If n < 200000 and happiness' is any slice of length n+1 obtained by inserting one additional integer entry x with 1 <= x <= H[k-1], then whenever the function returns r on (happiness, k) and r' on (happiness', k), r' = r.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n < 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_12 (happiness happiness' : Slice Std.I64) (k : Std.I64)
      (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length < 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H)
      (hins : ∃ (l1 l2 : List Std.I64) (x : Std.I64),
        happiness'.val = l1 ++ x :: l2 ∧ happiness.val = l1 ++ l2 ∧
          1 ≤ x.val ∧ x.val ≤ nthVal H (k.val.toNat - 1))
      (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
      (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r') :
      r' = r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (happiness happiness' : Slice Std.I64) (k : Std.I64)
        (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length < 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H)
        (hins : ∃ (l1 l2 : List Std.I64) (x : Std.I64),
          happiness'.val = l1 ++ x :: l2 ∧ happiness.val = l1 ++ l2 ∧
            1 ≤ x.val ∧ x.val ≤ nthVal H (k.val.toNat - 1))
        (r : Std.I64) (hr : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r)
        (r' : Std.I64) (hr' : Aegis.MaximumHappinessSum.maximum_happiness_sum happiness' k = ok r'), r' = r) := by
    sorry

  /-- The function returns a result r and there exist pairwise distinct indices i_0, i_1, ..., i_{k-1} with 0 <= i_j < n such that all three following conditions hold: (a) the multiset {happiness[i_j] : 0 <= j < k} equals the multiset {H[0], H[1], ..., H[k-1]}, where H is the non-increasingly sorted list of the entries of happiness; (b) happiness[i_0] >= happiness[i_1] >= ... >= happiness[i_{k-1}]; and (c) r = sum_{j=0}^{k-1} max(happiness[i_j] - j, 0), where max(a,0) denotes the larger of a and 0.
    Preconditions: Let n = len(happiness). The slice happiness has length n with 1 <= n <= 200000; for every i with 0 <= i < n, 1 <= happiness[i] <= 100000000; and k is an integer with 1 <= k <= n. The Lean parameter k is an i64 interpreted as this non-negative integer. All indices are 0-based. -/
  theorem spec_13 (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
      (hn1 : 1 ≤ happiness.val.length)
      (hn2 : happiness.val.length ≤ 200000)
      (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (happiness.val.length : Int))
      (hHlen : H.length = happiness.val.length)
      (hHperm : H.Perm happiness.val)
      (hHsorted : SortedDesc H) :
      ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
        ∃ idxs : List Nat,
          idxs.length = k.val.toNat ∧
          idxs.Nodup ∧
          (∀ i ∈ idxs, i < happiness.val.length) ∧
          (selVals happiness.val idxs).Perm (H.take k.val.toNat) ∧
          SortedDesc (selVals happiness.val idxs) ∧
          r.val = selSum happiness.val idxs := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (happiness : Slice Std.I64) (k : Std.I64) (H : List Std.I64)
        (hn1 : 1 ≤ happiness.val.length)
        (hn2 : happiness.val.length ≤ 200000)
        (hbounds : ∀ x ∈ happiness.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (happiness.val.length : Int))
        (hHlen : H.length = happiness.val.length)
        (hHperm : H.Perm happiness.val)
        (hHsorted : SortedDesc H), ∃ r, Aegis.MaximumHappinessSum.maximum_happiness_sum happiness k = ok r ∧
          ∃ idxs : List Nat,
            idxs.length = k.val.toNat ∧
            idxs.Nodup ∧
            (∀ i ∈ idxs, i < happiness.val.length) ∧
            (selVals happiness.val idxs).Perm (H.take k.val.toNat) ∧
            SortedDesc (selVals happiness.val idxs) ∧
            r.val = selSum happiness.val idxs) := by
    sorry

  end AegisSpec.MaximumHappinessSum
