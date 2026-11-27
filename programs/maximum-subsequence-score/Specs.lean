import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-subsequence-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxScore

  def contents (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def atIdx (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def IsKSubset (n k : ℕ) (S : Finset ℕ) : Prop := S ⊆ Finset.range n ∧ S.card = k

  def subsetSum (f : ℕ → ℤ) (S : Finset ℕ) : ℤ := ∑ i ∈ S, f i

  def subsetMin (f : ℕ → ℤ) (S : Finset ℕ) : ℤ := if h : S.Nonempty then S.inf' h f else 0

  def score (nums1 nums2 : ℕ → ℤ) (S : Finset ℕ) : ℤ := subsetSum nums1 S * subsetMin nums2 S

  def idxMax (n : ℕ) (f : ℕ → ℤ) : ℤ :=
    if h : (Finset.range n).Nonempty then (Finset.range n).sup' h f else 0

  def kSubsetMax (n k : ℕ) (f : Finset ℕ → ℤ) : ℤ :=
    if h : (Finset.powersetCard k (Finset.range n)).Nonempty then
      (Finset.powersetCard k (Finset.range n)).sup' h f
    else 0

  def permFun (n : ℕ) (pi : Equiv.Perm (Fin n)) : ℕ → ℕ :=
    fun i => if h : i < n then (pi ⟨i, h⟩).val else i

  lemma subsetMin_eq_inf' (f : ℕ → ℤ) {S : Finset ℕ} (h : S.Nonempty) :
      subsetMin f S = S.inf' h f := by
    rw [subsetMin, dite_eq_left h]

  lemma IsKSubset.nonempty {n k : ℕ} {S : Finset ℕ} (h : IsKSubset n k S) (hk : 1 ≤ k) :
      S.Nonempty := by
    obtain ⟨-, hcard⟩ := h
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hcard
    omega

  lemma kSubsetMax_eq_sup' (f : Finset ℕ → ℤ) {n k : ℕ} (h : k ≤ n) :
      kSubsetMax n k f =
        (Finset.powersetCard k (Finset.range n)).sup'
          (Finset.powersetCard_nonempty.2 (by simpa using h)) f := by
    rw [kSubsetMax, dite_eq_left (Finset.powersetCard_nonempty.2 (by simpa using h))]

  lemma idxMax_eq_sup' (f : ℕ → ℤ) {n : ℕ} (h : 1 ≤ n) :
      idxMax n f = (Finset.range n).sup' (Finset.nonempty_range_iff.2 (by omega)) f := by
    rw [idxMax, dite_eq_left (Finset.nonempty_range_iff.2 (by omega))]

  /-- For every k-element subset S of {0,...,n-1}, define score(S) = (sum_{i in S} nums1[i]) * (min_{i in S} nums2[i]). The function returns a result r, and r is the maximum of score(S) over all k-element subsets S of {0,...,n-1}; equivalently, score(S) <= r for every such S, and score(S) = r for at least one such S.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∃ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r ∧
        (∀ S, IsKSubset (contents nums1).length k.val.toNat S →
          score (atIdx (contents nums1)) (atIdx (contents nums2)) S ≤ r.val) ∧
        (∃ S, IsKSubset (contents nums1).length k.val.toNat S ∧
          score (atIdx (contents nums1)) (atIdx (contents nums2)) S = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∃ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r ∧
          (∀ S, IsKSubset (contents nums1).length k.val.toNat S →
            score (atIdx (contents nums1)) (atIdx (contents nums2)) S ≤ r.val) ∧
          (∃ S, IsKSubset (contents nums1).length k.val.toNat S ∧
            score (atIdx (contents nums1)) (atIdx (contents nums2)) S = r.val)) := by
    sorry

  /-- Under these preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∃ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∃ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists a k-element subset S of {0,...,n-1} such that r = (sum_{i in S} nums1[i]) * (min_{i in S} nums2[i]).
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        ∃ S, IsKSubset (contents nums1).length k.val.toNat S ∧
          r.val = score (atIdx (contents nums1)) (atIdx (contents nums2)) S := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          ∃ S, IsKSubset (contents nums1).length k.val.toNat S ∧
            r.val = score (atIdx (contents nums1)) (atIdx (contents nums2)) S) := by
    sorry

  /-- Whenever the function returns a result r, for every k-element subset S of {0,...,n-1}, (sum_{i in S} nums1[i]) * (min_{i in S} nums2[i]) <= r.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        ∀ S, IsKSubset (contents nums1).length k.val.toNat S →
          score (atIdx (contents nums1)) (atIdx (contents nums2)) S ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          ∀ S, IsKSubset (contents nums1).length k.val.toNat S →
            score (atIdx (contents nums1)) (atIdx (contents nums2)) S ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let L be the maximum, over all k-element subsets T of {0,...,n-1}, of sum_{i in T} nums1[i]. Then r <= L * (max_{0 <= i < n} nums2[i]).
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        r.val ≤ kSubsetMax (contents nums1).length k.val.toNat
            (subsetSum (atIdx (contents nums1))) *
          idxMax (contents nums1).length (atIdx (contents nums2)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          r.val ≤ kSubsetMax (contents nums1).length k.val.toNat
              (subsetSum (atIdx (contents nums1))) *
            idxMax (contents nums1).length (atIdx (contents nums2))) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < n} (nums1[i] * nums2[i]).
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). Also k = 1. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
      (hk : k.val = 1) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        r.val = idxMax (contents nums1).length
          (fun i => atIdx (contents nums1) i * atIdx (contents nums2) i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
        (hk : k.val = 1), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          r.val = idxMax (contents nums1).length
            (fun i => atIdx (contents nums1) i * atIdx (contents nums2) i)) := by
    sorry

  /-- Whenever the function returns a result r, r = (sum_{i = 0}^{n-1} nums1[i]) * (min_{0 <= i < n} nums2[i]).
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). Also k = n. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
      (hk : k.val = ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        r.val = subsetSum (atIdx (contents nums1)) (Finset.range (contents nums1).length) *
          subsetMin (atIdx (contents nums2)) (Finset.range (contents nums1).length) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
        (hk : k.val = ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          r.val = subsetSum (atIdx (contents nums1)) (Finset.range (contents nums1).length) *
            subsetMin (atIdx (contents nums2)) (Finset.range (contents nums1).length)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). Also nums1[i] = 0 for every 0 <= i < n. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
      (hzero : ∀ x ∈ contents nums1, x = 0) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r → r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
        (hzero : ∀ x ∈ contents nums1, x = 0), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = c * M, where M is the maximum, over all k-element subsets S of {0,...,n-1}, of sum_{i in S} nums1[i].
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). Also there exists an integer c with 0 <= c <= 100000 such that nums2[i] = c for every 0 <= i < n. -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
      (c : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 100000)
      (hc : ∀ x ∈ contents nums2, x = c) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        r.val = c * kSubsetMax (contents nums1).length k.val.toNat
          (subsetSum (atIdx (contents nums1))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
        (c : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 100000)
        (hc : ∀ x ∈ contents nums2, x = c), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          r.val = c * kSubsetMax (contents nums1).length k.val.toNat
            (subsetSum (atIdx (contents nums1)))) := by
    sorry

  /-- Whenever the function returns a result r, r = a * k * m, where m is the maximum, over all k-element subsets S of {0,...,n-1}, of min_{i in S} nums2[i].
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). Also there exists an integer a with 0 <= a <= 100000 such that nums1[i] = a for every 0 <= i < n. -/
  theorem spec_11 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
      (a : ℤ) (ha0 : 0 ≤ a) (ha1 : a ≤ 100000)
      (ha : ∀ x ∈ contents nums1, x = a) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        r.val = a * k.val * kSubsetMax (contents nums1).length k.val.toNat
          (subsetMin (atIdx (contents nums2))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ))
        (a : ℤ) (ha0 : 0 ≤ a) (ha1 : a ≤ 100000)
        (ha : ∀ x ∈ contents nums1, x = a), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          r.val = a * k.val * kSubsetMax (contents nums1).length k.val.toNat
            (subsetMin (atIdx (contents nums2)))) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every k-element subset S of {0,...,n-1}, either sum_{i in S} nums1[i] = 0 or min_{i in S} nums2[i] = 0.
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_12 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        (r.val = 0 ↔
          ∀ S, IsKSubset (contents nums1).length k.val.toNat S →
            subsetSum (atIdx (contents nums1)) S = 0 ∨
              subsetMin (atIdx (contents nums2)) S = 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          (r.val = 0 ↔
            ∀ S, IsKSubset (contents nums1).length k.val.toNat S →
              subsetSum (atIdx (contents nums1)) S = 0 ∨
                subsetMin (atIdx (contents nums2)) S = 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every permutation pi of {0,...,n-1}, r is also equal to the maximum, over all k-element subsets T of {0,...,n-1}, of (sum_{i in T} nums1[pi(i)]) * (min_{i in T} nums2[pi(i)]).
    Preconditions: Let n = len(nums1). The inputs satisfy len(nums1) = len(nums2) = n, 1 <= n <= 100000, 0 <= nums1[i] <= 100000 for every 0 <= i < n, 0 <= nums2[i] <= 100000 for every 0 <= i < n, and 1 <= k <= n (with k interpreted as an integer in this range). -/
  theorem spec_13 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen : (contents nums1).length = (contents nums2).length)
      (hn1 : 1 ≤ (contents nums1).length)
      (hn2 : (contents nums1).length ≤ 100000)
      (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
      (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)) :
      ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
        ∀ pi : Equiv.Perm (Fin (contents nums1).length),
          r.val = kSubsetMax (contents nums1).length k.val.toNat
            (score
              (fun i => atIdx (contents nums1) (permFun (contents nums1).length pi i))
              (fun i => atIdx (contents nums2) (permFun (contents nums1).length pi i))) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen : (contents nums1).length = (contents nums2).length)
        (hn1 : 1 ≤ (contents nums1).length)
        (hn2 : (contents nums1).length ≤ 100000)
        (hb1 : ∀ x ∈ contents nums1, 0 ≤ x ∧ x ≤ 100000)
        (hb2 : ∀ x ∈ contents nums2, 0 ≤ x ∧ x ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((contents nums1).length : ℤ)), ∀ r, Aegis.MaxScore.max_score nums1 nums2 k = ok r →
          ∀ pi : Equiv.Perm (Fin (contents nums1).length),
            r.val = kSubsetMax (contents nums1).length k.val.toNat
              (score
                (fun i => atIdx (contents nums1) (permFun (contents nums1).length pi i))
                (fun i => atIdx (contents nums2) (permFun (contents nums1).length pi i)))) := by
    sorry

  end AegisSpec.MaxScore
