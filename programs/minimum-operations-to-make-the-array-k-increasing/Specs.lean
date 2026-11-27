import Aegis.KIncreasing.Code.Funs

/-!
# Specifications of `Aegis.KIncreasing.k_increasing`

LeetCode problem `minimum-operations-to-make-the-array-k-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KIncreasing

  def vals (arr : Slice I64) : List ℤ := arr.val.map fun x => x.val

  def lvals (b : List I64) : List ℤ := b.map fun x => x.val

  def entry (a : List ℤ) (i : ℕ) : ℤ := a.getD i 0

  def classSeq (a : List ℤ) (k c : ℕ) : List ℤ :=
    ((a.zipIdx.filter fun p => decide (p.2 % k = c % k)).map fun p => p.1)

  def ndSubseq (s a : List ℤ) : Prop := s.Sublist a ∧ s.Pairwise (· ≤ ·)

  def lndsLen (a : List ℤ) : ℕ :=
    ((a.sublists.filter fun s => decide (s.Pairwise (· ≤ ·))).map List.length).foldr max 0

  def KIncr (a : List ℤ) (k : ℕ) : Prop :=
    ∀ i, i + k < a.length → entry a i ≤ entry a (i + k)

  def cntEqClass (a b : List ℤ) (k c : ℕ) : ℕ :=
    (((a.zip b).zipIdx).filter fun q => decide (q.2 % k = c % k ∧ q.1.1 = q.1.2)).length

  def cntNe (a b : List ℤ) : ℕ :=
    (((a.zip b).zipIdx).filter fun q => decide (q.1.1 ≠ q.1.2)).length

  def cntNotND (a : List ℤ) (k : ℕ) : ℕ :=
    ((Finset.range k).filter fun c => ¬ (classSeq a k c).Pairwise (· ≤ ·)).card

  /-- Let n = len(arr). For each c with 0 <= c < k, let m_c be the number of indices i with 0 <= i < n and i mod k = c mod k, and let A_c be the sequence (arr[c], arr[c+k], ..., arr[c+k*(m_c-1)]). Let L_c be the maximum length t for which there exist integers 0 <= j_0 < ... < j_{t-1} < m_c with A_c[j_0] <= ... <= A_c[j_{t-1}]. Then the function returns a result r and r = n - (L_0 + L_1 + ... + L_{k-1}).
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers; counts and sums in the specification are mathematical and do not overflow. -/
  theorem spec_1
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r ∧
        r.val = (n : ℤ) -
          ∑ c ∈ Finset.range k.val.toNat, (lndsLen (classSeq (vals arr) k.val.toNat c) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r ∧
          r.val = (n : ℤ) -
            ∑ c ∈ Finset.range k.val.toNat, (lndsLen (classSeq (vals arr) k.val.toNat c) : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_2
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n - k.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_3
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r →
        0 ≤ r.val ∧ r.val ≤ (n : ℤ) - k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r →
          0 ≤ r.val ∧ r.val ≤ (n : ℤ) - k.val) := by
    sorry

  /-- If arr is K-increasing, meaning that for every index i with k <= i < n we have arr[i-k] <= arr[i], then the function returns a result r and r = 0.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_4
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
      (hincr : KIncr (vals arr) k.val.toNat) :
      ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
        (hincr : KIncr (vals arr) k.val.toNat), ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r and r = 0, arr is K-increasing: for every index i with k <= i < n, arr[i-k] <= arr[i].
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_5
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r → r.val = 0 →
        KIncr (vals arr) k.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r → r.val = 0 →
          KIncr (vals arr) k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, there exists an array b of length n of positive 64-bit integers such that: (a) b is K-increasing, so b[i-k] <= b[i] for every k <= i < n; (b) for every c with 0 <= c < k, if A_c and L_c are defined as in spec_1, then exactly L_c indices i with i mod k = c mod k satisfy b[i] = arr[i]; and (c) exactly r indices i with 0 <= i < n satisfy b[i] != arr[i].
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_6
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r →
        ∃ b : List I64, b.length = n ∧ (∀ x ∈ b, 0 < x.val) ∧
          KIncr (lvals b) k.val.toNat ∧
          (∀ c, c < k.val.toNat →
            cntEqClass (vals arr) (lvals b) k.val.toNat c =
              lndsLen (classSeq (vals arr) k.val.toNat c)) ∧
          (cntNe (vals arr) (lvals b) : ℤ) = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r →
          ∃ b : List I64, b.length = n ∧ (∀ x ∈ b, 0 < x.val) ∧
            KIncr (lvals b) k.val.toNat ∧
            (∀ c, c < k.val.toNat →
              cntEqClass (vals arr) (lvals b) k.val.toNat c =
                lndsLen (classSeq (vals arr) k.val.toNat c)) ∧
            (cntNe (vals arr) (lvals b) : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every array b of length n of positive 64-bit integers that is K-increasing, meaning b[i-k] <= b[i] for every k <= i < n, the number of indices i with 0 <= i < n and b[i] != arr[i] is at least r.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_7
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r →
        ∀ b : List I64, b.length = n → (∀ x ∈ b, 0 < x.val) →
          KIncr (lvals b) k.val.toNat →
          r.val ≤ (cntNe (vals arr) (lvals b) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r →
          ∀ b : List I64, b.length = n → (∀ x ∈ b, 0 < x.val) →
            KIncr (lvals b) k.val.toNat →
            r.val ≤ (cntNe (vals arr) (lvals b) : ℤ)) := by
    sorry

  /-- If the call k_increasing(arr, k) returns r and the call k_increasing(arr', k) returns r', then r = r'.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. Let c0 be an integer with 0 <= c0 < k and let d be an integer. Define arr' by arr'[i] = arr[i] + d when i mod k = c0 mod k, and arr'[i] = arr[i] otherwise. Assume 1 <= arr'[i] <= n and arr'[i] is a 64-bit signed integer for every 0 <= i < n. -/
  theorem spec_8
      (arr arr' : Slice I64) (k : I64) (n : ℕ) (c0 : ℕ) (d : ℤ)
      (hn : n = arr.val.length)
      (hn' : n = arr'.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
      (hc0 : c0 < k.val.toNat)
      (hshift : ∀ i, i < n → entry (vals arr') i =
        if i % k.val.toNat = c0 % k.val.toNat then entry (vals arr) i + d
        else entry (vals arr) i)
      (hbound' : ∀ i, i < n → 1 ≤ entry (vals arr') i ∧ entry (vals arr') i ≤ (n : ℤ)) :
      ∀ r r' : I64, Aegis.KIncreasing.k_increasing arr k = .ok r →
        Aegis.KIncreasing.k_increasing arr' k = .ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr arr' : Slice I64) (k : I64) (n : ℕ) (c0 : ℕ) (d : ℤ)
        (hn : n = arr.val.length)
        (hn' : n = arr'.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
        (hc0 : c0 < k.val.toNat)
        (hshift : ∀ i, i < n → entry (vals arr') i =
          if i % k.val.toNat = c0 % k.val.toNat then entry (vals arr) i + d
          else entry (vals arr) i)
        (hbound' : ∀ i, i < n → 1 ≤ entry (vals arr') i ∧ entry (vals arr') i ≤ (n : ℤ)), ∀ r r' : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r →
          Aegis.KIncreasing.k_increasing arr' k = Result.ok r' → r = r') := by
    sorry

  /-- For each c with 0 <= c < k, let A_c be the sequence of arr values in residue class c, as in spec_1. Let B be the number of c in 0 <= c < k for which A_c is not non-decreasing. Whenever the function returns a result r, r >= B.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. All values are 64-bit signed integers. -/
  theorem spec_9
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)) :
      ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r →
        (cntNotND (vals arr) k.val.toNat : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ)), ∀ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r →
          (cntNotND (vals arr) k.val.toNat : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = n - k.
    Preconditions: Let n = len(arr). The input satisfies n >= 1, n <= 100000, 1 <= k <= n, and 1 <= arr[i] <= n for every 0 <= i < n. For every c with 0 <= c < k and every t with 0 <= t+1 < m_c, where m_c is the number of indices in residue class c, assume arr[c+k*t] > arr[c+k*(t+1)]. All values are 64-bit signed integers. -/
  theorem spec_10
      (arr : Slice I64) (k : I64) (n : ℕ)
      (hn : n = arr.val.length)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
      (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
      (hdec : ∀ c, c < k.val.toNat →
        ∀ t, t + 1 < (classSeq (vals arr) k.val.toNat c).length →
          entry (vals arr) (c + k.val.toNat * t) >
            entry (vals arr) (c + k.val.toNat * (t + 1))) :
      ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = .ok r ∧ r.val = (n : ℤ) - k.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice I64) (k : I64) (n : ℕ)
        (hn : n = arr.val.length)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (n : ℤ))
        (hbound : ∀ i, i < n → 1 ≤ entry (vals arr) i ∧ entry (vals arr) i ≤ (n : ℤ))
        (hdec : ∀ c, c < k.val.toNat →
          ∀ t, t + 1 < (classSeq (vals arr) k.val.toNat c).length →
            entry (vals arr) (c + k.val.toNat * t) >
              entry (vals arr) (c + k.val.toNat * (t + 1))), ∃ r : I64, Aegis.KIncreasing.k_increasing arr k = Result.ok r ∧ r.val = (n : ℤ) - k.val) := by
    sorry

  end AegisSpec.KIncreasing
