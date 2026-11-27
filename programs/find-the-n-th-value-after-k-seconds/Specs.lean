import Aegis.ValueAfterKSeconds.Code.Funs

/-!
# Specifications of `Aegis.ValueAfterKSeconds.value_after_k_seconds`

LeetCode problem `find-the-n-th-value-after-k-seconds`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ValueAfterKSeconds

  namespace AegisSpec.ValueAfterKSeconds

  def M : ℤ := 1000000007

  def binom (N R : ℤ) : ℤ :=
    if 0 ≤ R ∧ R ≤ N then (N.toNat.choose R.toNat : ℤ) else 0

  /-- Let M = 1,000,000,007, and for integers 0 ≤ R ≤ N let C(N,R) = N!/(R!(N−R)!) (with 0! = 1; C(N,R)=0 when R<0 or R>N). For every n,k satisfying the preconditions, whenever value_after_k_seconds(n,k) returns a result r, r is the unique integer such that 0 ≤ r < M and r ≡ C(n+k−1,k) (mod M).
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 1 ≤ k ≤ 1000. -/
  theorem spec_1 (n k r : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r) :
      0 ≤ r.val ∧ r.val < M ∧ r.val ≡ binom (n.val + k.val - 1) k.val [ZMOD M] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k r : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r), 0 ≤ r.val ∧ r.val < M ∧ r.val ≡ binom (n.val + k.val - 1) k.val [ZMOD M]) := by
    sorry

  /-- For every n,k satisfying the preconditions, the call value_after_k_seconds(n,k) returns a result; it does not fail, panic, or overflow.
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 1 ≤ k ≤ 1000. -/
  theorem spec_2 (n k : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
      ∃ r, value_after_k_seconds n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r, value_after_k_seconds n k = ok r) := by
    sorry

  /-- Let M = 1,000,000,007. For every n,k satisfying the preconditions, whenever value_after_k_seconds(n,k) returns a result r, we have 0 < r < M.
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 1 ≤ k ≤ 1000. -/
  theorem spec_3 (n k r : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r) :
      0 < r.val ∧ r.val < M := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k r : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r), 0 < r.val ∧ r.val < M) := by
    sorry

  /-- Let r be the result of value_after_k_seconds(n,k) and s be the result of value_after_k_seconds(k+1,n−1). Whenever these two calls return results, r = s.
    Preconditions: n and k are integers with 2 ≤ n ≤ 1000 and 1 ≤ k ≤ 999. -/
  theorem spec_4 (n k r s : Std.I64)
      (hn : 2 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 999)
      (hr : value_after_k_seconds n k = ok r)
      (hs : value_after_k_seconds (Std.I64.ofInt (k.val + 1) (by scalar_tac))
              (Std.I64.ofInt (n.val - 1) (by scalar_tac)) = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k r s : Std.I64)
        (hn : 2 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 999)
        (hr : value_after_k_seconds n k = ok r)
        (hs : value_after_k_seconds (Std.I64.ofInt (k.val + 1) (by scalar_tac))
                (Std.I64.ofInt (n.val - 1) (by scalar_tac)) = ok s), r.val = s.val) := by
    sorry

  /-- Let M = 1,000,000,007. Let r be the result for (n,k), a the result for (n−1,k), and b the result for (n,k−1). Whenever these three calls return results, r ≡ a + b (mod M), equivalently r = (a+b) mod M.
    Preconditions: n and k are integers with 2 ≤ n ≤ 1000 and 2 ≤ k ≤ 1000. -/
  theorem spec_5 (n k r a b : Std.I64)
      (hn : 2 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r)
      (ha : value_after_k_seconds (Std.I64.ofInt (n.val - 1) (by scalar_tac)) k = ok a)
      (hb : value_after_k_seconds n (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok b) :
      r.val ≡ a.val + b.val [ZMOD M] := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k r a b : Std.I64)
        (hn : 2 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r)
        (ha : value_after_k_seconds (Std.I64.ofInt (n.val - 1) (by scalar_tac)) k = ok a)
        (hb : value_after_k_seconds n (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok b), r.val ≡ a.val + b.val [ZMOD M]) := by
    sorry

  /-- Let M = 1,000,000,007. Let r be the result for (n,k), and for each i with 1 ≤ i ≤ n let r_i be the result for (i,k−1). Whenever all these calls return results, r ≡ Σ_{i=1}^{n} r_i (mod M).
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 2 ≤ k ≤ 1000. -/
  theorem spec_6 (n k r : Std.I64) (ri : ℕ → Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r)
      (hri : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n.val.toNat),
        value_after_k_seconds (Std.I64.ofInt (i : ℤ) (by scalar_tac))
          (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok (ri i)) :
      r.val ≡ (∑ i ∈ Finset.Icc (1 : ℕ) n.val.toNat, (ri i).val) [ZMOD M] := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k r : Std.I64) (ri : ℕ → Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r)
        (hri : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n.val.toNat),
          value_after_k_seconds (Std.I64.ofInt (i : ℤ) (by scalar_tac))
            (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok (ri i)), r.val ≡ (∑ i ∈ Finset.Icc (1 : ℕ) n.val.toNat, (ri i).val) [ZMOD M]) := by
    sorry

  /-- Let M = 1,000,000,007. Let s be the result for (n+1,K), and for each j with 1 ≤ j ≤ K let r_j be the result for (n,j). Whenever all these calls return results, s ≡ 1 + Σ_{j=1}^{K} r_j (mod M).
    Preconditions: n and K are integers with 1 ≤ n ≤ 999 and 1 ≤ K ≤ 1000. -/
  theorem spec_7 (n K s : Std.I64) (rj : ℕ → Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 999) (hK : 1 ≤ K.val ∧ K.val ≤ 1000)
      (hs : value_after_k_seconds (Std.I64.ofInt (n.val + 1) (by scalar_tac)) K = ok s)
      (hrj : ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ K.val.toNat),
        value_after_k_seconds n (Std.I64.ofInt (j : ℤ) (by scalar_tac)) = ok (rj j)) :
      s.val ≡ (1 + ∑ j ∈ Finset.Icc (1 : ℕ) K.val.toNat, (rj j).val) [ZMOD M] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n K s : Std.I64) (rj : ℕ → Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 999) (hK : 1 ≤ K.val ∧ K.val ≤ 1000)
        (hs : value_after_k_seconds (Std.I64.ofInt (n.val + 1) (by scalar_tac)) K = ok s)
        (hrj : ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ K.val.toNat),
          value_after_k_seconds n (Std.I64.ofInt (j : ℤ) (by scalar_tac)) = ok (rj j)), s.val ≡ (1 + ∑ j ∈ Finset.Icc (1 : ℕ) K.val.toNat, (rj j).val) [ZMOD M]) := by
    sorry

  /-- Let M = 1,000,000,007. Let r be the result for (n,k) and s the result for (n,k−1). Whenever both calls return results, k·r ≡ (n+k−1)·s (mod M).
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 2 ≤ k ≤ 1000. -/
  theorem spec_8 (n k r s : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r)
      (hs : value_after_k_seconds n (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok s) :
      k.val * r.val ≡ (n.val + k.val - 1) * s.val [ZMOD M] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k r s : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 2 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r)
        (hs : value_after_k_seconds n (Std.I64.ofInt (k.val - 1) (by scalar_tac)) = ok s), k.val * r.val ≡ (n.val + k.val - 1) * s.val [ZMOD M]) := by
    sorry

  /-- Let M = 1,000,000,007, and let C(N,R) denote the binomial coefficient N!/(R!(N−R)!). Whenever value_after_k_seconds(n,k) returns a result r, r ≡ Σ_{i=0}^{n−1} C(k−1+i,i) (mod M).
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 1 ≤ k ≤ 1000. -/
  theorem spec_9 (n k r : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r) :
      r.val ≡ (∑ i ∈ Finset.range n.val.toNat, binom (k.val - 1 + (i : ℤ)) (i : ℤ)) [ZMOD M] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k r : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r), r.val ≡ (∑ i ∈ Finset.range n.val.toNat, binom (k.val - 1 + (i : ℤ)) (i : ℤ)) [ZMOD M]) := by
    sorry

  /-- Let M = 1,000,000,007, and let C(N,R) denote the binomial coefficient N!/(R!(N−R)!) for 0 ≤ R ≤ N, with C(N,R)=0 when R<0 or R>N. For every n,k satisfying the preconditions, whenever value_after_k_seconds(n,k) returns a result r, r ≡ Σ_{i=0}^{k} C(n−1,i)·C(k,i) (mod M).
    Preconditions: n and k are integers with 1 ≤ n ≤ 1000 and 1 ≤ k ≤ 1000. -/
  theorem spec_10 (n k r : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hr : value_after_k_seconds n k = ok r) :
      r.val ≡ (∑ i ∈ Finset.range (k.val.toNat + 1),
        binom (n.val - 1) (i : ℤ) * binom k.val (i : ℤ)) [ZMOD M] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k r : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val ≤ 1000) (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hr : value_after_k_seconds n k = ok r), r.val ≡ (∑ i ∈ Finset.range (k.val.toNat + 1),
          binom (n.val - 1) (i : ℤ) * binom k.val (i : ℤ)) [ZMOD M]) := by
    sorry

  end AegisSpec.ValueAfterKSeconds
