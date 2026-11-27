import Aegis.KInversePairs.Code.Funs

/-!
# Specifications of `Aegis.KInversePairs.k_inverse_pairs`

LeetCode problem `k-inverse-pairs-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KInversePairs

  open Aegis.KInversePairs (k_inverse_pairs)

  def MOD : ℤ := 1000000007

  def M (n : ℤ) : ℤ := n * (n - 1) / 2

  def i64 (x : ℤ) : I64 :=
    if h : IScalar.cMin IScalarTy.I64 ≤ x ∧ x ≤ IScalar.cMax IScalarTy.I64 then
      IScalar.ofInt (ty := IScalarTy.I64) x h
    else 0#i64

  theorem i64_val {x : ℤ}
      (h : IScalar.cMin IScalarTy.I64 ≤ x ∧ x ≤ IScalar.cMax IScalarTy.I64) :
      (i64 x).val = x := by
    unfold i64
    rw [dite_eq_left h]
    simp [IScalar.ofInt]

  def invPairs (a : List ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin a.length × Fin a.length)).filter
        (fun p => p.1 < p.2 ∧ a.get p.2 < a.get p.1)).card

  def permsOfRange (n : ℕ) : List (List ℕ) :=
    ((List.range n).map (fun i => i + 1)).permutations

  def P (n k : ℕ) : ℕ := ((permsOfRange n).filter (fun a => invPairs a = k)).length

  /-- Let MOD = 1000000007. Let P(n,k) be the number of arrays a of length n such that a is a permutation of {1,2,...,n} (every integer from 1 to n occurs exactly once among a[0],...,a[n-1]) and the number of inverse pairs (i,j) with 0 <= i < j < n and a[i] > a[j] is exactly k. Whenever k_inverse_pairs(n,k) returns a result r, r is an integer satisfying 0 <= r < MOD and r ≡ P(n,k) (mod MOD).
    Preconditions: 1 <= n <= 1000 and 0 <= k <= 1000. -/
  theorem spec_1 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) :
      ∀ r : I64, k_inverse_pairs n k = .ok r →
        0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ (P n.val.toNat k.val.toNat : ℤ) [ZMOD MOD] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000), ∀ r : I64, k_inverse_pairs n k = Result.ok r →
          0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ (P n.val.toNat k.val.toNat : ℤ) [ZMOD MOD]) := by
    sorry

  /-- For every n and k with 1 <= n <= 1000 and 0 <= k <= 1000, the call k_inverse_pairs(n,k) returns a result (it does not fail, overflow, panic, or get stuck).
    Preconditions: 1 <= n <= 1000 and 0 <= k <= 1000. -/
  theorem spec_2 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) :
      ∃ r : I64, k_inverse_pairs n k = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000), ∃ r : I64, k_inverse_pairs n k = Result.ok r) := by
    sorry

  /-- Whenever k_inverse_pairs(n,0) returns a result r, r = 1.
    Preconditions: 1 <= n <= 1000 and k = 0. -/
  theorem spec_3 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) (hk : k.val = 0) :
      ∀ r : I64, k_inverse_pairs n k = .ok r → r.val = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) (hk : k.val = 0), ∀ r : I64, k_inverse_pairs n k = Result.ok r → r.val = 1) := by
    sorry

  /-- Whenever k_inverse_pairs(n,1) returns a result r, r = n - 1.
    Preconditions: 1 <= n <= 1000 and k = 1. -/
  theorem spec_4 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) (hk : k.val = 1) :
      ∀ r : I64, k_inverse_pairs n k = .ok r → r.val = n.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) (hk : k.val = 1), ∀ r : I64, k_inverse_pairs n k = Result.ok r → r.val = n.val - 1) := by
    sorry

  /-- Whenever k_inverse_pairs(n,k) returns a result r, r = 0.
    Preconditions: 1 <= n <= 1000, 0 <= k <= 1000, and k > n*(n-1)/2. -/
  theorem spec_5 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) (hk : M n.val < k.val) :
      ∀ r : I64, k_inverse_pairs n k = .ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) (hk : M n.val < k.val), ∀ r : I64, k_inverse_pairs n k = Result.ok r → r.val = 0) := by
    sorry

  /-- Whenever k_inverse_pairs(n,k) returns a result r, r = 1.
    Preconditions: 1 <= n <= 1000, n*(n-1)/2 <= 1000, and k = n*(n-1)/2. -/
  theorem spec_6 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hM : M n.val ≤ 1000) (hk : k.val = M n.val) :
      ∀ r : I64, k_inverse_pairs n k = .ok r → r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hM : M n.val ≤ 1000) (hk : k.val = M n.val), ∀ r : I64, k_inverse_pairs n k = Result.ok r → r.val = 1) := by
    sorry

  /-- Let M = n*(n-1)/2. Whenever k_inverse_pairs(n,k) returns r and k_inverse_pairs(n,M-k) returns s, r = s.
    Preconditions: 1 <= n <= 1000, 0 <= k <= 1000, and 0 <= n*(n-1)/2 - k <= 1000. -/
  theorem spec_7 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd_lo : 0 ≤ M n.val - k.val) (hd_hi : M n.val - k.val ≤ 1000) :
      ∀ r s : I64, k_inverse_pairs n k = .ok r →
        k_inverse_pairs n (i64 (M n.val - k.val)) = .ok s → r.val = s.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd_lo : 0 ≤ M n.val - k.val) (hd_hi : M n.val - k.val ≤ 1000), ∀ r s : I64, k_inverse_pairs n k = Result.ok r →
          k_inverse_pairs n (i64 (M n.val - k.val)) = Result.ok s → r.val = s.val) := by
    sorry

  /-- Let M = n*(n-1)/2. For each integer t with 0 <= t <= M, let f(t) be the result returned by k_inverse_pairs(n,t). Then (Σ_{t=0}^{M} f(t)) mod 1000000007 = (n!) mod 1000000007.
    Preconditions: 1 <= n <= 1000 and n*(n-1)/2 <= 1000. -/
  theorem spec_8 (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hM : M n.val ≤ 1000) (f : I64 → ℤ)
      (hf : ∀ t : I64, 0 ≤ t.val → t.val ≤ M n.val → k_inverse_pairs n t = .ok (i64 (f t))) :
      (∑ t ∈ Finset.range ((M n.val).toNat + 1), f (i64 (t : ℤ))) ≡
        (Nat.factorial n.val.toNat : ℤ) [ZMOD MOD] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hM : M n.val ≤ 1000) (f : I64 → ℤ)
        (hf : ∀ t : I64, 0 ≤ t.val → t.val ≤ M n.val → k_inverse_pairs n t = Result.ok (i64 (f t))), (∑ t ∈ Finset.range ((M n.val).toNat + 1), f (i64 (t : ℤ))) ≡
          (Nat.factorial n.val.toNat : ℤ) [ZMOD MOD]) := by
    sorry

  /-- Let P(n,k) be the number of permutations a of {1,2,...,n} (arrays of length n containing each of 1,2,...,n exactly once) with exactly k inverse pairs (i,j) where 0 <= i < j < n and a[i] > a[j]. Whenever k_inverse_pairs(n,k) returns a result r, r = P(n,k) as an ordinary integer (not merely a congruence modulo 1000000007).
    Preconditions: 1 <= n <= 12 and 0 <= k <= 1000. -/
  theorem spec_9 (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) :
      ∀ r : I64, k_inverse_pairs n k = .ok r → r.val = (P n.val.toNat k.val.toNat : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000), ∀ r : I64, k_inverse_pairs n k = Result.ok r → r.val = (P n.val.toNat k.val.toNat : ℤ)) := by
    sorry

  /-- Whenever k_inverse_pairs(n,M-1) returns a result r, r = n - 1.
    Preconditions: 2 <= n <= 1000, M = n*(n-1)/2, and 0 <= M-1 <= 1000. -/
  theorem spec_10 (n : I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hM_lo : 0 ≤ M n.val - 1) (hM_hi : M n.val - 1 ≤ 1000) :
      ∀ r : I64, k_inverse_pairs n (i64 (M n.val - 1)) = .ok r → r.val = n.val - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hM_lo : 0 ≤ M n.val - 1) (hM_hi : M n.val - 1 ≤ 1000), ∀ r : I64, k_inverse_pairs n (i64 (M n.val - 1)) = Result.ok r → r.val = n.val - 1) := by
    sorry

  /-- Let f(m,t) denote the result returned by k_inverse_pairs(m,t) when 0 <= t <= 1000, and define f(m,t)=0 when t < 0. Then f(n,k) ≡ Σ_{i=0}^{min(k,n-1)} f(n-1,k-i) (mod 1000000007).
    Preconditions: 2 <= n <= 1000 and 0 <= k <= 1000. -/
  theorem spec_11 (n k : I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) (f : I64 → I64 → ℤ)
      (hf : ∀ m t : I64, 0 ≤ t.val → t.val ≤ 1000 →
        k_inverse_pairs m t = .ok (i64 (f m t)))
      (hf_neg : ∀ m t : I64, t.val < 0 → f m t = 0) :
      ∀ r : I64, k_inverse_pairs n k = .ok r →
        r.val ≡ (∑ i ∈ Finset.range ((min k.val (n.val - 1)).toNat + 1),
          f (i64 (n.val - 1)) (i64 (k.val - (i : ℤ)))) [ZMOD MOD] := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ 1000) (f : I64 → I64 → ℤ)
        (hf : ∀ m t : I64, 0 ≤ t.val → t.val ≤ 1000 →
          k_inverse_pairs m t = Result.ok (i64 (f m t)))
        (hf_neg : ∀ m t : I64, t.val < 0 → f m t = 0), ∀ r : I64, k_inverse_pairs n k = Result.ok r →
          r.val ≡ (∑ i ∈ Finset.range ((min k.val (n.val - 1)).toNat + 1),
            f (i64 (n.val - 1)) (i64 (k.val - (i : ℤ)))) [ZMOD MOD]) := by
    sorry

  end AegisSpec.KInversePairs
