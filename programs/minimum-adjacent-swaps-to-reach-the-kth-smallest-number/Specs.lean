import Aegis.GetMinSwaps.Code.Funs

/-!
# Specifications of `Aegis.GetMinSwaps.get_min_swaps`

LeetCode problem `minimum-adjacent-swaps-to-reach-the-kth-smallest-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.GetMinSwaps

  open Aeneas.Std

  def IsDigitByte (b : U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def AllDigits (l : List U8) : Prop := ∀ b ∈ l, IsDigitByte b

  def digitVals (l : List U8) : List Nat := l.map (fun b => b.val)

  def LexLt : List Nat → List Nat → Prop
    | [], [] => False
    | [], _ :: _ => True
    | _ :: _, [] => False
    | a :: xa, b :: xb => a < b ∨ (a = b ∧ LexLt xa xb)

  def SameDigitCounts (p q : List Nat) : Prop := ∀ d, d ≤ 9 → p.count d = q.count d

  def IsWonderfulAbove (num p : List Nat) : Prop :=
    p.length = num.length ∧ SameDigitCounts p num ∧ LexLt num p

  noncomputable def WonderfulCount (num : List Nat) : Nat :=
    Set.ncard {p : List Nat | IsWonderfulAbove num p}

  def IsKthWonderful (num : List Nat) (k : Nat) (W : List Nat) : Prop :=
    IsWonderfulAbove num W ∧
      Set.ncard {p : List Nat | IsWonderfulAbove num p ∧ LexLt p W} = k - 1

  def AdjSwapStep (p q : List Nat) : Prop :=
    ∃ (i a b : Nat) (l r : List Nat),
      p = l ++ a :: b :: r ∧ l.length = i ∧ q = l ++ b :: a :: r

  inductive AdjSwaps : List Nat → List Nat → Nat → Prop where
    | refl (p : List Nat) : AdjSwaps p p 0
    | step {p q r : List Nat} {m : Nat} :
        AdjSwapStep p q → AdjSwaps q r m → AdjSwaps p r (m + 1)

  def MinAdjSwaps (p q : List Nat) (m : Nat) : Prop :=
    AdjSwaps p q m ∧ ∀ m', AdjSwaps p q m' → m ≤ m'

  noncomputable def InversionCount (σ : Nat → Nat) (n : Nat) : Nat :=
    Set.ncard {ij : Nat × Nat | ij.1 < n ∧ ij.2 < n ∧ ij.1 < ij.2 ∧ σ ij.2 < σ ij.1}

  def MatchesInOrder (p q : List Nat) (σ : Nat → Nat) : Prop :=
    (∀ i, i < p.length → σ i < q.length ∧ q[σ i]? = p[i]?) ∧
      (∀ i, i < p.length → ∀ j, j < p.length → σ i = σ j → i = j) ∧
      (∀ j, j < q.length → ∃ i, i < p.length ∧ σ i = j) ∧
      (∀ i, i < p.length → ∀ j, j < p.length → i < j → p[i]? = p[j]? → σ i < σ j)

  /-- The function returns a result r, and r is the minimum length m of a sequence of adjacent swaps (each swap exchanges two neighboring entries i and i+1 of a digit string) whose successive application to num yields W_k, where W_k is the kth smallest digit string in increasing lexicographic order among all distinct length-n digit strings that are permutations of num and are strictly greater than num.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and there exist at least k distinct length-n digit strings p such that for every digit d in '0'..'9' the count of d in p equals the count of d in num and p > num lexicographically (equivalently numerically for equal-length digit strings). Thus the kth smallest such string W_k is defined. -/
  theorem spec_1 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W) :
      ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧
        ∃ m : Nat, MinAdjSwaps (digitVals num.val) W m ∧ r.val = (m : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W), ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧
          ∃ m : Nat, MinAdjSwaps (digitVals num.val) W m ∧ r.val = (m : Int)) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and there exist at least k distinct length-n digit strings p such that for every digit d in '0'..'9' the count of d in p equals the count of d in num and p > num lexicographically. Thus W_k is defined. -/
  theorem spec_2 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W) :
      ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W), ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 1 <= r <= n * (n - 1) / 2.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and the kth smallest wonderful digit string W_k exists as described in spec_1. -/
  theorem spec_3 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
      (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r) :
      1 ≤ r.val ∧
        r.val ≤ ((num.val.length * (num.val.length - 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
        (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r), 1 ≤ r.val ∧
          r.val ≤ ((num.val.length * (num.val.length - 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Under these preconditions the function returns r = 1.
    Preconditions: Let n = len(num). Assume n = 2, every byte of num is an ASCII digit ('0' through '9'), 1 <= k <= 1000, and the kth smallest wonderful digit string exists. -/
  theorem spec_4 (num : Slice U8) (k : I64) (W : List Nat)
      (hn : num.val.length = 2)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W) :
      ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧ r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn : num.val.length = 2)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W), ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns r = 1.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, k = 1, every byte of num is an ASCII digit ('0' through '9'), and num[0] < num[1] < ... < num[n-1] (strictly increasing digit values). -/
  theorem spec_5 (num : Slice U8) (k : I64)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk : k.val = 1)
      (hd : AllDigits num.val)
      (hsorted : (digitVals num.val).Pairwise (· < ·)) :
      ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Slice U8) (k : I64)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk : k.val = 1)
        (hd : AllDigits num.val)
        (hsorted : (digitVals num.val).Pairwise (· < ·)), ∃ r : I64, Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r ∧ r.val = 1) := by
    sorry

  /-- Let W = W_k. For each digit d, match the occurrences of d in num to the occurrences of d in W in their left-to-right order. This determines a bijection sigma on positions such that W[sigma(i)] = num[i]. Whenever the function returns r, r equals the number of pairs (i,j) with 0 <= i < j < n and sigma(i) > sigma(j).
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and the kth smallest wonderful digit string W_k exists as described in spec_1. -/
  theorem spec_6 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
      (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r)
      (σ : Nat → Nat) (hσ : MatchesInOrder (digitVals num.val) W σ) :
      r.val = (InversionCount σ num.val.length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
        (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r)
        (σ : Nat → Nat) (hσ : MatchesInOrder (digitVals num.val) W σ), r.val = (InversionCount σ num.val.length : Int)) := by
    sorry

  /-- Whenever the function returns r, r is also the minimum length of a sequence of adjacent swaps that transforms W_k into num.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and the kth smallest wonderful digit string W_k exists as described in spec_1. -/
  theorem spec_7 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
      (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r) :
      ∃ m : Nat, MinAdjSwaps W (digitVals num.val) m ∧ r.val = (m : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
        (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r), ∃ m : Nat, MinAdjSwaps W (digitVals num.val) m ∧ r.val = (m : Int)) := by
    sorry

  /-- If get_min_swaps(num,k) returns r and get_min_swaps(num',k) returns r', then r = r'.
    Preconditions: Let num and num' be two slices of ASCII digits with equal length n, and let the same k satisfy 1 <= k <= 1000. Assume both (num,k) and (num',k) satisfy the common existence precondition for W_k, and assume there is a strictly increasing function f on the digit values occurring in num such that num'[i] = f(num[i]) for every 0 <= i < n. -/
  theorem spec_8 (num num' : Slice U8) (k : I64) (f : Nat → Nat)
      (hn_len : num'.val.length = num.val.length)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val) (hd' : AllDigits num'.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hexists' : k.val.toNat ≤ WonderfulCount (digitVals num'.val))
      (hf_mono : ∀ a, a ∈ digitVals num.val → ∀ b, b ∈ digitVals num.val →
        a < b → f a < f b)
      (hlab : ∀ i, i < num.val.length →
        (digitVals num'.val)[i]? = ((digitVals num.val)[i]?).map f)
      (r r' : I64)
      (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r)
      (hr' : Aegis.GetMinSwaps.get_min_swaps num' k = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num num' : Slice U8) (k : I64) (f : Nat → Nat)
        (hn_len : num'.val.length = num.val.length)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val) (hd' : AllDigits num'.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hexists' : k.val.toNat ≤ WonderfulCount (digitVals num'.val))
        (hf_mono : ∀ a, a ∈ digitVals num.val → ∀ b, b ∈ digitVals num.val →
          a < b → f a < f b)
        (hlab : ∀ i, i < num.val.length →
          (digitVals num'.val)[i]? = ((digitVals num.val)[i]?).map f)
        (r r' : I64)
        (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r)
        (hr' : Aegis.GetMinSwaps.get_min_swaps num' k = Result.ok r'), r = r') := by
    sorry

  /-- Whenever the function returns r, there exists a finite sequence of exactly r adjacent swaps whose successive application to num yields W_k.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and the kth smallest wonderful digit string W_k exists as described in spec_1. -/
  theorem spec_9 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
      (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r) :
      AdjSwaps (digitVals num.val) W r.val.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
        (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r), AdjSwaps (digitVals num.val) W r.val.toNat) := by
    sorry

  /-- Whenever the function returns r, no sequence of adjacent swaps of length strictly less than r transforms num into W_k.
    Preconditions: Let n = len(num). Assume 2 <= n <= 1000, 1 <= k <= 1000, every byte of num is an ASCII digit ('0' through '9'), and the kth smallest wonderful digit string W_k exists as described in spec_1. -/
  theorem spec_10 (num : Slice U8) (k : I64) (W : List Nat)
      (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
      (hd : AllDigits num.val)
      (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
      (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
      (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r) :
      ∀ m : Nat, AdjSwaps (digitVals num.val) W m → r.val.toNat ≤ m := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Slice U8) (k : I64) (W : List Nat)
        (hn_lo : 2 ≤ num.val.length) (hn_hi : num.val.length ≤ 1000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 1000)
        (hd : AllDigits num.val)
        (hexists : k.val.toNat ≤ WonderfulCount (digitVals num.val))
        (hW : IsKthWonderful (digitVals num.val) k.val.toNat W)
        (r : I64) (hr : Aegis.GetMinSwaps.get_min_swaps num k = Result.ok r), ∀ m : Nat, AdjSwaps (digitVals num.val) W m → r.val.toNat ≤ m) := by
    sorry

  end AegisSpec.GetMinSwaps
