import Aegis.MinStoneSum.Code.Funs

/-!
# Specifications of `Aegis.MinStoneSum.min_stone_sum`

LeetCode problem `remove-stones-to-minimize-the-total`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinStoneSum

  namespace AegisSpec.MinStoneSum

  def vals (piles : Slice Std.I64) : List ℤ := piles.val.map (fun p => p.val)

  def pileAt (piles : Slice Std.I64) (i : ℕ) : ℤ := (vals piles).getD i 0

  def ceilDivPow2 (x : ℤ) (c : ℕ) : ℤ := (x + 2 ^ c - 1) / 2 ^ c

  def total (piles : Slice Std.I64) : ℤ := (vals piles).sum

  def ceilLog2 (x : ℕ) : ℕ := Nat.clog 2 x

  def totalOps (piles : Slice Std.I64) : ℕ :=
    ∑ i ∈ Finset.range piles.length, ceilLog2 (pileAt piles i).toNat

  def maxHalf (piles : Slice Std.I64) : ℤ :=
    (vals piles).foldr (fun x acc => max (x / 2) acc) 0

  def cost (piles : Slice Std.I64) (c : ℕ → ℕ) : ℤ :=
    ∑ i ∈ Finset.range piles.length, ceilDivPow2 (pileAt piles i) (c i)

  def achievable (piles : Slice Std.I64) (kv : ℤ) : Set ℤ :=
    { v | ∃ c : ℕ → ℕ, (∑ i ∈ Finset.range piles.length, (c i : ℤ)) = kv ∧ v = cost piles c }

  /-- The function returns a result r, and r equals the minimum, over all n-tuples (c_0, ..., c_{n-1}) of nonnegative integers satisfying c_0 + ... + c_{n-1} = k, of sum_{i=0}^{n-1} ceil(piles[i] / 2^{c_i}), where ceil(x / 2^c) is the least integer y >= 0 such that x <= y * 2^c (so ceil(x / 1) = x).
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_1
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∃ r, min_stone_sum piles k = ok r ∧ IsLeast (achievable piles k.val) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∃ r, min_stone_sum piles k = ok r ∧ IsLeast (achievable piles k.val) r.val) := by
    sorry

  /-- The function returns a result r; it does not fail with overflow, out-of-bounds indexing, or panic on any input satisfying the preconditions.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_2
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∃ r, min_stone_sum piles k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∃ r, min_stone_sum piles k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= n.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_3
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r → (piles.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r → (piles.length : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} piles[i].
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_4
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r → r.val ≤ total piles := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r → r.val ≤ total piles) := by
    sorry

  /-- Whenever the function returns a result r, r = (sum_{i=0}^{n-1} piles[i]) - max_{0 <= j < n} floor(piles[j] / 2).
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, k = 1, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_5
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk : k.val = 1)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r → r.val = total piles - maxHalf piles := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk : k.val = 1)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r → r.val = total piles - maxHalf piles) := by
    sorry

  /-- Whenever the function returns a result r, r = ceil(piles[0] / 2^k), where ceil(x / 2^k) is the least integer y >= 0 such that x <= y * 2^k.
    Preconditions: Let n = len(piles). The input satisfies n = 1, 1 <= k <= 100000, and 1 <= piles[0] <= 10000. -/
  theorem spec_6
    (piles : Slice Std.I64) (k : Std.I64)
    (hn : piles.length = 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : 1 ≤ pileAt piles 0 ∧ pileAt piles 0 ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r → r.val = ceilDivPow2 (pileAt piles 0) k.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn : piles.length = 1)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : 1 ≤ pileAt piles 0 ∧ pileAt piles 0 ≤ 10000), ∀ r, min_stone_sum piles k = ok r → r.val = ceilDivPow2 (pileAt piles 0) k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r = n.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and piles[i] = 1 for every i with 0 <= i < n. -/
  theorem spec_7
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → pileAt piles i = 1) :
    ∀ r, min_stone_sum piles k = ok r → r.val = (piles.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → pileAt piles i = 1), ∀ r, min_stone_sum piles k = ok r → r.val = (piles.length : ℤ)) := by
    sorry

  /-- For each i let t_i be the least nonnegative integer with piles[i] <= 2^{t_i}. If k >= t_0 + ... + t_{n-1}, then whenever the function returns a result r, r = n.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_8
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
    (hk : (totalOps piles : ℤ) ≤ k.val) :
    ∀ r, min_stone_sum piles k = ok r → r.val = (piles.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
      (hk : (totalOps piles : ℤ) ≤ k.val), ∀ r, min_stone_sum piles k = ok r → r.val = (piles.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = (n - k) * p + k * ceil(p/2), where ceil(p/2) = p - floor(p/2).
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, k <= n, and there exists p with 1 <= p <= 10000 such that piles[i] = p for every i with 0 <= i < n. -/
  theorem spec_9
    (piles : Slice Std.I64) (k : Std.I64) (p : ℤ)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hkn : k.val ≤ (piles.length : ℤ))
    (hp1 : 1 ≤ p) (hp2 : p ≤ 10000)
    (hp : ∀ i, i < piles.length → pileAt piles i = p) :
    ∀ r, min_stone_sum piles k = ok r →
      r.val = ((piles.length : ℤ) - k.val) * p + k.val * ceilDivPow2 p 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64) (p : ℤ)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (hkn : k.val ≤ (piles.length : ℤ))
      (hp1 : 1 ≤ p) (hp2 : p ≤ 10000)
      (hp : ∀ i, i < piles.length → pileAt piles i = p), ∀ r, min_stone_sum piles k = ok r →
        r.val = ((piles.length : ℤ) - k.val) * p + k.val * ceilDivPow2 p 1) := by
    sorry

  /-- If the call min_stone_sum(piles, k1) returns r1 and the call min_stone_sum(piles, k2) returns r2, then r2 <= r1.
    Preconditions: Let n = len(piles). The slice satisfies 1 <= n <= 100000 and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. The integers k1 and k2 satisfy 1 <= k1 <= k2 <= 100000. -/
  theorem spec_10
    (piles : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r1 r2, min_stone_sum piles k1 = ok r1 → min_stone_sum piles k2 = ok r2 →
      r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (piles : Slice Std.I64) (k1 k2 : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r1 r2, min_stone_sum piles k1 = ok r1 → min_stone_sum piles k2 = ok r2 →
        r2.val ≤ r1.val) := by
    sorry

  /-- If min_stone_sum(piles, k) returns r and min_stone_sum(piles2, k) returns r2, then r <= r2.
    Preconditions: Let piles and piles2 be two slices of the same length n. Both satisfy 1 <= n <= 100000 and 1 <= piles[i], piles2[i] <= 10000 for every i with 0 <= i < n, and piles[i] <= piles2[i] for every i. Let k satisfy 1 <= k <= 100000. -/
  theorem spec_11
    (piles piles2 : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hlen : piles2.length = piles.length)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
    (hp2 : ∀ i, i < piles2.length → 1 ≤ pileAt piles2 i ∧ pileAt piles2 i ≤ 10000)
    (hle : List.Forall₂ (fun a b => a ≤ b) (vals piles) (vals piles2)) :
    ∀ r r2, min_stone_sum piles k = ok r → min_stone_sum piles2 k = ok r2 →
      r.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (piles piles2 : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hlen : piles2.length = piles.length)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
      (hp2 : ∀ i, i < piles2.length → 1 ≤ pileAt piles2 i ∧ pileAt piles2 i ≤ 10000)
      (hle : List.Forall₂ (fun a b => a ≤ b) (vals piles) (vals piles2)), ∀ r r2, min_stone_sum piles k = ok r → min_stone_sum piles2 k = ok r2 →
        r.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r, for every n-tuple (c_0, ..., c_{n-1}) of nonnegative integers with c_0 + ... + c_{n-1} = k, we have r <= sum_{i=0}^{n-1} ceil(piles[i] / 2^{c_i}), with ceil(x / 2^c) defined as the least integer y >= 0 such that x <= y * 2^c.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_12
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r →
      ∀ c : ℕ → ℕ, (∑ i ∈ Finset.range piles.length, (c i : ℤ)) = k.val →
        r.val ≤ cost piles c := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r →
        ∀ c : ℕ → ℕ, (∑ i ∈ Finset.range piles.length, (c i : ℤ)) = k.val →
          r.val ≤ cost piles c) := by
    sorry

  /-- Whenever the function returns a result r, there exists an n-tuple (c_0, ..., c_{n-1}) of nonnegative integers with c_0 + ... + c_{n-1} = k such that r = sum_{i=0}^{n-1} ceil(piles[i] / 2^{c_i}), with ceil(x / 2^c) defined as the least integer y >= 0 such that x <= y * 2^c.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_13
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r →
      ∃ c : ℕ → ℕ, (∑ i ∈ Finset.range piles.length, (c i : ℤ)) = k.val ∧
        r.val = cost piles c := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r →
        ∃ c : ℕ → ℕ, (∑ i ∈ Finset.range piles.length, (c i : ℤ)) = k.val ∧
          r.val = cost piles c) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} piles[i] if and only if piles[i] = 1 for every i with 0 <= i < n.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_14
    (piles : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000) :
    ∀ r, min_stone_sum piles k = ok r →
      (r.val = total piles ↔ ∀ i, i < piles.length → pileAt piles i = 1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (piles : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000), ∀ r, min_stone_sum piles k = ok r →
        (r.val = total piles ↔ ∀ i, i < piles.length → pileAt piles i = 1)) := by
    sorry

  /-- If min_stone_sum(piles, k) returns r and min_stone_sum(piles2, k) returns r2, then r = r2.
    Preconditions: Let n = len(piles). The input satisfies 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= piles[i] <= 10000 for every i with 0 <= i < n. Let pi be any permutation of {0, ..., n-1}, and let piles2 be the slice of length n defined by piles2[i] = piles[pi(i)] for 0 <= i < n. -/
  theorem spec_15
    (piles piles2 : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
    (hp2 : ∀ i, i < piles2.length → 1 ≤ pileAt piles2 i ∧ pileAt piles2 i ≤ 10000)
    (hperm : List.Perm (vals piles2) (vals piles)) :
    ∀ r r2, min_stone_sum piles k = ok r → min_stone_sum piles2 k = ok r2 →
      r.val = r2.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (piles piles2 : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ piles.length) (hn2 : piles.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hp : ∀ i, i < piles.length → 1 ≤ pileAt piles i ∧ pileAt piles i ≤ 10000)
      (hp2 : ∀ i, i < piles2.length → 1 ≤ pileAt piles2 i ∧ pileAt piles2 i ≤ 10000)
      (hperm : List.Perm (vals piles2) (vals piles)), ∀ r r2, min_stone_sum piles k = ok r → min_stone_sum piles2 k = ok r2 →
        r.val = r2.val) := by
    sorry

  end AegisSpec.MinStoneSum
