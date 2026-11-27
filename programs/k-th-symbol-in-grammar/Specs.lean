import Aegis.KthGrammar.Code.Funs

/-!
# Specifications of `Aegis.KthGrammar.kth_grammar`

LeetCode problem `k-th-symbol-in-grammar`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical

  namespace AegisSpec.KthGrammar

  def zpow2 (e : ℤ) : ℤ := 2 ^ e.toNat

  def toI64 (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

  def thueMorseStep (l : List ℤ) : List ℤ :=
    l.flatMap fun b => if b = 0 then [0, 1] else [1, 0]

  def row : Nat → List ℤ
    | 0 => []
    | 1 => [0]
    | (i + 2) => thueMorseStep (row (i + 1))

  def nthEntry : List ℤ → Nat → Option ℤ
    | [], _ => none
    | a :: _, 0 => some a
    | _ :: l, (i + 1) => nthEntry l i

  def rowEntry (n k : Nat) : Option ℤ := nthEntry (row n) (k - 1)

  def popcount (n : Nat) : Nat :=
    if h : n = 0 then 0 else n % 2 + popcount (n / 2)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

  noncomputable def countOnes (n : ℤ) : Nat :=
    ((List.range (zpow2 (n - 1)).toNat).filter fun j =>
        decide (∃ r : Std.I64,
          Aegis.KthGrammar.kth_grammar (toI64 n) (toI64 ((j : ℤ) + 1)) = ok r ∧ r.val = 1)).length

  /-- Let R_1 = [0], and for i >= 2 let R_i be obtained from R_{i-1} by replacing each 0 with 01 and each 1 with 10 and concatenating the replacements in order; thus len(R_i) = 2^(i-1). The function returns a result r and r = R_n[k], where positions are 1-indexed.
    Preconditions: n and k are integers with 1 <= n <= 30 and 1 <= k <= 2^(n-1). -/
  theorem spec_1 (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)) :
      ∃ r : Std.I64,
        Aegis.KthGrammar.kth_grammar n k = ok r ∧ rowEntry n.val.toNat k.val.toNat = some r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)), ∃ r : Std.I64,
          Aegis.KthGrammar.kth_grammar n k = ok r ∧ rowEntry n.val.toNat k.val.toNat = some r.val) := by
    sorry

  /-- For every such n and k, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: n and k are integers with 1 <= n <= 30 and 1 <= k <= 2^(n-1). -/
  theorem spec_2 (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)) :
      ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)), ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r) := by
    sorry

  /-- The function returns a result r and r is either 0 or 1.
    Preconditions: n and k are integers with 1 <= n <= 30 and 1 <= k <= 2^(n-1). -/
  theorem spec_3 (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)) :
      ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ (r.val = 0 ∨ r.val = 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)), ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ (r.val = 0 ∨ r.val = 1)) := by
    sorry

  /-- The function returns 0.
    Preconditions: 2 <= n <= 30 and k = 1. -/
  theorem spec_4 (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30) (hk : k.val = 1) :
      ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30) (hk : k.val = 1), ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns 1.
    Preconditions: 2 <= n <= 30 and k = 2. -/
  theorem spec_5 (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30) (hk : k.val = 2) :
      ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30) (hk : k.val = 2), ∃ r : Std.I64, Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns 0 if n is odd and returns 1 if n is even.
    Preconditions: 2 <= n <= 30 and k = 2^(n-1). -/
  theorem spec_6 (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk : k.val = zpow2 (n.val - 1)) :
      ∃ r : Std.I64,
        Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = if n.val % 2 = 0 then 1 else 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk : k.val = zpow2 (n.val - 1)), ∃ r : Std.I64,
          Aegis.KthGrammar.kth_grammar n k = ok r ∧ r.val = if n.val % 2 = 0 then 1 else 0) := by
    sorry

  /-- Let r be the result returned for input (n,k) and let s be the result returned for input (m,k). Then r = s; equivalently, R_n[k] = R_m[k].
    Preconditions: 1 <= m <= n <= 30 and 1 <= k <= 2^(m-1). -/
  theorem spec_7 (m n k : Std.I64) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ n.val)
      (hn30 : n.val ≤ 30) (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (m.val - 1)) :
      ∀ r s : Std.I64,
        Aegis.KthGrammar.kth_grammar n k = ok r → Aegis.KthGrammar.kth_grammar m k = ok s →
          r = s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n k : Std.I64) (hm1 : 1 ≤ m.val) (hmn : m.val ≤ n.val)
        (hn30 : n.val ≤ 30) (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (m.val - 1)), ∀ r s : Std.I64,
          Aegis.KthGrammar.kth_grammar n k = ok r → Aegis.KthGrammar.kth_grammar m k = ok s →
            r = s) := by
    sorry

  /-- Let r be the result returned for input (n,H+k) and let s be the result returned for input (n-1,k). Then r = 1 - s; equivalently, R_n[H+k] = 1 - R_{n-1}[k].
    Preconditions: 2 <= n <= 30, let H = 2^(n-2), and 1 <= k <= H. -/
  theorem spec_8 (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 2)) :
      ∀ r s : Std.I64,
        Aegis.KthGrammar.kth_grammar n (toI64 (zpow2 (n.val - 2) + k.val)) = ok r →
          Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) k = ok s → r.val = 1 - s.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 2)), ∀ r s : Std.I64,
          Aegis.KthGrammar.kth_grammar n (toI64 (zpow2 (n.val - 2) + k.val)) = ok r →
            Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) k = ok s → r.val = 1 - s.val) := by
    sorry

  /-- Let r be the result returned for input (n,2j-1) and let s be the result returned for input (n-1,j). Then r = s; equivalently, R_n[2j-1] = R_{n-1}[j].
    Preconditions: 2 <= n <= 30 and 1 <= j <= 2^(n-2). -/
  theorem spec_9 (n j : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
      (hj1 : 1 ≤ j.val) (hj : j.val ≤ zpow2 (n.val - 2)) :
      ∀ r s : Std.I64,
        Aegis.KthGrammar.kth_grammar n (toI64 (2 * j.val - 1)) = ok r →
          Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) j = ok s → r.val = s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n j : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
        (hj1 : 1 ≤ j.val) (hj : j.val ≤ zpow2 (n.val - 2)), ∀ r s : Std.I64,
          Aegis.KthGrammar.kth_grammar n (toI64 (2 * j.val - 1)) = ok r →
            Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) j = ok s → r.val = s.val) := by
    sorry

  /-- Let r be the result returned for input (n,2j) and let s be the result returned for input (n-1,j). Then r = 1 - s; equivalently, R_n[2j] = 1 - R_{n-1}[j].
    Preconditions: 2 <= n <= 30 and 1 <= j <= 2^(n-2). -/
  theorem spec_10 (n j : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
      (hj1 : 1 ≤ j.val) (hj : j.val ≤ zpow2 (n.val - 2)) :
      ∀ r s : Std.I64,
        Aegis.KthGrammar.kth_grammar n (toI64 (2 * j.val)) = ok r →
          Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) j = ok s → r.val = 1 - s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n j : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
        (hj1 : 1 ≤ j.val) (hj : j.val ≤ zpow2 (n.val - 2)), ∀ r s : Std.I64,
          Aegis.KthGrammar.kth_grammar n (toI64 (2 * j.val)) = ok r →
            Aegis.KthGrammar.kth_grammar (toI64 (n.val - 1)) j = ok s → r.val = 1 - s.val) := by
    sorry

  /-- Let r be the result returned for input (n,k) and let s be the result returned for input (n,k+1). Then r + s = 1; equivalently, the two symbols at positions k and k+1 of row n are different.
    Preconditions: 2 <= n <= 30, k is odd, and 1 <= k < 2^(n-1). -/
  theorem spec_11 (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hko : Odd k.val) (hk : k.val < zpow2 (n.val - 1)) :
      ∀ r s : Std.I64,
        Aegis.KthGrammar.kth_grammar n k = ok r →
          Aegis.KthGrammar.kth_grammar n (toI64 (k.val + 1)) = ok s → r.val + s.val = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hko : Odd k.val) (hk : k.val < zpow2 (n.val - 1)), ∀ r s : Std.I64,
          Aegis.KthGrammar.kth_grammar n k = ok r →
            Aegis.KthGrammar.kth_grammar n (toI64 (k.val + 1)) = ok s → r.val + s.val = 1) := by
    sorry

  /-- Let t be the number of 1-bits in the binary representation of k-1. The function returns r = 0 if t is even and r = 1 if t is odd.
    Preconditions: 1 <= n <= 30 and 1 <= k <= 2^(n-1). -/
  theorem spec_12 (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
      (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)) :
      ∃ r : Std.I64,
        Aegis.KthGrammar.kth_grammar n k = ok r ∧
          r.val = if popcount (k.val.toNat - 1) % 2 = 0 then 0 else 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64) (hn1 : 1 ≤ n.val) (hn30 : n.val ≤ 30)
        (hk1 : 1 ≤ k.val) (hk : k.val ≤ zpow2 (n.val - 1)), ∃ r : Std.I64,
          Aegis.KthGrammar.kth_grammar n k = ok r ∧
            r.val = if popcount (k.val.toNat - 1) % 2 = 0 then 0 else 1) := by
    sorry

  /-- For every k with 1 <= k <= 2^(n-1), let r_k be the result returned by the function on input (n,k). The number of k in that range for which r_k = 1 is exactly 2^(n-2).
    Preconditions: 2 <= n <= 30. -/
  theorem spec_13 (n : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30) :
      countOnes n.val = 2 ^ (n.val - 2).toNat := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn2 : 2 ≤ n.val) (hn30 : n.val ≤ 30), countOnes n.val = 2 ^ (n.val - 2).toNat) := by
    sorry

  end AegisSpec.KthGrammar
