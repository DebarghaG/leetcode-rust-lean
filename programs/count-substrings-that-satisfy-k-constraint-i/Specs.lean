import Aegis.CountKConstraintSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountKConstraintSubstrings.count_k_constraint_substrings`

LeetCode problem `count-substrings-that-satisfy-k-constraint-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountKConstraintSubstrings

open Aegis.CountKConstraintSubstrings

abbrev zeroByte : Nat := 48

abbrev oneByte : Nat := 49

def countByte (l : List Std.U8) (v : Nat) : Nat :=
  l.countP (fun b => decide (b.val = v))

def substring (l : List Std.U8) (a b : Nat) : List Std.U8 :=
  (l.drop a).take (b + 1 - a)

def zeroCount (l : List Std.U8) (a b : Nat) : Nat := countByte (substring l a b) zeroByte

def oneCount (l : List Std.U8) (a b : Nat) : Nat := countByte (substring l a b) oneByte

def constraintOK (l : List Std.U8) (k a b : Nat) : Prop :=
  zeroCount l a b ≤ k ∨ oneCount l a b ≤ k

def constraintOKb (l : List Std.U8) (k a b : Nat) : Bool :=
  decide (zeroCount l a b ≤ k ∨ oneCount l a b ≤ k)

def indexPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun a => (List.range n).map (fun b => (a, b)))

def numGood (l : List Std.U8) (k : Nat) : Nat :=
  (indexPairs l.length).countP (fun p => decide (p.1 ≤ p.2) && constraintOKb l k p.1 p.2)

def totalSubstrings (n : Nat) : Nat := n * (n + 1) / 2

def sumWindowCounts (n L : Nat) : Nat := (Finset.Icc 1 L).sum (fun l => n - l + 1)

def binaryBytes (l : List Std.U8) : Prop :=
  ∀ (i : Nat) (_h : i < l.length), (l[i]).val = zeroByte ∨ (l[i]).val = oneByte

def allBytesEq (l : List Std.U8) (v : Nat) : Prop :=
  ∀ (i : Nat) (_h : i < l.length), (l[i]).val = v

/-- The function returns a result r, and r is the number of pairs of indices (a,b) with 0 <= a <= b < n such that, letting z(a,b) be the number of q with a <= q <= b and s[q] = 48, and o(a,b) be the number of q with a <= q <= b and s[q] = 49, we have z(a,b) <= k or o(a,b) <= k. Equivalently, r = sum over all pairs 0 <= a <= b < n of 1 if z(a,b) <= k or o(a,b) <= k, and 0 otherwise. The counted substrings are the non-empty contiguous substrings s[a..b], with indices inclusive.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int)) :
    ∃ r : Std.I64, count_k_constraint_substrings s k = ok r ∧
      r.val = (numGood s.val k.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int)), ∃ r : Std.I64, count_k_constraint_substrings s k = ok r ∧
      r.val = (numGood s.val k.val.toNat : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not panic, access out of bounds, or overflow during its computation.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int)) :
    ∃ r : Std.I64, count_k_constraint_substrings s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int)), ∃ r : Std.I64, count_k_constraint_substrings s k = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 0 <= r <= n*(n+1)/2, where n = len(s).
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_3 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r) :
    0 ≤ r.val ∧ r.val ≤ (totalSubstrings s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r), 0 ≤ r.val ∧ r.val ≤ (totalSubstrings s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{l=1}^{L} (n - l + 1), where n = len(s) and L = min(n, 2*k + 1).
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_4 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r) :
    (sumWindowCounts s.val.length (min s.val.length (2 * k.val.toNat + 1)) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r), (sumWindowCounts s.val.length (min s.val.length (2 * k.val.toNat + 1)) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if either s[i] = 48 for every i with 0 <= i < n, or s[i] = 49 for every i with 0 <= i < n, then r = n*(n+1)/2.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_5 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hconst : allBytesEq s.val zeroByte ∨ allBytesEq s.val oneByte) :
    r.val = (totalSubstrings s.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hconst : allBytesEq s.val zeroByte ∨ allBytesEq s.val oneByte), r.val = (totalSubstrings s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every integer k' with 1 <= k' <= k, let N(s,k') be the number of pairs 0 <= a <= b < n such that s[a..b] contains at most k' occurrences of 48 or at most k' occurrences of 49. Then N(s,k') <= r.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_6 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (k' : Int) (hk'_pos : 1 ≤ k') (hk'_le : k' ≤ k.val) :
    (numGood s.val k'.toNat : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (k' : Int) (hk'_pos : 1 ≤ k') (hk'_le : k' ≤ k.val), (numGood s.val k'.toNat : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r for s and k, for every byte slice t with len(t) = n such that for every i with 0 <= i < n, t[i] = 48 exactly when s[i] = 49 and t[i] = 49 exactly when s[i] = 48, the number of pairs 0 <= a <= b < n for which t[a..b] contains at most k occurrences of 48 or at most k occurrences of 49 is also r.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_7 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (t : Slice Std.U8) (ht_len : t.val.length = s.val.length)
    (ht_swap : ∀ (i : Nat) (_hi : i < s.val.length),
      ((t.val[i]).val = zeroByte ↔ (s.val[i]).val = oneByte) ∧
      ((t.val[i]).val = oneByte ↔ (s.val[i]).val = zeroByte)) :
    (numGood t.val k.val.toNat : Int) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (t : Slice Std.U8) (ht_len : t.val.length = s.val.length)
    (ht_swap : ∀ (i : Nat) (_hi : i < s.val.length),
      ((t.val[i]).val = zeroByte ↔ (s.val[i]).val = oneByte) ∧
      ((t.val[i]).val = oneByte ↔ (s.val[i]).val = zeroByte)), (numGood t.val k.val.toNat : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r for s and k, let t be any byte slice with len(t) = n and t[i] = s[n-1-i] for every i with 0 <= i < n. Then the number of pairs 0 <= a <= b < n for which t[a..b] contains at most k occurrences of 48 or at most k occurrences of 49 equals r.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_8 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (t : Slice Std.U8) (ht_len : t.val.length = s.val.length)
    (ht_rev : ∀ (i : Nat) (_hi : i < s.val.length),
      (t.val[i]).val = (s.val[s.val.length - 1 - i]).val) :
    (numGood t.val k.val.toNat : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (t : Slice Std.U8) (ht_len : t.val.length = s.val.length)
    (ht_rev : ∀ (i : Nat) (_hi : i < s.val.length),
      (t.val[i]).val = (s.val[s.val.length - 1 - i]).val), (numGood t.val k.val.toNat : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r < n*(n+1)/2, where n = len(s), then there exists at least one pair of indices (a,b) with 0 <= a <= b < n such that the number of occurrences of 48 in s[a..b] is greater than k and the number of occurrences of 49 in s[a..b] is greater than k.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_9 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hlt : r.val < (totalSubstrings s.val.length : Int)) :
    ∃ a b : Nat, a ≤ b ∧ b < s.val.length ∧
      k.val.toNat < zeroCount s.val a b ∧ k.val.toNat < oneCount s.val a b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hlt : r.val < (totalSubstrings s.val.length : Int)), ∃ a b : Nat, a ≤ b ∧ b < s.val.length ∧
      k.val.toNat < zeroCount s.val a b ∧ k.val.toNat < oneCount s.val a b) := by
  sorry

/-- Whenever the function returns a result r, if 2*k >= n - 1, where n = len(s), then r = n*(n+1)/2.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 50; for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'); and 1 <= k <= n. -/
theorem spec_10 (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hbig : (s.val.length : Int) - 1 ≤ 2 * k.val) :
    r.val = (totalSubstrings s.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k r : Std.I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 50)
    (hs_bin : binaryBytes s.val)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : Int))
    (hr : count_k_constraint_substrings s k = ok r)
    (hbig : (s.val.length : Int) - 1 ≤ 2 * k.val), r.val = (totalSubstrings s.val.length : Int)) := by
  sorry

end AegisSpec.CountKConstraintSubstrings
