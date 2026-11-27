import Aegis.MinimumBeautifulSubstrings.Code.Funs

/-!
# Specifications of `Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings`

LeetCode problem `partition-string-into-minimum-beautiful-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumBeautifulSubstrings

def content (s : Slice Std.U8) : List Nat :=
  s.val.map (fun b => b.val)

def digits (l : List Nat) : List Nat :=
  l.map (fun c => c - 48)

def binVal : List Nat → Nat
  | [] => 0
  | d :: l => d * 2 ^ l.length + binVal l

def val (s : Slice Std.U8) (a b : Nat) : Nat :=
  binVal (digits (((content s).drop a).take (b - a)))

def numOnes (s : Slice Std.U8) : Nat :=
  ((content s).filter (fun c => c = 49)).length

def Beautiful (s : Slice Std.U8) (a b : Nat) : Prop :=
  a < b ∧ b ≤ (content s).length ∧ (content s)[a]? = some 49 ∧
    ∃ t : Nat, val s a b = 5 ^ t

def GoodPartition (s : Slice Std.U8) (p : List Nat) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some (content s).length ∧ p.Pairwise (· < ·) ∧
    ∀ q ∈ p.zip p.tail, Beautiful s q.1 q.2

def HasPartition (s : Slice Std.U8) (k : Nat) : Prop :=
  ∃ p : List Nat, p.length = k + 1 ∧ GoodPartition s p

/-- Let v(a,b) = sum_{i=a}^{b-1} (s[i] - 48) * 2^{b-1-i}. Call a nonempty substring s[a..b) with 0 <= a < b <= len(s) beautiful iff s[a] = 49 (ASCII '1') and there exists an integer t >= 0 with v(a,b) = 5^t. Let K = { k | k >= 1 and there exist indices 0 = p0 < p1 < ... < pk = len(s) such that for every j with 0 <= j < k, the substring s[p_j..p_{j+1}) is beautiful }. The function returns a result r; if K is nonempty then r = min(K), and if K is empty then r = -1.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' (48) or ASCII '1' (49). -/
theorem spec_1 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧
      ((∃ k : Nat, 1 ≤ k ∧ HasPartition s k) →
        ∃ m : Nat, 1 ≤ m ∧ HasPartition s m ∧
          (∀ k : Nat, 1 ≤ k → HasPartition s k → m ≤ k) ∧ r.val = (m : ℤ)) ∧
      (¬ (∃ k : Nat, 1 ≤ k ∧ HasPartition s k) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧
      ((∃ k : Nat, 1 ≤ k ∧ HasPartition s k) →
        ∃ m : Nat, 1 ≤ m ∧ HasPartition s m ∧
          (∀ k : Nat, 1 ≤ k → HasPartition s k → m ≤ k) ∧ r.val = (m : ℤ)) ∧
      (¬ (∃ k : Nat, 1 ≤ k ∧ HasPartition s k) → r.val = -1)) := by
  sorry

/-- The function returns a result r and does not fail; in particular, no overflow, out-of-bounds access, or panic occurs.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_2 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∃ r : Std.I64, Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∃ r : Std.I64, Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(s).
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_3 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((content s).length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((content s).length : ℤ))) := by
  sorry

/-- The function returns a result r and r = -1.
  Preconditions: 1 <= len(s) <= 15, every s[i] is ASCII '0' or ASCII '1', and s[0] = 48 (ASCII '0'). -/
theorem spec_4 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49)
    (h_zero : (content s)[0]? = some 48) :
    ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧ r.val = -1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49)
    (h_zero : (content s)[0]? = some 48), ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧ r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if s itself is beautiful; that is, s[0] = 49 (ASCII '1') and there exists an integer t >= 0 such that sum_{i=0}^{len(s)-1} (s[i] - 48) * 2^{len(s)-1-i} = 5^t.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_5 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      (r.val = 1 ↔
        ((content s)[0]? = some 49 ∧ ∃ t : Nat, val s 0 (content s).length = 5 ^ t)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      (r.val = 1 ↔
        ((content s)[0]? = some 49 ∧ ∃ t : Nat, val s 0 (content s).length = 5 ^ t))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r >= 1 and there exist indices 0 = p0 < p1 < ... < p_r = len(s) such that for every j with 0 <= j < r, the substring s[p_j..p_{j+1}) is beautiful, meaning it starts with ASCII '1' and its binary value is a power of 5.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_6 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      1 ≤ r.val ∧
        ∃ p : List Nat, p.length = r.val.toNat + 1 ∧ GoodPartition s p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      1 ≤ r.val ∧
        ∃ p : List Nat, p.length = r.val.toNat + 1 ∧ GoodPartition s p) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every integer k with 1 <= k < r, there do not exist indices 0 = p0 < p1 < ... < pk = len(s) such that every substring s[p_j..p_{j+1}) with 0 <= j < k is beautiful.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_7 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      ∀ k : Nat, 1 ≤ k → (k : ℤ) < r.val → ¬ HasPartition s k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      ∀ k : Nat, 1 ≤ k → (k : ℤ) < r.val → ¬ HasPartition s k) := by
  sorry

/-- Whenever the function returns a result r with r = -1, for every integer k >= 1 and every chain of indices 0 = p0 < p1 < ... < pk = len(s), at least one substring s[p_j..p_{j+1}) with 0 <= j < k is not beautiful.
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_8 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val = -1 →
      ∀ k : Nat, 1 ≤ k → ¬ HasPartition s k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val = -1 →
      ∀ k : Nat, 1 ≤ k → ¬ HasPartition s k) := by
  sorry

/-- The function returns a result r and r = len(s).
  Preconditions: 1 <= len(s) <= 15, every s[i] is ASCII '0' or ASCII '1', and for every i with 0 <= i < len(s), s[i] = 49 (ASCII '1'). -/
theorem spec_9 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length → (content s)[i]? = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧
      r.val = ((content s).length : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length → (content s)[i]? = some 49), ∃ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r ∧
      r.val = ((content s).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= the number of indices i with 0 <= i < len(s) and s[i] = 49 (ASCII '1').
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_10 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      r.val ≤ ((numOnes s : Nat) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r → r.val ≠ -1 →
      r.val ≤ ((numOnes s : Nat) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if r = len(s), then for every i with 0 <= i < len(s), s[i] = 49 (ASCII '1').
  Preconditions: 1 <= len(s) <= 15 and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_11 (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49) :
    ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      r.val = ((content s).length : ℤ) →
      ∀ i : Nat, i < (content s).length → (content s)[i]? = some 49 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len1 : 1 ≤ (content s).length) (h_len15 : (content s).length ≤ 15)
    (h_bits : ∀ i : Nat, i < (content s).length →
      (content s)[i]? = some 48 ∨ (content s)[i]? = some 49), ∀ r : Std.I64,
      Aegis.MinimumBeautifulSubstrings.minimum_beautiful_substrings s = ok r →
      r.val = ((content s).length : ℤ) →
      ∀ i : Nat, i < (content s).length → (content s)[i]? = some 49) := by
  sorry

end AegisSpec.MinimumBeautifulSubstrings
