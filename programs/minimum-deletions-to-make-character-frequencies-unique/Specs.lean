import Aegis.MinDeletions.Code.Funs

/-!
# Specifications of `Aegis.MinDeletions.min_deletions`

LeetCode problem `minimum-deletions-to-make-character-frequencies-unique`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinDeletions

def bytes (s : Slice Std.U8) : List Std.U8 := s.list.toList

def slen (s : Slice Std.U8) : ℕ := (Slice.len s).val

def countByte (l : List Std.U8) (c : ℕ) : ℕ := l.countP (fun b => b.val = c)

def freq (s : Slice Std.U8) (c : ℕ) : ℕ := countByte (bytes s) c

def Bounded (s : Slice Std.U8) : Prop := 1 ≤ slen s ∧ slen s ≤ 100000

def LowerAscii (s : Slice Std.U8) : Prop :=
  ∀ i : ℕ, i < slen s → ∃ b : Std.U8, (bytes s)[i]? = some b ∧ 97 ≤ b.val ∧ b.val ≤ 122

def Feasible (s : Slice Std.U8) (k : ℕ → ℕ) : Prop :=
  (∀ c : ℕ, k c ≤ freq s c) ∧
    ∀ c₁ c₂ : ℕ, c₁ ≠ c₂ → 0 < k c₁ → 0 < k c₂ → k c₁ ≠ k c₂

def total (k : ℕ → ℕ) : ℕ := ∑ c ∈ Finset.range 256, k c

def feasibleTotals (s : Slice Std.U8) : Set ℕ :=
  { m : ℕ | ∃ k : ℕ → ℕ, Feasible s k ∧ total k = m }

def presentValues (s : Slice Std.U8) : Finset ℕ :=
  (Finset.range 256).filter (fun c => 0 < freq s c)

def numPresent (s : Slice Std.U8) : ℕ := (presentValues s).card

def numDistinctFreqs (s : Slice Std.U8) : ℕ := (presentValues s).image (freq s) |>.card

def fmax (s : Slice Std.U8) : ℕ := (presentValues s).sup (freq s)

def capSum (f t : ℕ) : ℕ := ∑ i ∈ Finset.range t, (f - i)

/-- Define, for every byte value c in 0..255, freq(c) = the number of indices i with 0 <= i < len(s) and s[i] = c. Call a function k from byte values to natural numbers feasible if (i) k(c) <= freq(c) for every c, and (ii) for all distinct byte values c1, c2 with k(c1) > 0 and k(c2) > 0, k(c1) != k(c2). Let M = max{ sum_{c=0}^{255} k(c) | k feasible }. The function returns a result r and r = len(s) - M.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∃ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r ∧
      ∃ M : ℕ, IsGreatest (feasibleTotals s) M ∧ r.val = (slen s : ℤ) - (M : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∃ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r ∧
      ∃ M : ℕ, IsGreatest (feasibleTotals s) M ∧ r.val = (slen s : ℤ) - (M : ℤ)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every s satisfying the preconditions.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∃ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∃ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(s) - 1.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      0 ≤ r.val ∧ r.val ≤ (slen s : ℤ) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      0 ≤ r.val ∧ r.val ≤ (slen s : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for all distinct byte values c1, c2 with freq(c1) > 0 and freq(c2) > 0, freq(c1) != freq(c2), where freq is defined as in spec_1.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (r.val = 0 ↔
        ∀ c₁ c₂ : ℕ, c₁ ≠ c₂ → 0 < freq s c₁ → 0 < freq s c₂ → freq s c₁ ≠ freq s c₂) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (r.val = 0 ↔
        ∀ c₁ c₂ : ℕ, c₁ ≠ c₂ → 0 < freq s c₁ → 0 < freq s c₂ → freq s c₁ ≠ freq s c₂)) := by
  sorry

/-- Whenever the function returns a result r, where freq(c) is defined as in S1 (the number of indices i with 0 <= i < len(s) and s[i] = c), if every byte value c with freq(c) > 0 has freq(c) = 1, then r = len(s) - 1.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∀ c : ℕ, 0 < freq s c → freq s c = 1) → r.val = (slen s : ℤ) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∀ c : ℕ, 0 < freq s c → freq s c = 1) → r.val = (slen s : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, where freq(c) is defined as in spec_1, if there are exactly two byte values c1 and c2 with freq(c1) > 0 and freq(c2) > 0 and freq(c1) = freq(c2), then r = 1.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∃ c₁ c₂ : ℕ, c₁ ≠ c₂ ∧ 0 < freq s c₁ ∧ 0 < freq s c₂ ∧ freq s c₁ = freq s c₂ ∧
        ∀ c : ℕ, 0 < freq s c → c = c₁ ∨ c = c₂) → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∃ c₁ c₂ : ℕ, c₁ ≠ c₂ ∧ 0 < freq s c₁ ∧ 0 < freq s c₂ ∧ freq s c₁ = freq s c₂ ∧
        ∀ c : ℕ, 0 < freq s c → c = c₁ ∨ c = c₂) → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, where freq(c) is defined as in spec_1, if there is exactly one byte value c0 with freq(c0) >= 2, every other byte value with positive frequency has frequency 1, and the number m of byte values with positive frequency is at least 2, then r = m - 2.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∃ c₀ : ℕ, 2 ≤ freq s c₀ ∧ ∀ c : ℕ, c ≠ c₀ → 0 < freq s c → freq s c = 1) →
      2 ≤ numPresent s → r.val = (numPresent s : ℤ) - 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (∃ c₀ : ℕ, 2 ≤ freq s c₀ ∧ ∀ c : ℕ, c ≠ c₀ → 0 < freq s c → freq s c = 1) →
      2 ≤ numPresent s → r.val = (numPresent s : ℤ) - 2) := by
  sorry

/-- Whenever the function returns a result r, there exists a feasible k (as defined in spec_1) such that sum_{c=0}^{255} k(c) = len(s) - r.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      ∃ k : ℕ → ℕ, Feasible s k ∧ (total k : ℤ) = (slen s : ℤ) - r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      ∃ k : ℕ → ℕ, Feasible s k ∧ (total k : ℤ) = (slen s : ℤ) - r.val) := by
  sorry

/-- Whenever the function returns a result r, for every feasible k (as defined in spec_1), sum_{c=0}^{255} k(c) <= len(s) - r.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      ∀ k : ℕ → ℕ, Feasible s k → (total k : ℤ) ≤ (slen s : ℤ) - r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      ∀ k : ℕ → ℕ, Feasible s k → (total k : ℤ) ≤ (slen s : ℤ) - r.val) := by
  sorry

/-- Whenever the function returns a result r, let m be the number of byte values c with freq(c) > 0, and let d be the number of distinct positive integers v for which there exists a byte value c with freq(c) = v (where freq is defined as in spec_1). Then r >= m - d.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (numPresent s : ℤ) - (numDistinctFreqs s : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (numPresent s : ℤ) - (numDistinctFreqs s : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let m be the number of byte values c with freq(c) > 0, let fmax = max_{c} freq(c), and let t = min(m, fmax) (where freq is defined as in spec_1). Then r >= len(s) - (fmax + (fmax - 1) + ... + (fmax - t + 1)), where the sum contains exactly t terms.
  Preconditions: 1 <= len(s) <= 100000; for every index i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e., 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s) :
    ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (slen s : ℤ) - (capSum (fmax s) (min (numPresent s) (fmax s)) : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s), ∀ r : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      (slen s : ℤ) - (capSum (fmax s) (min (numPresent s) (fmax s)) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever min_deletions returns r on s and r' on t, we have r = r'. Equivalently, the answer depends only on the multiset of character frequencies, not on the order of characters.
  Preconditions: 1 <= len(s) <= 100000 and 1 <= len(t) <= 100000; all bytes of s and t are ASCII lowercase letters; and for every byte value c in 0..255, the frequency of c in s equals the frequency of c in t. -/
theorem spec_12 (s t : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s)
    (ht : Bounded t) (hb : LowerAscii t) (hfreq : ∀ c : ℕ, freq s c = freq t c) :
    ∀ r r' : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      Aegis.MinDeletions.min_deletions t = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : Bounded s) (ha : LowerAscii s)
    (ht : Bounded t) (hb : LowerAscii t) (hfreq : ∀ c : ℕ, freq s c = freq t c), ∀ r r' : Std.I64, Aegis.MinDeletions.min_deletions s = ok r →
      Aegis.MinDeletions.min_deletions t = ok r' → r = r') := by
  sorry

end AegisSpec.MinDeletions
