import Aegis.CloseStrings.Code.Funs

/-!
# Specifications of `Aegis.CloseStrings.close_strings`

LeetCode problem `determine-if-two-strings-are-close`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CloseStrings

namespace AegisSpec.CloseStrings

def IsLower (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllLower (w : Slice Std.U8) : Prop := ∀ b ∈ w.val, IsLower b

def len (w : Slice Std.U8) : ℕ := w.val.length

def countOcc (w : Slice Std.U8) (c : Std.U8) : ℕ :=
  (w.val.filter (fun b => b = c)).length

def Occurs (w : Slice Std.U8) (c : Std.U8) : Prop :=
  ∃ i : ℕ, i < len w ∧ w.val[i]? = some c

def letterByte (i : ℕ) : Std.U8 := ⟨BitVec.ofNat 8 (97 + i)⟩

def letterCount (w : Slice Std.U8) (i : ℕ) : ℕ := countOcc w (letterByte i)

def numLettersWithCount (w : Slice Std.U8) (k : ℕ) : ℕ :=
  ((List.range 26).map (fun i => letterCount w i)).countP (fun n => decide (n = k))

def swapByte (c d : Std.U8) (b : Std.U8) : Std.U8 :=
  if b = c then d else if b = d then c else b

def IsLetterPerm (σ : Std.U8 → Std.U8) : Prop :=
  (∀ c, IsLower c → IsLower (σ c)) ∧
    (∀ c d, IsLower c → IsLower d → σ c = σ d → c = d)

/-- Whenever close_strings(word1, word2) returns a result r, r = true if and only if all three conditions hold: (a) len(word1) = len(word2); (b) for every lowercase letter c, c occurs in word1 if and only if c occurs in word2; (c) for every integer k >= 1, the number of lowercase letters occurring exactly k times in word1 equals the number of lowercase letters occurring exactly k times in word2. Thus r = false exactly when at least one of (a), (b), (c) fails. An occurrence of c in a slice w means an index i with 0 <= i < len(w) and w[i] = c.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122 (lowercase English letters). -/
theorem spec_1 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    ∀ r, close_strings word1 word2 = ok r →
      (r = true ↔
        (len word1 = len word2 ∧
          (∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) ∧
          (∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), ∀ r, close_strings word1 word2 = ok r →
      (r = true ↔
        (len word1 = len word2 ∧
          (∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) ∧
          (∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k)))) := by
  sorry

/-- The call close_strings(word1, word2) returns a result (a Bool) and does not fail, panic, overflow, or go out of bounds for every word1 and word2 satisfying the preconditions.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122 (lowercase English letters). -/
theorem spec_2 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    ∃ r, close_strings word1 word2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), ∃ r, close_strings word1 word2 = ok r) := by
  sorry

/-- Whenever close_strings(word1, word2) returns a result r, r = false.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122; len(word1) != len(word2). -/
theorem spec_3 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_len : len word1 ≠ len word2) :
    ∀ r, close_strings word1 word2 = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_len : len word1 ≠ len word2), ∀ r, close_strings word1 word2 = ok r → r = false) := by
  sorry

/-- Whenever close_strings(word1, word2) returns true, for every lowercase letter c, c occurs in word1 if and only if c occurs in word2.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_4 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    close_strings word1 word2 = ok true →
      ∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), close_strings word1 word2 = ok true →
      ∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) := by
  sorry

/-- Whenever close_strings(word1, word2) returns true, for every integer k >= 1, the number of lowercase letters occurring exactly k times in word1 equals the number of lowercase letters occurring exactly k times in word2.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_5 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    close_strings word1 word2 = ok true →
      ∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), close_strings word1 word2 = ok true →
      ∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k) := by
  sorry

/-- Whenever close_strings(word1, word2) returns a result r, r = true.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122; for every lowercase letter c, the number of occurrences of c in word1 equals the number of occurrences of c in word2. -/
theorem spec_6 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_counts : ∀ c, IsLower c → countOcc word1 c = countOcc word2 c) :
    ∀ r, close_strings word1 word2 = ok r → r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_counts : ∀ c, IsLower c → countOcc word1 c = countOcc word2 c), ∀ r, close_strings word1 word2 = ok r → r = true) := by
  sorry

/-- Whenever close_strings(word1, word2) returns r and close_strings(word2, word1) returns r', we have r = r'.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_7 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    ∀ r r', close_strings word1 word2 = ok r →
      close_strings word2 word1 = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), ∀ r r', close_strings word1 word2 = ok r →
      close_strings word2 word1 = ok r' → r = r') := by
  sorry

/-- For every byte slice word1' with 1 <= len(word1') <= 100000, all bytes in 97..122, len(word1') = len(word1), and the same number of occurrences of every lowercase letter as word1, whenever close_strings(word1, word2) returns r and close_strings(word1', word2) returns r', we have r = r'.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_8 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (word1' : Slice Std.U8)
    (h1'_lo : 1 ≤ len word1') (h1'_hi : len word1' ≤ 100000)
    (h1'_range : AllLower word1')
    (h1'_len : len word1' = len word1)
    (h1'_counts : ∀ c, IsLower c → countOcc word1' c = countOcc word1 c) :
    ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2 = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (word1' : Slice Std.U8)
    (h1'_lo : 1 ≤ len word1') (h1'_hi : len word1' ≤ 100000)
    (h1'_range : AllLower word1')
    (h1'_len : len word1' = len word1)
    (h1'_counts : ∀ c, IsLower c → countOcc word1' c = countOcc word1 c), ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2 = ok r' → r = r') := by
  sorry

/-- For every byte slice word2' with 1 <= len(word2') <= 100000, all bytes in 97..122, len(word2') = len(word2), and the same number of occurrences of every lowercase letter as word2, whenever close_strings(word1, word2) returns r and close_strings(word1, word2') returns r', we have r = r'.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_9 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (word2' : Slice Std.U8)
    (h2'_lo : 1 ≤ len word2') (h2'_hi : len word2' ≤ 100000)
    (h2'_range : AllLower word2')
    (h2'_len : len word2' = len word2)
    (h2'_counts : ∀ c, IsLower c → countOcc word2' c = countOcc word2 c) :
    ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1 word2' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (word2' : Slice Std.U8)
    (h2'_lo : 1 ≤ len word2') (h2'_hi : len word2' ≤ 100000)
    (h2'_range : AllLower word2')
    (h2'_len : len word2' = len word2)
    (h2'_counts : ∀ c, IsLower c → countOcc word2' c = countOcc word2 c), ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1 word2' = ok r' → r = r') := by
  sorry

/-- For every bijection sigma from the set of lowercase letter bytes {97,...,122} to itself, let word1' and word2' be the slices defined by len(word1') = len(word1), len(word2') = len(word2), word1'[i] = sigma(word1[i]) for 0 <= i < len(word1), and word2'[j] = sigma(word2[j]) for 0 <= j < len(word2). Whenever close_strings(word1, word2) returns r and close_strings(word1', word2') returns r', we have r = r'.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_10 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (sigma : Std.U8 → Std.U8) (h_sigma : IsLetterPerm sigma)
    (word1' word2' : Slice Std.U8)
    (h1' : word1'.val = word1.val.map sigma)
    (h2' : word2'.val = word2.val.map sigma) :
    ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (sigma : Std.U8 → Std.U8) (h_sigma : IsLetterPerm sigma)
    (word1' word2' : Slice Std.U8)
    (h1' : word1'.val = word1.val.map sigma)
    (h2' : word2'.val = word2.val.map sigma), ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2' = ok r' → r = r') := by
  sorry

/-- For every pair of distinct lowercase letters c and d that both occur in word1, let word1' be obtained from word1 by replacing every occurrence of c with d and every occurrence of d with c, leaving all other bytes unchanged. Whenever close_strings(word1, word2) returns r and close_strings(word1', word2) returns r', we have r = r'.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_11 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (c d : Std.U8) (hc : IsLower c) (hd : IsLower d) (h_cd : c ≠ d)
    (hc_occ : Occurs word1 c) (hd_occ : Occurs word1 d)
    (word1' : Slice Std.U8)
    (h1' : word1'.val = word1.val.map (swapByte c d)) :
    ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2 = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (c d : Std.U8) (hc : IsLower c) (hd : IsLower d) (h_cd : c ≠ d)
    (hc_occ : Occurs word1 c) (hd_occ : Occurs word1 d)
    (word1' : Slice Std.U8)
    (h1' : word1'.val = word1.val.map (swapByte c d)), ∀ r r', close_strings word1 word2 = ok r →
      close_strings word1' word2 = ok r' → r = r') := by
  sorry

/-- Whenever close_strings(word1, word2) returns a result r, r = true if and only if c = d and len(word1) = len(word2).
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122; there exist lowercase letters c and d such that every byte of word1 equals c and every byte of word2 equals d. -/
theorem spec_12 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (c d : Std.U8) (hc : IsLower c) (hd : IsLower d)
    (h1_const : ∀ b ∈ word1.val, b = c) (h2_const : ∀ b ∈ word2.val, b = d) :
    ∀ r, close_strings word1 word2 = ok r → (r = true ↔ c = d ∧ len word1 = len word2) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (c d : Std.U8) (hc : IsLower c) (hd : IsLower d)
    (h1_const : ∀ b ∈ word1.val, b = c) (h2_const : ∀ b ∈ word2.val, b = d), ∀ r, close_strings word1 word2 = ok r → (r = true ↔ c = d ∧ len word1 = len word2)) := by
  sorry

/-- Whenever close_strings(word1, word2) returns true, let S be the set of lowercase letters occurring in word1. Then S is also the set of lowercase letters occurring in word2, and there exists a bijection f from S to S such that, for every c in S, the number of occurrences of f(c) in word2 equals the number of occurrences of c in word1.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122. -/
theorem spec_13 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2) :
    close_strings word1 word2 = ok true →
      ((∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) ∧
        ∃ f : Std.U8 → Std.U8,
          (∀ c, IsLower c → Occurs word1 c → IsLower (f c) ∧ Occurs word2 (f c)) ∧
            (∀ c, IsLower c → Occurs word1 c → countOcc word2 (f c) = countOcc word1 c) ∧
              (∀ c d, IsLower c → IsLower d → Occurs word1 c → Occurs word1 d →
                f c = f d → c = d) ∧
                (∀ c, IsLower c → Occurs word2 c →
                  ∃ d, IsLower d ∧ Occurs word1 d ∧ f d = c)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2), close_strings word1 word2 = ok true →
      ((∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) ∧
        ∃ f : Std.U8 → Std.U8,
          (∀ c, IsLower c → Occurs word1 c → IsLower (f c) ∧ Occurs word2 (f c)) ∧
            (∀ c, IsLower c → Occurs word1 c → countOcc word2 (f c) = countOcc word1 c) ∧
              (∀ c d, IsLower c → IsLower d → Occurs word1 c → Occurs word1 d →
                f c = f d → c = d) ∧
                (∀ c, IsLower c → Occurs word2 c →
                  ∃ d, IsLower d ∧ Occurs word1 d ∧ f d = c))) := by
  sorry

/-- Whenever close_strings(word1, word2) returns a result r, r = true if and only if for every integer k >= 1, the number of lowercase letters occurring exactly k times in word1 equals the number of lowercase letters occurring exactly k times in word2.
  Preconditions: 1 <= len(word1) <= 100000 and 1 <= len(word2) <= 100000; every byte of word1 and word2 lies in the inclusive range 97..122; len(word1) = len(word2); for every lowercase letter c, c occurs in word1 if and only if c occurs in word2. -/
theorem spec_14 (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_len : len word1 = len word2)
    (h_occ : ∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)) :
    ∀ r, close_strings word1 word2 = ok r →
      (r = true ↔
        ∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8)
    (h1_lo : 1 ≤ len word1) (h1_hi : len word1 ≤ 100000)
    (h2_lo : 1 ≤ len word2) (h2_hi : len word2 ≤ 100000)
    (h1_range : AllLower word1) (h2_range : AllLower word2)
    (h_len : len word1 = len word2)
    (h_occ : ∀ c, IsLower c → (Occurs word1 c ↔ Occurs word2 c)), ∀ r, close_strings word1 word2 = ok r →
      (r = true ↔
        ∀ k, 1 ≤ k → numLettersWithCount word1 k = numLettersWithCount word2 k)) := by
  sorry

end AegisSpec.CloseStrings
