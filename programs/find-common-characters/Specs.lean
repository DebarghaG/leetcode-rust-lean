import Aegis.CommonChars.Code.Funs

/-!
# Specifications of `Aegis.CommonChars.common_chars`

LeetCode problem `find-common-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CommonChars (common_chars)

namespace AegisSpec.CommonChars

def count (c : Nat) : List U8 → Nat
  | [] => 0
  | b :: bs => (if b.val = c then 1 else 0) + count c bs

def copies (c : Nat) : List (alloc.vec.Vec U8) → Nat
  | [] => 0
  | w :: ws =>
    (match w.val with
      | [b] => if b.val = c then 1 else 0
      | _ => 0) + copies c ws

def minCount (c : Nat) (words : List (alloc.vec.Vec U8)) : Nat :=
  match words with
  | [] => 0
  | w :: ws => ws.foldl (fun acc v => Nat.min acc (count c v.val)) (count c w.val)

def isLetterByte (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

/-- Whenever the function returns a result r, the following holds. For every j with 0 <= j < len(r), len(r[j]) = 1 and 97 <= r[j][0] <= 122. For every byte c with 97 <= c <= 122, copies(r,c) = min { count(c, words[i]) | 0 <= i < len(words) }, where count(c, xs) is the number of indices k with 0 <= k < len(xs) and xs[k] = c, and copies(r,c) is the number of indices j with 0 <= j < len(r), len(r[j]) = 1, and r[j][0] = c.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_1
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∀ r, common_chars words = ok r →
      (∀ (j : Nat) (hj : j < r.val.length),
        ∃ b, (r.val.get ⟨j, hj⟩).val = [b] ∧ 97 ≤ b.val ∧ b.val ≤ 122) ∧
      (∀ c, isLetterByte c → copies c r.val = minCount c words.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∀ r, common_chars words = ok r →
      (∀ (j : Nat) (hj : j < r.val.length),
        ∃ b, (r.val.get ⟨j, hj⟩).val = [b] ∧ 97 ≤ b.val ∧ b.val ≤ 122) ∧
      (∀ c, isLetterByte c → copies c r.val = minCount c words.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_2
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∃ r, common_chars words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∃ r, common_chars words = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(words), len(r) <= len(words[i]).
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_3
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∀ r, common_chars words = ok r →
      ∀ (i : Nat) (hi : i < words.val.length),
        r.val.length ≤ (words.val.get ⟨i, hi⟩).val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∀ r, common_chars words = ok r →
      ∀ (i : Nat) (hi : i < words.val.length),
        r.val.length ≤ (words.val.get ⟨i, hi⟩).val.length) := by
  sorry

/-- Whenever the function returns a result r, len(r) = sum over c from 97 to 122 of min { count(c, words[i]) | 0 <= i < len(words) }, where count(c, xs) is the number of indices k with 0 <= k < len(xs) and xs[k] = c.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_4
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∀ r, common_chars words = ok r →
      r.val.length = ∑ c ∈ Finset.Icc 97 122, minCount c words.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∀ r, common_chars words = ok r →
      r.val.length = ∑ c ∈ Finset.Icc 97 122, minCount c words.val) := by
  sorry

/-- Whenever the function returns a result r, for every byte c with 97 <= c <= 122 and every i with 0 <= i < len(words), copies(r,c) <= count(c, words[i]), where count(c, xs) is the number of indices k with 0 <= k < len(xs) and xs[k] = c, and copies(r,c) is the number of indices j with 0 <= j < len(r), len(r[j]) = 1, and r[j][0] = c.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_5
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∀ r, common_chars words = ok r →
      ∀ c, isLetterByte c →
        ∀ (i : Nat) (hi : i < words.val.length),
          copies c r.val ≤ count c (words.val.get ⟨i, hi⟩).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∀ r, common_chars words = ok r →
      ∀ c, isLetterByte c →
        ∀ (i : Nat) (hi : i < words.val.length),
          copies c r.val ≤ count c (words.val.get ⟨i, hi⟩).val) := by
  sorry

/-- Whenever the function returns a result r, for every byte c with 97 <= c <= 122 and every integer k >= 0, if count(c, words[i]) >= k for every i with 0 <= i < len(words), then copies(r,c) >= k, where count(c, xs) is the number of indices k' with 0 <= k' < len(xs) and xs[k'] = c, and copies(r,c) is the number of indices j with 0 <= j < len(r), len(r[j]) = 1, and r[j][0] = c.
  Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100; for every i and j with 0 <= i < len(words) and 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
theorem spec_6
    (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122) :
    ∀ r, common_chars words = ok r →
      ∀ c, isLetterByte c → ∀ k : Nat,
        (∀ (i : Nat) (hi : i < words.val.length),
          count c (words.val.get ⟨i, hi⟩).val ≥ k) →
        copies c r.val ≥ k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec U8))
    (hlen_lo : 1 ≤ words.val.length) (hlen_hi : words.val.length ≤ 100)
    (hword_len : ∀ (i : Nat) (hi : i < words.val.length),
      1 ≤ (words.val.get ⟨i, hi⟩).val.length ∧ (words.val.get ⟨i, hi⟩).val.length ≤ 100)
    (hbyte : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
      (hj : j < (words.val.get ⟨i, hi⟩).val.length),
      97 ≤ ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ∧
        ((words.val.get ⟨i, hi⟩).val.get ⟨j, hj⟩).val ≤ 122), ∀ r, common_chars words = ok r →
      ∀ c, isLetterByte c → ∀ k : Nat,
        (∀ (i : Nat) (hi : i < words.val.length),
          count c (words.val.get ⟨i, hi⟩).val ≥ k) →
        copies c r.val ≥ k) := by
  sorry

end AegisSpec.CommonChars
