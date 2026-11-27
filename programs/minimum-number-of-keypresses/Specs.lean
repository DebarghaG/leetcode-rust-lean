import Aegis.MinimumKeypresses.Code.Funs

/-!
# Specifications of `Aegis.MinimumKeypresses.minimum_keypresses`

LeetCode problem `minimum-number-of-keypresses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumKeypresses

  def freq (s : Slice Std.U8) (c : ℕ) : ℕ :=
    (s.val.filter (fun b => b.val == c)).length

  def freqs (s : Slice Std.U8) : List ℕ :=
    (List.range 26).map (fun k => freq s (97 + k))

  def sortedFreqs (s : Slice Std.U8) : List ℕ :=
    (freqs s).mergeSort (fun a b => a ≥ b)

  def topNine (s : Slice Std.U8) : ℕ :=
    ((sortedFreqs s).take 9).sum

  def tenthLargest (s : Slice Std.U8) : ℕ :=
    (sortedFreqs s).getD 9 0

  def numDistinct (s : Slice Std.U8) : ℕ :=
    (freqs s).countP (fun n => decide (0 < n))

  def optimalPresses (s : Slice Std.U8) : ℤ :=
    ((((sortedFreqs s).take 9).sum : ℕ) : ℤ)
      + 2 * (((((sortedFreqs s).drop 9).take 9).sum : ℕ) : ℤ)
      + 3 * (((((sortedFreqs s).drop 18).sum : ℕ)) : ℤ)

  structure Keypad where

    buttons : List (List ℕ)

  namespace Keypad

  def IsLetter (c : ℕ) : Prop :=
    97 ≤ c ∧ c ≤ 122

  def Valid (k : Keypad) : Prop :=
    k.buttons.length ≤ 9
      ∧ (∀ b ∈ k.buttons, b.length ≤ 3)
      ∧ (∀ b ∈ k.buttons, b.Nodup)
      ∧ (∀ b ∈ k.buttons, ∀ c ∈ b, IsLetter c)
      ∧ k.buttons.flatten.Nodup
      ∧ (∀ c, IsLetter c → c ∈ k.buttons.flatten)

  def presses (k : Keypad) (c : ℕ) : ℕ :=
    (k.buttons.map (fun b => if c ∈ b then b.idxOf c + 1 else 0)).sum

  def totalPresses (k : Keypad) (s : Slice Std.U8) : ℕ :=
    (s.val.map (fun b => k.presses b.val)).sum

  end Keypad

  /-- Let cnt(c) be the number of indices i with 0 <= i < len(s) and s[i] = c, for c in {'a',...,'z'}. Let f1 >= f2 >= ... >= f26 be the 26 numbers cnt('a'),...,cnt('z') sorted in non-increasing order. The function returns a result r (it does not fail), and r = (f1 + ... + f9) + 2*(f10 + ... + f18) + 3*(f19 + ... + f26).
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is a lowercase ASCII letter). -/
  theorem spec_1 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
        r.val = optimalPresses s := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          r.val = optimalPresses s) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, overflow, or panic.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r) := by
    sorry

  /-- Let cnt(c) be the number of indices i with 0 <= i < len(s) and s[i] = c, for c in {'a',...,'z'}. Let T be the sum of the nine largest values among {cnt('a'),...,cnt('z')}. Whenever the function returns a result r, r >= 2*len(s) - T.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
        2 * (s.val.length : ℤ) - (topNine s : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
          2 * (s.val.length : ℤ) - (topNine s : ℤ) ≤ r.val) := by
    sorry

  /-- Let cnt(c) be the number of indices i with 0 <= i < len(s) and s[i] = c, for c in {'a',...,'z'}. Let T be the sum of the nine largest values among {cnt('a'),...,cnt('z')}. Whenever the function returns a result r, r <= 3*len(s) - 2*T.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
        r.val ≤ 3 * (s.val.length : ℤ) - 2 * (topNine s : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
          r.val ≤ 3 * (s.val.length : ℤ) - 2 * (topNine s : ℤ)) := by
    sorry

  /-- The function returns a result r and r = len(s).
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let cnt(c) be the number of indices i with s[i] = c, and let d be the number of c in {'a',...,'z'} with cnt(c) > 0. Assume d <= 9. -/
  theorem spec_5 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (h_distinct : numDistinct s ≤ 9) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
        r.val = (s.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (h_distinct : numDistinct s ≤ 9), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          r.val = (s.val.length : ℤ)) := by
    sorry

  /-- Let m be the minimum of cnt(c) over those 10 letters c with cnt(c) > 0 (equivalently, m is the 10th largest of the 26 frequencies). The function returns a result r and r = len(s) + m.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let cnt(c) be the number of indices i with s[i] = c, and assume exactly 10 lowercase letters c have cnt(c) > 0. -/
  theorem spec_6 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (h_distinct : numDistinct s = 10) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
        r.val = (s.val.length : ℤ) + (tenthLargest s : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (h_distinct : numDistinct s = 10), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          r.val = (s.val.length : ℤ) + (tenthLargest s : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r >= len(s) + 25.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let cnt(c) be the number of indices i with s[i] = c, and assume cnt(c) >= 1 for every c in {'a',...,'z'}. -/
  theorem spec_7 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (h_all_letters : ∀ k : ℕ, k < 26 → 1 ≤ freq s (97 + k)) :
      ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
        (s.val.length : ℤ) + 25 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (h_all_letters : ∀ k : ℕ, k < 26 → 1 ≤ freq s (97 + k)), ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
          (s.val.length : ℤ) + 25 ≤ r.val) := by
    sorry

  /-- Let r be the value the function returns on s. If cnt_t(c) = cnt_s(c) for every c in {'a',...,'z'}, then the value the function returns on t is also r.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let cnt_s(c) be the number of occurrences of c in s. Let t be any slice satisfying the same length and alphabet constraints, and let cnt_t(c) be the number of occurrences of c in t. -/
  theorem spec_8 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
        ∀ t : Slice Std.U8, 1 ≤ t.val.length → t.val.length ≤ 100000 →
          (∀ (i : ℕ) (hi : i < t.val.length),
            97 ≤ (t.val[i]).val ∧ (t.val[i]).val ≤ 122) →
          (∀ k : ℕ, k < 26 → freq t (97 + k) = freq s (97 + k)) →
          Aegis.MinimumKeypresses.minimum_keypresses t = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
          ∀ t : Slice Std.U8, 1 ≤ t.val.length → t.val.length ≤ 100000 →
            (∀ (i : ℕ) (hi : i < t.val.length),
              97 ≤ (t.val[i]).val ∧ (t.val[i]).val ≤ 122) →
            (∀ k : ℕ, k < 26 → freq t (97 + k) = freq s (97 + k)) →
            Aegis.MinimumKeypresses.minimum_keypresses t = ok r) := by
    sorry

  /-- Let a valid keypad setup be a partition of the 26 lowercase letters into at most 9 ordered lists (the buttons), each list of length at most 3, where the p-th letter of a list (1 <= p <= length) is typed by p presses. The function returns a result r, and there exists a valid keypad setup such that the total number of presses needed to type s under that setup is exactly r.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
        ∃ k : Keypad, k.Valid ∧ (k.totalPresses s : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          ∃ k : Keypad, k.Valid ∧ (k.totalPresses s : ℤ) = r.val) := by
    sorry

  /-- Let a valid keypad setup be a partition of the 26 lowercase letters into at most 9 ordered lists (the buttons), each list of length at most 3, where the p-th letter of a list (1 <= p <= length) is typed by p presses. The function returns a result r, and for every valid keypad setup, the total number of presses needed to type s under that setup is at least r.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_10 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122) :
      ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
        ∀ k : Keypad, k.Valid → r.val ≤ (k.totalPresses s : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122), ∃ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          ∀ k : Keypad, k.Valid → r.val ≤ (k.totalPresses s : ℤ)) := by
    sorry

  /-- Let T be the sum of the nine largest values among {cnt('a'),...,cnt('z')}. Whenever the function returns a result r, r > 2*len(s) - T.
    Preconditions: 1 <= len(s) <= 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let cnt(c) be the number of indices i with s[i] = c, and assume the number d of c in {'a',...,'z'} with cnt(c) > 0 is at least 19. -/
  theorem spec_11 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (h_distinct : 19 ≤ numDistinct s) :
      ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
        2 * (s.val.length : ℤ) - (topNine s : ℤ) < r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (h_distinct : 19 ≤ numDistinct s), ∀ r : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r →
          2 * (s.val.length : ℤ) - (topNine s : ℤ) < r.val) := by
    sorry

  /-- The function returns a result r on s and a result r' on s', and r + 1 <= r' <= r + 3.
    Preconditions: 1 <= len(s) < 100000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let c be any byte with 97 <= c <= 122, and let s' be the slice obtained by appending c to s, so len(s') = len(s) + 1. -/
  theorem spec_12 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_lt : s.val.length < 100000)
      (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
        97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
      (c : Std.U8) (h_c : 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ t : Slice Std.U8, t.val = s.val ++ [c] →
        ∃ r r' : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
          Aegis.MinimumKeypresses.minimum_keypresses t = ok r' ∧
          r.val + 1 ≤ r'.val ∧ r'.val ≤ r.val + 3 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_lt : s.val.length < 100000)
        (h_alphabet : ∀ (i : ℕ) (hi : i < s.val.length),
          97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
        (c : Std.U8) (h_c : 97 ≤ c.val ∧ c.val ≤ 122), ∀ t : Slice Std.U8, t.val = s.val ++ [c] →
          ∃ r r' : Std.I64, Aegis.MinimumKeypresses.minimum_keypresses s = ok r ∧
            Aegis.MinimumKeypresses.minimum_keypresses t = ok r' ∧
            r.val + 1 ≤ r'.val ∧ r'.val ≤ r.val + 3) := by
    sorry

  end AegisSpec.MinimumKeypresses
