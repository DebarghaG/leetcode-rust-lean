import Aegis.DoesAliceWin.Code.Funs

/-!
# Specifications of `Aegis.DoesAliceWin.does_alice_win`

LeetCode problem `vowels-game-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DoesAliceWin

  def Vowel (c : Std.U8) : Prop :=
    c.val = 97 ∨ c.val = 101 ∨ c.val = 105 ∨ c.val = 111 ∨ c.val = 117

  def AllLowerAlpha (s : Slice Std.U8) : Prop :=
    ∀ (i : ℕ) (hi : i < s.val.length), 97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122

  def HasVowel (s : Slice Std.U8) : Prop :=
    ∃ (i : ℕ) (hi : i < s.val.length), Vowel (s.val[i])

  /-- The function returns a result r (it does not fail), and r = true if and only if there exists an index i with 0 <= i < len(s) such that Vowel(s[i]). Equivalently, r is true exactly when Alice has a winning strategy in the stated game, and false otherwise.
    Preconditions: Let Vowel(c) mean c is one of the ASCII bytes 97 ('a'), 101 ('e'), 105 ('i'), 111 ('o'), or 117 ('u'). Assume len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (halpha : AllLowerAlpha s) :
      ∃ r, Aegis.DoesAliceWin.does_alice_win s = ok r ∧ (r = true ↔ HasVowel s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (halpha : AllLowerAlpha s), ∃ r, Aegis.DoesAliceWin.does_alice_win s = ok r ∧ (r = true ↔ HasVowel s)) := by
    sorry

  /-- The function returns a result r (true or false) and does not fail for every s satisfying the preconditions.
    Preconditions: Let Vowel(c) mean c is one of 97 ('a'), 101 ('e'), 105 ('i'), 111 ('o'), or 117 ('u'). Assume len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (halpha : AllLowerAlpha s) :
      ∃ r, Aegis.DoesAliceWin.does_alice_win s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (halpha : AllLowerAlpha s), ∃ r, Aegis.DoesAliceWin.does_alice_win s = ok r) := by
    sorry

  /-- The function returns results r_s on s and r_t on t, and r_s = r_t.
    Preconditions: Let Vowel(c) mean c is one of 97 ('a'), 101 ('e'), 105 ('i'), 111 ('o'), or 117 ('u'). Assume len(s) >= 1, len(s) < 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let c be a byte with 97 <= c <= 122 and not Vowel(c). Let t be the byte array of length len(s)+1 such that t[0] = c and t[i+1] = s[i] for every i with 0 <= i < len(s). -/
  theorem spec_3 (s : Slice Std.U8) (c : Std.U8) (t : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length < 100000)
      (halpha : AllLowerAlpha s)
      (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122) (hc_nvowel : ¬ Vowel c)
      (ht : t.val = c :: s.val) :
      ∃ r_s r_t, Aegis.DoesAliceWin.does_alice_win s = ok r_s ∧
        Aegis.DoesAliceWin.does_alice_win t = ok r_t ∧ r_s = r_t := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (c : Std.U8) (t : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length < 100000)
        (halpha : AllLowerAlpha s)
        (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122) (hc_nvowel : ¬ Vowel c)
        (ht : t.val = c :: s.val), ∃ r_s r_t, Aegis.DoesAliceWin.does_alice_win s = ok r_s ∧
          Aegis.DoesAliceWin.does_alice_win t = ok r_t ∧ r_s = r_t) := by
    sorry

  end AegisSpec.DoesAliceWin
