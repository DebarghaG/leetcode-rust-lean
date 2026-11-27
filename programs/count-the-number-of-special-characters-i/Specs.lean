import Aegis.NumberOfSpecialChars.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSpecialChars.number_of_special_chars`

LeetCode problem `count-the-number-of-special-characters-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfSpecialChars

  def IsUpperByte (b : Nat) : Prop := 65 ≤ b ∧ b ≤ 90

  def IsLowerByte (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

  def AllLetters (w : Slice Std.U8) : Prop :=
    ∀ i : Fin w.val.length, IsUpperByte (w.val.get i).val ∨ IsLowerByte (w.val.get i).val

  def OccursIn (w : Slice Std.U8) (b : Nat) : Prop :=
    ∃ i : Fin w.val.length, (w.val.get i).val = b

  noncomputable def specialCount (w : Slice Std.U8) : Nat := by
    classical
    exact ((Finset.range 26).filter
      (fun c => OccursIn w (97 + c) ∧ OccursIn w (65 + c))).card

  noncomputable def lowerCount (w : Slice Std.U8) : Nat := by
    classical
    exact ((Finset.range 26).filter (fun c => OccursIn w (97 + c))).card

  noncomputable def upperCount (w : Slice Std.U8) : Nat := by
    classical
    exact ((Finset.range 26).filter (fun c => OccursIn w (65 + c))).card

  /-- Whenever number_of_special_chars(word) returns a result r, r is exactly the number of integers c with 0 <= c <= 25 such that there exists i with 0 <= i < len(word) and word[i] = 97 + c, and there exists j with 0 <= j < len(word) and word[j] = 65 + c. Equivalently, r is the number of English letters (with c = 0 meaning a or A, ..., c = 25 meaning z or Z) for which both the lowercase byte and the uppercase byte occur somewhere in word.
    Preconditions: len(word) >= 1 and for every i with 0 <= i < len(word), word[i] is an ASCII code in 65..90 (uppercase English letters) or in 97..122 (lowercase English letters). -/
  theorem spec_1 (word : Slice Std.U8)
      (hlen : 1 ≤ word.val.length)
      (hbytes : AllLetters word)
      (r : Std.I64)
      (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r) :
      r.val = (specialCount word : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen : 1 ≤ word.val.length)
        (hbytes : AllLetters word)
        (r : Std.I64)
        (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r), r.val = (specialCount word : Int)) := by
    sorry

  /-- For every word satisfying the preconditions, number_of_special_chars(word) returns a result r; evaluation does not panic, access an out-of-bounds index, or overflow.
    Preconditions: len(word) >= 1 and for every i with 0 <= i < len(word), word[i] is an ASCII code in 65..90 or in 97..122. -/
  theorem spec_2 (word : Slice Std.U8)
      (hlen : 1 ≤ word.val.length)
      (hbytes : AllLetters word) :
      ∃ r : Std.I64, Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen : 1 ≤ word.val.length)
        (hbytes : AllLetters word), ∃ r : Std.I64, Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r) := by
    sorry

  /-- Whenever number_of_special_chars(word) returns a result r, 0 <= r <= 26.
    Preconditions: len(word) >= 1 and for every i with 0 <= i < len(word), word[i] is an ASCII code in 65..90 or in 97..122. -/
  theorem spec_3 (word : Slice Std.U8)
      (hlen : 1 ≤ word.val.length)
      (hbytes : AllLetters word)
      (r : Std.I64)
      (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r) :
      0 ≤ r.val ∧ r.val ≤ 26 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen : 1 ≤ word.val.length)
        (hbytes : AllLetters word)
        (r : Std.I64)
        (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r), 0 ≤ r.val ∧ r.val ≤ 26) := by
    sorry

  /-- If for every c with 0 <= c <= 25, byte 97 + c occurs in u if and only if byte 97 + c occurs in v, and byte 65 + c occurs in u if and only if byte 65 + c occurs in v, then whenever number_of_special_chars(u) returns r_u and number_of_special_chars(v) returns r_v, r_u = r_v. Here byte b occurs in a slice w means there exists i with 0 <= i < len(w) and w[i] = b.
    Preconditions: u and v are byte slices, each of length at least 1, and every byte of each slice is an ASCII code in 65..90 or in 97..122. -/
  theorem spec_4 (u v : Slice Std.U8)
      (hu : 1 ≤ u.val.length)
      (hv : 1 ≤ v.val.length)
      (hbu : AllLetters u)
      (hbv : AllLetters v)
      (hocc : ∀ c : Nat, c ≤ 25 →
        ((OccursIn u (97 + c) ↔ OccursIn v (97 + c)) ∧
         (OccursIn u (65 + c) ↔ OccursIn v (65 + c))))
      (r_u r_v : Std.I64)
      (hr_u : Aegis.NumberOfSpecialChars.number_of_special_chars u = ok r_u)
      (hr_v : Aegis.NumberOfSpecialChars.number_of_special_chars v = ok r_v) :
      r_u.val = r_v.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (u v : Slice Std.U8)
        (hu : 1 ≤ u.val.length)
        (hv : 1 ≤ v.val.length)
        (hbu : AllLetters u)
        (hbv : AllLetters v)
        (hocc : ∀ c : Nat, c ≤ 25 →
          ((OccursIn u (97 + c) ↔ OccursIn v (97 + c)) ∧
           (OccursIn u (65 + c) ↔ OccursIn v (65 + c))))
        (r_u r_v : Std.I64)
        (hr_u : Aegis.NumberOfSpecialChars.number_of_special_chars u = ok r_u)
        (hr_v : Aegis.NumberOfSpecialChars.number_of_special_chars v = ok r_v), r_u.val = r_v.val) := by
    sorry

  /-- Whenever number_of_special_chars(word) returns r and number_of_special_chars(word2) returns r2, let c be the letter index such that b = 97 + c if b is lowercase, or b = 65 + c if b is uppercase, and let opposite be 65 + c in the first case or 97 + c in the second case. Then: if b occurs in word, r2 = r; if b does not occur in word and opposite occurs in word, r2 = r + 1; if b does not occur in word and opposite does not occur in word, r2 = r.
    Preconditions: word is a byte slice with len(word) >= 1 and every byte in 65..90 or 97..122. Let word2 be the byte slice of length len(word) + 1 defined by word2[i] = word[i] for 0 <= i < len(word) and word2[len(word)] = b, where b is an ASCII lowercase or uppercase English letter. -/
  theorem spec_5 (word : Slice Std.U8) (b : Std.U8) (word2 : Slice Std.U8)
      (hlen : 1 ≤ word.val.length)
      (hbytes : AllLetters word)
      (hb : IsLowerByte b.val ∨ IsUpperByte b.val)
      (h2 : word2.val = word.val ++ [b])
      (c opposite : Nat)
      (hc : c ≤ 25)
      (hcase : (b.val = 97 + c ∧ opposite = 65 + c) ∨
               (b.val = 65 + c ∧ opposite = 97 + c))
      (r r2 : Std.I64)
      (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r)
      (hr2 : Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2) :
      (OccursIn word b.val → r2.val = r.val) ∧
      (¬ OccursIn word b.val → OccursIn word opposite → r2.val = r.val + 1) ∧
      (¬ OccursIn word b.val → ¬ OccursIn word opposite → r2.val = r.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8) (b : Std.U8) (word2 : Slice Std.U8)
        (hlen : 1 ≤ word.val.length)
        (hbytes : AllLetters word)
        (hb : IsLowerByte b.val ∨ IsUpperByte b.val)
        (h2 : word2.val = word.val ++ [b])
        (c opposite : Nat)
        (hc : c ≤ 25)
        (hcase : (b.val = 97 + c ∧ opposite = 65 + c) ∨
                 (b.val = 65 + c ∧ opposite = 97 + c))
        (r r2 : Std.I64)
        (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r)
        (hr2 : Aegis.NumberOfSpecialChars.number_of_special_chars word2 = ok r2), (OccursIn word b.val → r2.val = r.val) ∧
        (¬ OccursIn word b.val → OccursIn word opposite → r2.val = r.val + 1) ∧
        (¬ OccursIn word b.val → ¬ OccursIn word opposite → r2.val = r.val)) := by
    sorry

  /-- Whenever number_of_special_chars(word) returns a result r, r is at most the number of distinct c with 0 <= c <= 25 for which byte 97 + c occurs in word, and r is at most the number of distinct c with 0 <= c <= 25 for which byte 65 + c occurs in word. A letter index c is counted once in each of these two numbers even if its byte occurs many times.
    Preconditions: len(word) >= 1 and for every i with 0 <= i < len(word), word[i] is an ASCII code in 65..90 or in 97..122. -/
  theorem spec_6 (word : Slice Std.U8)
      (hlen : 1 ≤ word.val.length)
      (hbytes : AllLetters word)
      (r : Std.I64)
      (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r) :
      r.val ≤ (lowerCount word : Int) ∧ r.val ≤ (upperCount word : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8)
        (hlen : 1 ≤ word.val.length)
        (hbytes : AllLetters word)
        (r : Std.I64)
        (hr : Aegis.NumberOfSpecialChars.number_of_special_chars word = ok r), r.val ≤ (lowerCount word : Int) ∧ r.val ≤ (upperCount word : Int)) := by
    sorry

  end AegisSpec.NumberOfSpecialChars
