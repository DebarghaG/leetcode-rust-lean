import Aegis.MaxRepOpt1.Code.Funs

/-!
# Specifications of `Aegis.MaxRepOpt1.max_rep_opt1`

LeetCode problem `swap-for-longest-repeated-character-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxRepOpt1

  def bytes (text : Slice U8) : List ℕ := text.val.map (fun b => b.val)

  def byteAt (text : Slice U8) (i : ℕ) : ℕ := (bytes text).getD i 0

  def win (text : Slice U8) (l u : ℕ) : List ℕ := (bytes text).drop l |>.take (u - l)

  def total (text : Slice U8) (c : ℕ) : ℕ := ((bytes text).filter (fun b => b = c)).length

  def badCount (text : Slice U8) (c l u : ℕ) : ℕ := ((win text l u).filter (fun b => b ≠ c)).length

  def windowOk (text : Slice U8) (c l u : ℕ) : Prop :=
    l ≤ u ∧ u ≤ text.length ∧ badCount text c l u ≤ 1

  def W (text : Slice U8) (c : ℕ) : ℕ :=
    (Finset.range (text.length + 1)).sup fun u =>
      (Finset.range (text.length + 1)).sup fun l =>
        if l ≤ u ∧ badCount text c l u ≤ 1 then u - l else 0

  def occurring (text : Slice U8) : Finset ℕ := (Finset.range 256).filter (fun c => 0 < total text c)

  def answer (text : Slice U8) : ℕ := (occurring text).sup fun c => min (total text c) (W text c)

  def Wmax (text : Slice U8) : ℕ := (Finset.range 256).sup fun c => W text c

  def totalMax (text : Slice U8) : ℕ := (Finset.range 256).sup fun c => total text c

  def maxOccExactlyTwo (text : Slice U8) : Prop :=
    (∃ c, total text c = 2) ∧ ∀ c, total text c ≤ 2

  def allBytesEqual (text : Slice U8) : Prop := ∃ c, ∀ i, i < text.length → byteAt text i = c

  def pairwiseDistinct (text : Slice U8) : Prop :=
    ∀ i j, i < j → j < text.length → byteAt text i ≠ byteAt text j

  def lowercaseInjective (phi : U8 → U8) : Prop :=
    (∀ a, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ (phi a).val ∧ (phi a).val ≤ 122) ∧
      ∀ a b, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ b.val → b.val ≤ 122 → phi a = phi b → a = b

  /-- For a byte value c, let total(c) = #{i | 0 <= i < len(text) and text[i] = c}. For each c with total(c) > 0, let W(c) be the maximum value u-l over all indices 0 <= l <= u <= len(text) such that the interval [l,u) contains at most one index i with text[i] != c. Then the function returns a result r and r = max { min(total(c), W(c)) | c is a byte value that occurs in text }.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_1 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val = (answer text : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val = (answer text : Int)) := by
    sorry

  /-- The function returns a result r and does not fail: for every text satisfying the preconditions there is no overflow, panic, or out-of-bounds access.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_2 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r) := by
    sorry

  /-- The function returns a result r and 1 <= r <= len(text).
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_3 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ 1 ≤ r.val ∧ r.val ≤ (text.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ 1 ≤ r.val ∧ r.val ≤ (text.length : Int)) := by
    sorry

  /-- The function returns a result r and r <= max { total(c) | c is a byte value that occurs in text }, where total(c) = #{i | 0 <= i < len(text) and text[i] = c}.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_4 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val ≤ (totalMax text : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val ≤ (totalMax text : Int)) := by
    sorry

  /-- For every byte value c and all indices 0 <= l <= u <= len(text), if the interval [l,u) contains at most one index i with text[i] != c, then the returned value r satisfies r >= min(u-l, total(c)), where total(c) = #{i | 0 <= i < len(text) and text[i] = c}.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_5 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) (r : I64)
      (hres : Aegis.MaxRepOpt1.max_rep_opt1 text = ok r) :
      ∀ (c l u : ℕ), windowOk text c l u →
        ((min (u - l) (total text c) : ℕ) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) (r : I64)
        (hres : Aegis.MaxRepOpt1.max_rep_opt1 text = ok r), ∀ (c l u : ℕ), windowOk text c l u →
          ((min (u - l) (total text c) : ℕ) : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r and there exist a byte value c and indices 0 <= l <= u <= len(text) such that the interval [l,u) contains at most one index i with text[i] != c, total(c) = #{i | 0 <= i < len(text) and text[i] = c}, and r = min(u-l, total(c)).
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_6 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
        ∃ (c l u : ℕ), windowOk text c l u ∧
          r.val = ((min (u - l) (total text c) : ℕ) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
          ∃ (c l u : ℕ), windowOk text c l u ∧
            r.val = ((min (u - l) (total text c) : ℕ) : Int)) := by
    sorry

  /-- The function returns a result r and r <= W, where W is the maximum value u-l over all byte values c and all indices 0 <= l <= u <= len(text) such that [l,u) contains at most one index i with text[i] != c.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_7 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val ≤ (Wmax text : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val ≤ (Wmax text : Int)) := by
    sorry

  /-- The function returns a result r, and r = len(text) if and only if all bytes of text are equal: there exists a byte c such that text[i] = c for every 0 <= i < len(text).
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_8 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
        (r.val = (text.length : Int) ↔ allBytesEqual text) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
          (r.val = (text.length : Int) ↔ allBytesEqual text)) := by
    sorry

  /-- The function returns a result r, and r = len(text)-1 if and only if there exists a byte value c that occurs at exactly len(text)-1 indices in text (equivalently, exactly one index i has text[i] != c).
    Preconditions: len(text) is between 2 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_9 (text : Slice U8)
      (hlen_low : 2 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
        (r.val = (text.length : Int) - 1 ↔ ∃ c, total text c = text.length - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 2 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
          (r.val = (text.length : Int) - 1 ↔ ∃ c, total text c = text.length - 1)) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if no byte value occurs more than once in text; equivalently, text[i] != text[j] for all 0 <= i < j < len(text).
    Preconditions: len(text) is between 2 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_10 (text : Slice U8)
      (hlen_low : 2 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
        (r.val = 1 ↔ pairwiseDistinct text) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 2 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧
          (r.val = 1 ↔ pairwiseDistinct text)) := by
    sorry

  /-- The function returns a result r and r = 2.
    Preconditions: len(text) is between 1 and 20000 inclusive, every byte of text is a lowercase English letter (ASCII code 97 through 122), and the maximum occurrence count of any byte value in text is exactly 2. -/
  theorem spec_11 (text : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hmax : maxOccExactlyTwo text) :
      ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (text : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hmax : maxOccExactlyTwo text), ∃ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r ∧ r.val = 2) := by
    sorry

  /-- The returned value r is invariant under any consistent injective renaming of the lowercase alphabet: if phi is an injective map from the 26 lowercase letters to lowercase letters and text' is defined by text'[i] = phi(text[i]) for every 0 <= i < len(text), then the correct answer for text' is also r.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_12 (text text' : Slice U8) (phi : U8 → U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hphi : lowercaseInjective phi)
      (hmap : text'.val = text.val.map phi) :
      ∀ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r →
        Aegis.MaxRepOpt1.max_rep_opt1 text' = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (text text' : Slice U8) (phi : U8 → U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hphi : lowercaseInjective phi)
        (hmap : text'.val = text.val.map phi), ∀ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r →
          Aegis.MaxRepOpt1.max_rep_opt1 text' = ok r) := by
    sorry

  /-- The returned value r is unchanged when text is reversed: for text' with text'[i] = text[len(text)-1-i] for every 0 <= i < len(text), the correct answer for text' is also r.
    Preconditions: len(text) is between 1 and 20000 inclusive, and every byte of text is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_13 (text text' : Slice U8)
      (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
      (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hrev : text'.val = text.val.reverse) :
      ∀ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r →
        Aegis.MaxRepOpt1.max_rep_opt1 text' = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (text text' : Slice U8)
        (hlen_low : 1 ≤ text.length) (hlen_high : text.length ≤ 20000)
        (hletters : ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hrev : text'.val = text.val.reverse), ∀ r : I64, Aegis.MaxRepOpt1.max_rep_opt1 text = ok r →
          Aegis.MaxRepOpt1.max_rep_opt1 text' = ok r) := by
    sorry

  end AegisSpec.MaxRepOpt1
