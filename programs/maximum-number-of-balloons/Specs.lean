import Aegis.MaxNumberOfBalloons.Code.Funs

/-!
# Specifications of `Aegis.MaxNumberOfBalloons.max_number_of_balloons`

LeetCode problem `maximum-number-of-balloons`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxNumberOfBalloons

  open Aegis.MaxNumberOfBalloons (max_number_of_balloons)

  def byte (n : Nat) : Std.U8 := ⟨BitVec.ofNat 8 n⟩

  def count (c : Nat) (text : Slice Std.U8) : Nat :=
    (text.val.filter fun b => b.val = c).length

  def lowerCaseBytes (text : Slice Std.U8) : Prop :=
    ∀ b ∈ text.val, 97 ≤ b.val ∧ b.val ≤ 122

  def pre (text : Slice Std.U8) : Prop :=
    lowerCaseBytes text ∧ text.val.length ≤ 10000

  def feasible (k : Nat) (text : Slice Std.U8) : Prop :=
    k ≤ count 98 text ∧ k ≤ count 97 text ∧ 2 * k ≤ count 108 text ∧
      2 * k ≤ count 111 text ∧ k ≤ count 110 text

  def balloons (text : Slice Std.U8) : Nat :=
    min (count 98 text)
      (min (count 97 text)
        (min (count 108 text / 2) (min (count 111 text / 2) (count 110 text))))

  /-- Let count(c, text) be the number of indices i with 0 <= i < len(text) and text[i] = c, where c is an ASCII byte. The function returns a result r and r = min(count('b', text), count('a', text), count('l', text) / 2, count('o', text) / 2, count('n', text)), where division by 2 is integer division rounding down. Equivalently, r is the largest integer k >= 0 such that count('b', text) >= k, count('a', text) >= k, count('l', text) >= 2*k, count('o', text) >= 2*k, and count('n', text) >= k.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_1 (text : Slice Std.U8) (h : pre text) :
      ∃ r : Std.I64,
        max_number_of_balloons text = ok r ∧
          r.val = (balloons text : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text), ∃ r : Std.I64,
          max_number_of_balloons text = ok r ∧
            r.val = (balloons text : Int)) := by
    sorry

  /-- For every text satisfying the preconditions, the function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_2 (text : Slice Std.U8) (h : pre text) :
      ∃ r : Std.I64, max_number_of_balloons text = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text), ∃ r : Std.I64, max_number_of_balloons text = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is non-negative, i.e., r >= 0.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_3 (text : Slice Std.U8) (h : pre text) (r : Std.I64)
      (hr : max_number_of_balloons text = ok r) : 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (r : Std.I64)
        (hr : max_number_of_balloons text = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 7 * r <= len(text). Equivalently, r <= floor(len(text) / 7).
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_4 (text : Slice Std.U8) (h : pre text) (r : Std.I64)
      (hr : max_number_of_balloons text = ok r) :
      7 * r.val ≤ (text.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (r : Std.I64)
        (hr : max_number_of_balloons text = ok r), 7 * r.val ≤ (text.val.length : Int)) := by
    sorry

  /-- If len(text) < 7, then whenever the function returns a result r, r = 0.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_5 (text : Slice Std.U8) (h : pre text) (hlen : text.val.length < 7)
      (r : Std.I64) (hr : max_number_of_balloons text = ok r) : r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (hlen : text.val.length < 7)
        (r : Std.I64) (hr : max_number_of_balloons text = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, all of the following hold: r <= count('b', text), r <= count('a', text), 2*r <= count('l', text), 2*r <= count('o', text), and r <= count('n', text), where count(c, text) is the number of indices i with 0 <= i < len(text) and text[i] = c.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_6 (text : Slice Std.U8) (h : pre text) (r : Std.I64)
      (hr : max_number_of_balloons text = ok r) :
      r.val ≤ (count 98 text : Int) ∧
        r.val ≤ (count 97 text : Int) ∧
          2 * r.val ≤ (count 108 text : Int) ∧
            2 * r.val ≤ (count 111 text : Int) ∧ r.val ≤ (count 110 text : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (r : Std.I64)
        (hr : max_number_of_balloons text = ok r), r.val ≤ (count 98 text : Int) ∧
          r.val ≤ (count 97 text : Int) ∧
            2 * r.val ≤ (count 108 text : Int) ∧
              2 * r.val ≤ (count 111 text : Int) ∧ r.val ≤ (count 110 text : Int)) := by
    sorry

  /-- For every integer k >= 0, if count('b', text) >= k, count('a', text) >= k, count('l', text) >= 2*k, count('o', text) >= 2*k, and count('n', text) >= k, then whenever the function returns a result r, r >= k. Here count(c, text) is the number of indices i with 0 <= i < len(text) and text[i] = c.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_7 (text : Slice Std.U8) (h : pre text) (k : Nat) (hk : feasible k text)
      (r : Std.I64) (hr : max_number_of_balloons text = ok r) : (k : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (k : Nat) (hk : feasible k text)
        (r : Std.I64) (hr : max_number_of_balloons text = ok r), (k : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if at least one of the following holds: count('b', text) = 0, count('a', text) = 0, count('l', text) < 2, count('o', text) < 2, or count('n', text) = 0. Here count(c, text) is the number of indices i with 0 <= i < len(text) and text[i] = c.
    Preconditions: Every byte of text is an ASCII lower-case English letter: for every i with 0 <= i < len(text), 97 <= text[i] <= 122. Also len(text) <= 10000. The empty slice is allowed. -/
  theorem spec_8 (text : Slice Std.U8) (h : pre text) (r : Std.I64)
      (hr : max_number_of_balloons text = ok r) :
      r.val = 0 ↔
        (count 98 text = 0 ∨ count 97 text = 0 ∨ count 108 text < 2 ∨
          count 111 text < 2 ∨ count 110 text = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (text : Slice Std.U8) (h : pre text) (r : Std.I64)
        (hr : max_number_of_balloons text = ok r), r.val = 0 ↔
          (count 98 text = 0 ∨ count 97 text = 0 ∨ count 108 text < 2 ∨
            count 111 text < 2 ∨ count 110 text = 0)) := by
    sorry

  /-- For any two byte slices text1 and text2 satisfying the preconditions, if count('b', text1) = count('b', text2), count('a', text1) = count('a', text2), count('l', text1) = count('l', text2), count('o', text1) = count('o', text2), and count('n', text1) = count('n', text2), then whenever max_number_of_balloons(text1) returns r1 and max_number_of_balloons(text2) returns r2, r1 = r2. Here count(c, text) is the number of indices i with 0 <= i < len(text) and text[i] = c.
    Preconditions: For text1 and text2 respectively, every byte is an ASCII lower-case English letter: for every i with 0 <= i < len(text1), 97 <= text1[i] <= 122, and for every i with 0 <= i < len(text2), 97 <= text2[i] <= 122; also len(text1) <= 10000 and len(text2) <= 10000. The empty slice is allowed. -/
  theorem spec_9 (text1 text2 : Slice Std.U8) (h1 : pre text1) (h2 : pre text2)
      (hb : count 98 text1 = count 98 text2) (ha : count 97 text1 = count 97 text2)
      (hl : count 108 text1 = count 108 text2) (ho : count 111 text1 = count 111 text2)
      (hn : count 110 text1 = count 110 text2) (r1 r2 : Std.I64)
      (hr1 : max_number_of_balloons text1 = ok r1)
      (hr2 : max_number_of_balloons text2 = ok r2) : r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (h1 : pre text1) (h2 : pre text2)
        (hb : count 98 text1 = count 98 text2) (ha : count 97 text1 = count 97 text2)
        (hl : count 108 text1 = count 108 text2) (ho : count 111 text1 = count 111 text2)
        (hn : count 110 text1 = count 110 text2) (r1 r2 : Std.I64)
        (hr1 : max_number_of_balloons text1 = ok r1)
        (hr2 : max_number_of_balloons text2 = ok r2), r1 = r2) := by
    sorry

  /-- For any lower-case byte slices text and text2 such that len(text2) = len(text) + 7 and text2 is the concatenation of text with the seven bytes 'b', 'a', 'l', 'l', 'o', 'o', 'n' (formally text2[i] = text[i] for 0 <= i < len(text), and text2[len(text)+0] = 'b', text2[len(text)+1] = 'a', text2[len(text)+2] = 'l', text2[len(text)+3] = 'l', text2[len(text)+4] = 'o', text2[len(text)+5] = 'o', text2[len(text)+6] = 'n'), if max_number_of_balloons(text) returns r and max_number_of_balloons(text2) returns r2, then r2 = r + 1.
    Preconditions: Both text and text2 are byte slices whose bytes are ASCII lower-case English letters, and both have length at most 10000. The empty slice is allowed. -/
  theorem spec_10 (text text2 : Slice Std.U8) (h1 : pre text) (h2 : pre text2)
      (hlen : text2.val.length = text.val.length + 7)
      (hcat : text2.val =
        text.val ++ [byte 98, byte 97, byte 108, byte 108, byte 111, byte 111, byte 110])
      (r r2 : Std.I64) (hr : max_number_of_balloons text = ok r)
      (hr2 : max_number_of_balloons text2 = ok r2) : r2.val = r.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (text text2 : Slice Std.U8) (h1 : pre text) (h2 : pre text2)
        (hlen : text2.val.length = text.val.length + 7)
        (hcat : text2.val =
          text.val ++ [byte 98, byte 97, byte 108, byte 108, byte 111, byte 111, byte 110])
        (r r2 : Std.I64) (hr : max_number_of_balloons text = ok r)
        (hr2 : max_number_of_balloons text2 = ok r2), r2.val = r.val + 1) := by
    sorry

  /-- For any lower-case byte slices text and text2 such that len(text2) = len(text) + 1 and text2 is obtained by appending one lower-case English letter c to text, if max_number_of_balloons(text) returns r and max_number_of_balloons(text2) returns r2, then r <= r2 <= r + 1.
    Preconditions: Both text and text2 are byte slices whose bytes are ASCII lower-case English letters, and both have length at most 10000. The empty slice is allowed. -/
  theorem spec_11 (text text2 : Slice Std.U8) (h1 : pre text) (h2 : pre text2)
      (c : Std.U8) (hc : 97 ≤ c.val ∧ c.val ≤ 122)
      (hlen : text2.val.length = text.val.length + 1) (hcat : text2.val = text.val ++ [c])
      (r r2 : Std.I64) (hr : max_number_of_balloons text = ok r)
      (hr2 : max_number_of_balloons text2 = ok r2) :
      r.val ≤ r2.val ∧ r2.val ≤ r.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (text text2 : Slice Std.U8) (h1 : pre text) (h2 : pre text2)
        (c : Std.U8) (hc : 97 ≤ c.val ∧ c.val ≤ 122)
        (hlen : text2.val.length = text.val.length + 1) (hcat : text2.val = text.val ++ [c])
        (r r2 : Std.I64) (hr : max_number_of_balloons text = ok r)
        (hr2 : max_number_of_balloons text2 = ok r2), r.val ≤ r2.val ∧ r2.val ≤ r.val + 1) := by
    sorry

  /-- For any two lower-case byte slices text1 and text2 satisfying the preconditions, if count('b', text1) <= count('b', text2), count('a', text1) <= count('a', text2), count('l', text1) <= count('l', text2), count('o', text1) <= count('o', text2), and count('n', text1) <= count('n', text2), then whenever max_number_of_balloons(text1) returns r1 and max_number_of_balloons(text2) returns r2, r1 <= r2. Here count(c, text) is the number of indices i with 0 <= i < len(text) and text[i] = c.
    Preconditions: For text1 and text2 respectively, every byte is an ASCII lower-case English letter: for every i with 0 <= i < len(text1), 97 <= text1[i] <= 122, and for every i with 0 <= i < len(text2), 97 <= text2[i] <= 122; also len(text1) <= 10000 and len(text2) <= 10000. The empty slice is allowed. -/
  theorem spec_12 (text1 text2 : Slice Std.U8) (h1 : pre text1) (h2 : pre text2)
      (hb : count 98 text1 ≤ count 98 text2) (ha : count 97 text1 ≤ count 97 text2)
      (hl : count 108 text1 ≤ count 108 text2) (ho : count 111 text1 ≤ count 111 text2)
      (hn : count 110 text1 ≤ count 110 text2) (r1 r2 : Std.I64)
      (hr1 : max_number_of_balloons text1 = ok r1)
      (hr2 : max_number_of_balloons text2 = ok r2) : r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (h1 : pre text1) (h2 : pre text2)
        (hb : count 98 text1 ≤ count 98 text2) (ha : count 97 text1 ≤ count 97 text2)
        (hl : count 108 text1 ≤ count 108 text2) (ho : count 111 text1 ≤ count 111 text2)
        (hn : count 110 text1 ≤ count 110 text2) (r1 r2 : Std.I64)
        (hr1 : max_number_of_balloons text1 = ok r1)
        (hr2 : max_number_of_balloons text2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MaxNumberOfBalloons
