import Aegis.ValidWordSquare.Code.Funs

/-!
# Specifications of `Aegis.ValidWordSquare.valid_word_square`

LeetCode problem `valid-word-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidWordSquare

  def Row (words : Slice (alloc.vec.Vec U8)) (k : Nat) : List U8 :=
    match words.val[k]? with
    | some w => w.val
    | none => []

  def Col (words : Slice (alloc.vec.Vec U8)) (k : Nat) : List U8 :=
    words.val.filterMap fun w => w.val[k]?

  def maxRowLen (words : Slice (alloc.vec.Vec U8)) : Nat :=
    (words.val.map fun w => w.val.length).foldr max 0

  def colCount (words : Slice (alloc.vec.Vec U8)) (k : Nat) : Nat :=
    (words.val.filter fun w => decide (k < w.val.length)).length

  def byteAt (words : Slice (alloc.vec.Vec U8)) (i j : Nat) : U8 :=
    ((Row words i)[j]?).getD 0#u8

  /-- Let n = len(words) and let m = max({len(words[i]) | 0 <= i < n}). The function returns a result r and r = true if and only if, for every integer k with 0 <= k < max(n, m), the row string Row(k) equals the column string Col(k), where Row(k) is the byte sequence words[k][0], words[k][1], ..., words[k][len(words[k])-1] when k < n, and is the empty sequence when k >= n, and Col(k) is the byte sequence consisting of words[i][k], in increasing order of i, for exactly those i with 0 <= i < n and k < len(words[i]). Equality of these sequences means they have the same length and equal bytes in every position.
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_1
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧
        (r = true ↔
          ∀ (k : Nat), k < Nat.max words.val.length (maxRowLen words) → Row words k = Col words k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧
          (r = true ↔
            ∀ (k : Nat), k < Nat.max words.val.length (maxRowLen words) → Row words k = Col words k)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_2
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r) := by
    sorry

  /-- Whenever valid_word_square(words) returns true, then for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), we have j < len(words), i < len(words[j]), and words[i][j] = words[j][i].
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_3
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      Aegis.ValidWordSquare.valid_word_square words = ok true →
        ∀ (i : Nat), i < words.val.length → ∀ (j : Nat), j < (Row words i).length →
          j < words.val.length ∧ i < (Row words j).length ∧ byteAt words i j = byteAt words j i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), Aegis.ValidWordSquare.valid_word_square words = ok true →
          ∀ (i : Nat), i < words.val.length → ∀ (j : Nat), j < (Row words i).length →
            j < words.val.length ∧ i < (Row words j).length ∧ byteAt words i j = byteAt words j i) := by
    sorry

  /-- Whenever valid_word_square(words) returns true, then for every k with 0 <= k < len(words), the length len(words[k]) equals the number of indices i with 0 <= i < len(words) and k < len(words[i]).
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_4
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      Aegis.ValidWordSquare.valid_word_square words = ok true →
        ∀ (k : Nat), (hk : k < words.val.length) →
          (words.val[k]).val.length = colCount words k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), Aegis.ValidWordSquare.valid_word_square words = ok true →
          ∀ (k : Nat), (hk : k < words.val.length) →
            (words.val[k]).val.length = colCount words k) := by
    sorry

  /-- Whenever valid_word_square(words) returns false, there exist integers i and j such that 0 <= i < len(words), 0 <= j < len(words[i]), and either (j >= len(words)), or (j < len(words) and i >= len(words[j])), or (j < len(words) and i < len(words[j]) and words[i][j] != words[j][i]).
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_5
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      Aegis.ValidWordSquare.valid_word_square words = ok false →
        ∃ (i : Nat) (j : Nat), i < words.val.length ∧ j < (Row words i).length ∧
          (words.val.length ≤ j ∨
            (j < words.val.length ∧ (Row words j).length ≤ i) ∨
            (j < words.val.length ∧ i < (Row words j).length ∧
              byteAt words i j ≠ byteAt words j i)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), Aegis.ValidWordSquare.valid_word_square words = ok false →
          ∃ (i : Nat) (j : Nat), i < words.val.length ∧ j < (Row words i).length ∧
            (words.val.length ≤ j ∨
              (j < words.val.length ∧ (Row words j).length ≤ i) ∨
              (j < words.val.length ∧ i < (Row words j).length ∧
                byteAt words i j ≠ byteAt words j i))) := by
    sorry

  /-- If there exists an index i with 0 <= i < len(words) such that len(words[i]) > len(words), then the function returns a result r and r = false.
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_6
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      (∃ (i : Nat), i < words.val.length ∧ words.val.length < (Row words i).length) →
        ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧ r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), (∃ (i : Nat), i < words.val.length ∧ words.val.length < (Row words i).length) →
          ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧ r = false) := by
    sorry

  /-- If len(words[0]) != len(words), then the function returns a result r and r = false.
    Preconditions: 1 <= len(words) <= 500; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 500; and every byte words[i][j] with 0 <= j < len(words[i]) is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_7
      (words : Slice (alloc.vec.Vec U8))
      (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
      (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
      (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
        (hj : j < (words.val[i]).val.length) →
        97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122) :
      (words.val[0]).val.length ≠ words.val.length →
        ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧ r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen1 : 1 ≤ words.val.length) (hlen2 : words.val.length ≤ 500)
        (hrow : ∀ (i : Nat), (hi : i < words.val.length) →
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 500)
        (hbyte : ∀ (i : Nat), (hi : i < words.val.length) → ∀ (j : Nat),
          (hj : j < (words.val[i]).val.length) →
          97 ≤ ((words.val[i]).val[j]).val ∧ ((words.val[i]).val[j]).val ≤ 122), (words.val[0]).val.length ≠ words.val.length →
          ∃ r, Aegis.ValidWordSquare.valid_word_square words = ok r ∧ r = false) := by
    sorry

  end AegisSpec.ValidWordSquare
