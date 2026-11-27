import Aegis.StringMatching.Code.Funs

/-!
# Specifications of `Aegis.StringMatching.string_matching`

LeetCode problem `string-matching-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.StringMatching

  set_option autoImplicit false

  namespace AegisSpec.StringMatching

  abbrev ByteString := alloc.vec.Vec Std.U8

  abbrev Words := Slice (alloc.vec.Vec Std.U8)

  abbrev Rows := alloc.vec.Vec (alloc.vec.Vec Std.U8)

  def byteAt (s : List Std.U8) (i : Nat) : Option Nat := (s[i]?).map (fun b => b.val)

  def isSubstring (s t : List Std.U8) : Prop :=
    ∃ k : Nat, k + s.length ≤ t.length ∧ ∀ j : Nat, j < s.length → byteAt s j = byteAt t (k + j)

  def wordAt (words : Words) (i : Nat) : List Std.U8 :=
    ((words.val[i]?).map (fun v => v.val)).getD []

  noncomputable def countContained (words : Words) : Nat := by
    classical
    exact ((List.range words.val.length).filter (fun i =>
      ∃ j : Nat, j < words.val.length ∧ j ≠ i ∧
        isSubstring (wordAt words i) (wordAt words j))).length

  def maxWordLen (words : Words) : Nat := (words.val.map (fun v => v.val.length)).foldr max 0

  /-- The function returns a result r such that: (1) for every i with 0 <= i < len(r), there exists k with 0 <= k < len(words) such that r[i] = words[k], and there exists j with 0 <= j < len(words) such that words[j] != r[i] and is_substring(r[i], words[j]); (2) for every k with 0 <= k < len(words), if there exists j with 0 <= j < len(words) such that words[j] != words[k] and is_substring(words[k], words[j]), then there exists exactly one i with 0 <= i < len(r) such that r[i] = words[k]. Here is_substring(s, t) means there exists k with 0 <= k and k + len(s) <= len(t) such that for every j with 0 <= j < len(s), s[j] = t[k+j].
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_1 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∃ r, string_matching words = ok r ∧
        (∀ (i : Nat) (hi : i < r.val.length),
          (∃ (k : Nat) (hk : k < words.val.length),
            (r.val[i]'hi).val = (words.val[k]'hk).val) ∧
          (∃ (j : Nat) (hj : j < words.val.length),
            (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
              isSubstring (r.val[i]'hi).val (words.val[j]'hj).val)) ∧
        (∀ (k : Nat) (hk : k < words.val.length),
          (∃ (j : Nat) (hj : j < words.val.length),
            (words.val[j]'hj).val ≠ (words.val[k]'hk).val ∧
              isSubstring (words.val[k]'hk).val (words.val[j]'hj).val) →
          ∃ (i : Nat) (hi : i < r.val.length),
            (r.val[i]'hi).val = (words.val[k]'hk).val ∧
              ∀ (i' : Nat) (hi' : i' < r.val.length),
                (r.val[i']'hi').val = (words.val[k]'hk).val → i' = i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∃ r, string_matching words = ok r ∧
          (∀ (i : Nat) (hi : i < r.val.length),
            (∃ (k : Nat) (hk : k < words.val.length),
              (r.val[i]'hi).val = (words.val[k]'hk).val) ∧
            (∃ (j : Nat) (hj : j < words.val.length),
              (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
                isSubstring (r.val[i]'hi).val (words.val[j]'hj).val)) ∧
          (∀ (k : Nat) (hk : k < words.val.length),
            (∃ (j : Nat) (hj : j < words.val.length),
              (words.val[j]'hj).val ≠ (words.val[k]'hk).val ∧
                isSubstring (words.val[k]'hk).val (words.val[j]'hj).val) →
            ∃ (i : Nat) (hi : i < r.val.length),
              (r.val[i]'hi).val = (words.val[k]'hk).val ∧
                ∀ (i' : Nat) (hi' : i' < r.val.length),
                  (r.val[i']'hi').val = (words.val[k]'hk).val → i' = i)) := by
    sorry

  /-- Whenever words satisfies the preconditions, the function returns a result r (it does not fail, overflow, or panic).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_2 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∃ r, string_matching words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∃ r, string_matching words = ok r) := by
    sorry

  /-- For every i with 0 <= i < len(r), there exists k with 0 <= k < len(words) such that r[i] = words[k].
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_3 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
        ∃ (k : Nat) (hk : k < words.val.length), (r.val[i]'hi).val = (words.val[k]'hk).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
          ∃ (k : Nat) (hk : k < words.val.length), (r.val[i]'hi).val = (words.val[k]'hk).val) := by
    sorry

  /-- For every i with 0 <= i < len(r), there exists j with 0 <= j < len(words) such that words[j] != r[i] and is_substring(r[i], words[j]).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_4 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
        ∃ (j : Nat) (hj : j < words.val.length),
          (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
            isSubstring (r.val[i]'hi).val (words.val[j]'hj).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
          ∃ (j : Nat) (hj : j < words.val.length),
            (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
              isSubstring (r.val[i]'hi).val (words.val[j]'hj).val) := by
    sorry

  /-- For every k with 0 <= k < len(words), if there exists j with 0 <= j < len(words) such that words[j] != words[k] and is_substring(words[k], words[j]), then there exists i with 0 <= i < len(r) such that r[i] = words[k].
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_5 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r) (k : Nat) (hk : k < words.val.length),
        (∃ (j : Nat) (hj : j < words.val.length),
          (words.val[j]'hj).val ≠ (words.val[k]'hk).val ∧
            isSubstring (words.val[k]'hk).val (words.val[j]'hj).val) →
          ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = (words.val[k]'hk).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r) (k : Nat) (hk : k < words.val.length),
          (∃ (j : Nat) (hj : j < words.val.length),
            (words.val[j]'hj).val ≠ (words.val[k]'hk).val ∧
              isSubstring (words.val[k]'hk).val (words.val[j]'hj).val) →
            ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = (words.val[k]'hk).val) := by
    sorry

  /-- len(r) = |{ i : 0 <= i < len(words) and there exists j with 0 <= j < len(words), j != i, and is_substring(words[i], words[j]) }|.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_6 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length = countContained words := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length = countContained words) := by
    sorry

  /-- len(r) = 0.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j; and for every i,j with 0 <= i < len(words), 0 <= j < len(words), if i != j then not is_substring(words[i], words[j]). -/
  theorem spec_7 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j)
      (h_no_sub : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        i ≠ j → ¬ isSubstring (words.val[i]'hi).val (words.val[j]'hj).val) :
      ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j)
        (h_no_sub : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          i ≠ j → ¬ isSubstring (words.val[i]'hi).val (words.val[j]'hj).val), ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length = 0) := by
    sorry

  /-- For every i,j with 0 <= i < len(r), 0 <= j < len(r), if r[i] = r[j] then i = j.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_8 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r)
        (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
        (r.val[i]'hi).val = (r.val[j]'hj).val → i = j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r)
          (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
          (r.val[i]'hi).val = (r.val[j]'hj).val → i = j) := by
    sorry

  /-- For every i with 0 <= i < len(r), there exists j with 0 <= j < len(words) such that words[j] != r[i] and is_substring(r[i], words[j]) and len(words[j]) > len(r[i]).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_9 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
        ∃ (j : Nat) (hj : j < words.val.length),
          (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
            isSubstring (r.val[i]'hi).val (words.val[j]'hj).val ∧
              (words.val[j]'hj).val.length > (r.val[i]'hi).val.length := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
          ∃ (j : Nat) (hj : j < words.val.length),
            (words.val[j]'hj).val ≠ (r.val[i]'hi).val ∧
              isSubstring (r.val[i]'hi).val (words.val[j]'hj).val ∧
                (words.val[j]'hj).val.length > (r.val[i]'hi).val.length) := by
    sorry

  /-- len(r) < len(words).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_10 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length < words.val.length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r), r.val.length < words.val.length) := by
    sorry

  /-- For every i with 0 <= i < len(r), len(r[i]) < max_{0 <= k < len(words)} len(words[k]).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 30 and every byte of words[i] is in the range 97..122; for every i,j with 0 <= i < len(words), 0 <= j < len(words), if words[i] = words[j] then i = j. -/
  theorem spec_11 (words : Words)
      (h_n : 1 ≤ words.val.length)
      (h_n' : words.val.length ≤ 100)
      (h_words : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
          ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
      (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
        (words.val[i]'hi).val = (words.val[j]'hj).val → i = j) :
      ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
        (r.val[i]'hi).val.length < maxWordLen words := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words : Words)
        (h_n : 1 ≤ words.val.length)
        (h_n' : words.val.length ≤ 100)
        (h_words : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length ∧ (words.val[i]'hi).val.length ≤ 30 ∧
            ∀ b ∈ (words.val[i]'hi).val, 97 ≤ b.val ∧ b.val ≤ 122)
        (h_distinct : ∀ (i j : Nat) (hi : i < words.val.length) (hj : j < words.val.length),
          (words.val[i]'hi).val = (words.val[j]'hj).val → i = j), ∀ (r : Rows) (hr : string_matching words = ok r) (i : Nat) (hi : i < r.val.length),
          (r.val[i]'hi).val.length < maxWordLen words) := by
    sorry

  end AegisSpec.StringMatching
