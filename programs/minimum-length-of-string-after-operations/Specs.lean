import Aegis.MinimumLength.Code.Funs

/-!
# Specifications of `Aegis.MinimumLength.minimum_length`

LeetCode problem `minimum-length-of-string-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumLength

  def isLowerByte (b : Aeneas.Std.U8) : Prop :=
    97 ≤ b.val ∧ b.val ≤ 122

  def countOf (l : List Aeneas.Std.U8) (c : ℕ) : ℕ :=
    (l.filter (fun b => b.val = 97 + c)).length

  def weight (n : ℕ) : ℤ :=
    if n = 0 then 0 else if n % 2 = 0 then 2 else 1

  def answer (l : List Aeneas.Std.U8) : ℤ :=
    Finset.sum (Finset.range 26) (fun c => weight (countOf l c))

  def numDistinct (l : List Aeneas.Std.U8) : ℕ :=
    l.dedup.length

  def step (u v : List Aeneas.Std.U8) : Prop :=
    ∃ (i : Fin u.length) (j k : Fin u.length),
      j.val < i.val ∧ i.val < k.val ∧
      u.get j = u.get i ∧ u.get k = u.get i ∧
      (∀ (j' : Fin u.length), j'.val < i.val → u.get j' = u.get i → j'.val ≤ j.val) ∧
      (∀ (k' : Fin u.length), i.val < k'.val → u.get k' = u.get i → k.val ≤ k'.val) ∧
      v = (u.eraseIdx k.val).eraseIdx j.val

  def Reach (u v : List Aeneas.Std.U8) : Prop :=
    Relation.ReflTransGen step u v

  /-- The function returns a result r (i.e. minimum_length s = Result.ok r) and r = sum over c from 'a' to 'z' of f(cnt(c)), where cnt(c) is the number of indices i with 0 <= i < len(s) and s[i] equal to the ASCII code of c, and f is defined by f(0)=0, f(n)=1 if n is odd, and f(n)=2 if n is a positive even integer.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧ r.val = answer s.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧ r.val = answer s.val) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r (minimum_length s = Result.ok r) and does not fail, panic, or overflow.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64, Aegis.MinimumLength.minimum_length s = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64, Aegis.MinimumLength.minimum_length s = Result.ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(s).
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r >= d, where d is the number of distinct byte values occurring among s[0],...,s[len(s)-1].
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          (numDistinct s.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            (numDistinct s.val : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 2*d, where d is the number of distinct byte values occurring among s[0],...,s[len(s)-1].
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          r.val ≤ 2 * (numDistinct s.val : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            r.val ≤ 2 * (numDistinct s.val : ℤ)) := by
    sorry

  /-- The function returns a result r and r mod 2 = len(s) mod 2.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          r.val % 2 = (s.val.length : ℤ) % 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            r.val % 2 = (s.val.length : ℤ) % 2) := by
    sorry

  /-- The function returns a result r and there exists a finite sequence of zero or more allowed operations that transforms s into a string t with len(t)=r. An allowed operation on a string u chooses an index i with 0 <= i < len(u) for which there is an equal character both somewhere strictly left of i and somewhere strictly right of i in u, and deletes the closest such equal character to the left of i and the closest such equal character to the right of i.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          ∃ t : List Aeneas.Std.U8, Reach s.val t ∧ (t.length : ℤ) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            ∃ t : List Aeneas.Std.U8, Reach s.val t ∧ (t.length : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and for every string t reachable from s by any finite sequence of zero or more allowed operations (with the same operation definition as in spec_7), len(t) >= r.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧
          ∀ t : List Aeneas.Std.U8, Reach s.val t → r.val ≤ (t.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧
            ∀ t : List Aeneas.Std.U8, Reach s.val t → r.val ≤ (t.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r <= len(s) - 2.
    Preconditions: s is a slice of bytes; 1 <= len(s) <= 200000; for every i with 0 <= i < len(s), s[i] is the ASCII code of a lowercase English letter; there exists a lowercase English letter c whose number of occurrences in s is at least 3. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
      (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩))
      (hthree : ∃ c : ℕ, c < 26 ∧ 3 ≤ countOf s.val c) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumLength.minimum_length s = Result.ok r ∧ r.val ≤ (s.val.length : ℤ) - 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
        (hlow : ∀ (i : ℕ) (hi : i < s.val.length), isLowerByte (s.val.get ⟨i, hi⟩))
        (hthree : ∃ c : ℕ, c < 26 ∧ 3 ≤ countOf s.val c), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumLength.minimum_length s = Result.ok r ∧ r.val ≤ (s.val.length : ℤ) - 2) := by
    sorry

  end AegisSpec.MinimumLength
