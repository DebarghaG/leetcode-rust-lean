import Aegis.CountAsterisks.Code.Funs

/-!
# Specifications of `Aegis.CountAsterisks.count_asterisks`

LeetCode problem `count-asterisks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountAsterisks

  def byteAt (s : Slice Std.U8) (i : ℕ) : Option ℕ := (s.val[i]?).map (fun c => c.val)

  def byteVal (s : Slice Std.U8) (i : ℕ) : ℕ := (byteAt s i).getD 0

  def starAt (s : Slice Std.U8) (i : ℕ) : Prop := byteVal s i = 42

  instance decidableStarAt (s : Slice Std.U8) (i : ℕ) : Decidable (starAt s i) :=
    inferInstanceAs (Decidable (byteVal s i = 42))

  def barAt (s : Slice Std.U8) (i : ℕ) : Prop := byteVal s i = 124

  instance decidableBarAt (s : Slice Std.U8) (i : ℕ) : Decidable (barAt s i) :=
    inferInstanceAs (Decidable (byteVal s i = 124))

  def lowerAt (s : Slice Std.U8) (i : ℕ) : Prop := 97 ≤ byteVal s i ∧ byteVal s i ≤ 122

  instance decidableLowerAt (s : Slice Std.U8) (i : ℕ) : Decidable (lowerAt s i) :=
    inferInstanceAs (Decidable (97 ≤ byteVal s i ∧ byteVal s i ≤ 122))

  def admissibleBytes (s : Slice Std.U8) : Prop :=
    ∀ i : ℕ, i < s.val.length → starAt s i ∨ barAt s i ∨ lowerAt s i

  def barPositions (s : Slice Std.U8) : List ℕ :=
    (List.range s.val.length).filter (fun i => decide (barAt s i))

  def barsTotal (s : Slice Std.U8) : ℕ := (barPositions s).length

  def barsBefore (s : Slice Std.U8) (i : ℕ) : ℕ :=
    ((List.range i).filter (fun j => decide (barAt s j))).length

  def starCount (s : Slice Std.U8) : ℕ :=
    ((List.range s.val.length).filter (fun i => decide (starAt s i))).length

  def starsBefore (s : Slice Std.U8) (i : ℕ) : ℕ :=
    ((List.range i).filter (fun j => decide (starAt s j))).length

  def starsAfter (s : Slice Std.U8) (i : ℕ) : ℕ :=
    ((List.range s.val.length).filter (fun j => decide (i < j ∧ starAt s j))).length

  def starsBetween (s : Slice Std.U8) (p q : ℕ) : ℕ :=
    ((List.range q).filter (fun j => decide (p < j ∧ starAt s j))).length

  def countedStars (s : Slice Std.U8) : ℕ :=
    ((List.range s.val.length).filter
      (fun i => decide (starAt s i ∧ barsBefore s i % 2 = 0))).length

  def starsBetweenBarsPairs (s : Slice Std.U8) : List ℕ → ℕ
    | [] => 0
    | [_] => 0
    | p :: q :: rest => starsBetween s p q + starsBetweenBarsPairs s rest

  def excludedStars (s : Slice Std.U8) : ℕ := starsBetweenBarsPairs s (barPositions s)

  /-- Whenever the function returns a result r, the integer value represented by r equals the number of indices i such that 0 <= i < len(s), s[i] = 42 ('*'), and the number of indices j with 0 <= j < i and s[j] = 124 ('|') is even.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        r.val = (countedStars s : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          r.val = (countedStars s : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result (Ok) and does not fail: no integer overflow, out-of-bounds access, or panic occurs.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0) :
      ∃ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0), ∃ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= V <= N, where V is the integer value represented by r and N is the number of indices i with 0 <= i < len(s) and s[i] = 42 ('*'). In particular, 0 <= V <= len(s) <= 1000.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        0 ≤ r.val ∧ r.val ≤ (starCount s : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          0 ≤ r.val ∧ r.val ≤ (starCount s : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, the integer value represented by r equals the number of indices i with 0 <= i < len(s) and s[i] = 42 ('*').
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); the number of indices i with s[i] = 124 is even; and s contains no byte equal to 124 ('|'). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
      (hnobar : ∀ i : ℕ, i < s.val.length → ¬ barAt s i) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        r.val = (starCount s : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
        (hnobar : ∀ i : ℕ, i < s.val.length → ¬ barAt s i), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          r.val = (starCount s : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, the integer value represented by r is 0.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); the number of indices i with s[i] = 124 is even; and s contains no byte equal to 42 ('*'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
      (hnostar : ∀ i : ℕ, i < s.val.length → ¬ starAt s i) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
        (hnostar : ∀ i : ℕ, i < s.val.length → ¬ starAt s i), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, the integer value represented by r equals A + B, where A is the number of indices i with 0 <= i < p and s[i] = 42 ('*'), and B is the number of indices i with q < i < len(s) and s[i] = 42 ('*').
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); s contains exactly two bytes equal to 124 ('|'); let p and q be their indices with 0 <= p < q < len(s). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s)
      (p q : ℕ) (hpq : p < q) (hq_lt : q < s.val.length)
      (hp_bar : barAt s p) (hq_bar : barAt s q)
      (honly : ∀ i : ℕ, i < s.val.length → barAt s i → i = p ∨ i = q) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        r.val = (starsBefore s p : ℤ) + (starsAfter s q : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s)
        (p q : ℕ) (hpq : p < q) (hq_lt : q < s.val.length)
        (hp_bar : barAt s p) (hq_bar : barAt s q)
        (honly : ∀ i : ℕ, i < s.val.length → barAt s i → i = p ∨ i = q), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          r.val = (starsBefore s p : ℤ) + (starsAfter s q : ℤ)) := by
    sorry

  /-- If the function returns a result r_s on input s and a result r_t on input t, then the integer value represented by r_s equals the integer value represented by r_t.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. Let t be the byte array of length len(s) with t[i] = s[len(s)-1-i] for every 0 <= i < len(s); then t satisfies the same constraints. -/
  theorem spec_7 (s t : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
      (hrev : t.val = s.val.reverse) :
      ∀ r_s r_t : Std.I64,
        Aegis.CountAsterisks.count_asterisks s = ok r_s →
        Aegis.CountAsterisks.count_asterisks t = ok r_t →
        r_s.val = r_t.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
        (hrev : t.val = s.val.reverse), ∀ r_s r_t : Std.I64,
          Aegis.CountAsterisks.count_asterisks s = ok r_s →
          Aegis.CountAsterisks.count_asterisks t = ok r_t →
          r_s.val = r_t.val) := by
    sorry

  /-- Whenever the function returns a result r, let T be the number of indices i with s[i] = 42 ('*'), and let E be the sum over k = 0,...,m-1 of the number of indices i with b_{2k} < i < b_{2k+1} and s[i] = 42 ('*'), where m is half the number of '|' bytes and b_0 < b_1 < ... < b_{2m-1} are the indices i with s[i] = 124 ('|') (the sum is empty when m = 0). Then the integer value represented by r plus E equals T.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        r.val + (excludedStars s : ℤ) = (starCount s : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          r.val + (excludedStars s : ℤ) = (starCount s : ℤ)) := by
    sorry

  /-- If the function returns a result r_s on input s and a result r_t on input t, then the integer value represented by r_s equals the integer value represented by r_t plus 1.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. Choose an index i with 0 <= i < len(s), s[i] = 42 ('*'), and the number of j with 0 <= j < i and s[j] = 124 ('|') is even. Let t be the byte array with len(t) = len(s), t[k] = s[k] for all k != i, and t[i] an ASCII lowercase letter (97..122); then t satisfies the same constraints. -/
  theorem spec_9 (s t : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
      (i : ℕ) (hi : i < s.val.length) (hstar : starAt s i) (hi_even : barsBefore s i % 2 = 0)
      (ht : ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧ t.val = s.val.set i c) :
      ∀ r_s r_t : Std.I64,
        Aegis.CountAsterisks.count_asterisks s = ok r_s →
        Aegis.CountAsterisks.count_asterisks t = ok r_t →
        r_s.val = r_t.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0)
        (i : ℕ) (hi : i < s.val.length) (hstar : starAt s i) (hi_even : barsBefore s i % 2 = 0)
        (ht : ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧ t.val = s.val.set i c), ∀ r_s r_t : Std.I64,
          Aegis.CountAsterisks.count_asterisks s = ok r_s →
          Aegis.CountAsterisks.count_asterisks t = ok r_t →
          r_s.val = r_t.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, the integer value represented by r is 0 if and only if for every i with 0 <= i < len(s) and s[i] = 42 ('*'), the number of indices j with 0 <= j < i and s[j] = 124 ('|') is odd.
    Preconditions: s satisfies the problem constraints: 1 <= len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is 42 ('*'), 124 ('|'), or an ASCII lowercase letter (97..122); and the number of indices i with s[i] = 124 is even. -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
      (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0) :
      ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
        (r.val = 0 ↔ ∀ i : ℕ, i < s.val.length → starAt s i → barsBefore s i % 2 = 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_bound : s.val.length ≤ 1000)
        (hbytes : admissibleBytes s) (heven : barsTotal s % 2 = 0), ∀ r : Std.I64, Aegis.CountAsterisks.count_asterisks s = ok r →
          (r.val = 0 ↔ ∀ i : ℕ, i < s.val.length → starAt s i → barsBefore s i % 2 = 1)) := by
    sorry

  end AegisSpec.CountAsterisks
