import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-score-after-splitting-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxScore

  abbrev codeZero : ℕ := 48

  abbrev codeOne : ℕ := 49

  def slen (s : Slice U8) : ℕ := s.val.length

  def byteAt (s : Slice U8) (i : ℕ) : ℕ := ((s.val.drop i).head?).map (fun b => b.val) |>.getD 0

  def countIn (s : Slice U8) (lo hi c : ℕ) : ℕ :=
    ((s.val.drop lo).take (hi - lo)).countP (fun b => b.val = c)

  def zerosBefore (s : Slice U8) (k : ℕ) : ℕ := countIn s 0 k codeZero

  def onesFrom (s : Slice U8) (k : ℕ) : ℕ := countIn s k (slen s) codeOne

  def onesBefore (s : Slice U8) (k : ℕ) : ℕ := countIn s 0 k codeOne

  def totalOnes (s : Slice U8) : ℕ := countIn s 0 (slen s) codeOne

  def totalZeros (s : Slice U8) : ℕ := countIn s 0 (slen s) codeZero

  def score (s : Slice U8) (k : ℕ) : ℕ := zerosBefore s k + onesFrom s k

  def balance (s : Slice U8) (k : ℕ) : ℤ := (zerosBefore s k : ℤ) - (onesBefore s k : ℤ)

  def splitPoints (s : Slice U8) : List ℕ := (List.range (slen s - 1)).map (· + 1)

  def listMax {α : Type} [Max α] (d : α) : List α → α
    | [] => d
    | x :: xs => xs.foldl max x

  def maxScore (s : Slice U8) : ℕ := listMax 0 ((splitPoints s).map (score s))

  def maxBalance (s : Slice U8) : ℤ := listMax 0 ((splitPoints s).map (balance s))

  def IsBinary (s : Slice U8) : Prop := ∀ b ∈ s.val, b.val = codeZero ∨ b.val = codeOne

  def flipByte (b : U8) : U8 := if b.val = codeZero then 49#u8 else 48#u8

  def mkSlice (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
    ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

  def complementReverse (s : Slice U8) : Slice U8 :=
    mkSlice (s.val.map flipByte).reverse (by
      have hlen : (s.val.map flipByte).reverse.length = s.val.length := by simp
      have hval : s.val.length = s.leng := by
        simp [Slice.val, Aeneas.Data.ListN.ListN_length]
      rw [hlen, hval]
      exact s.bound)

  theorem slen_eq_len (s : Slice U8) : slen s = (Slice.len s).val := by
    simp [slen, Slice.len]

  theorem complementReverse_val (s : Slice U8) :
      (complementReverse s).val = (s.val.map flipByte).reverse := by
    simp [complementReverse, mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  theorem slen_complementReverse (s : Slice U8) : slen (complementReverse s) = slen s := by
    simp [slen, complementReverse, mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  theorem flipByte_isBinary (b : U8) :
      (flipByte b).val = codeZero ∨ (flipByte b).val = codeOne := by
    unfold flipByte
    split <;> simp_all

  theorem isBinary_complementReverse (s : Slice U8) : IsBinary (complementReverse s) := by
    intro b hb
    rw [complementReverse_val, List.mem_reverse] at hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    exact flipByte_isBinary c

  /-- Let n = len(s). For each integer k with 1 <= k <= n-1, define score(k) = (the number of indices j with 0 <= j < k and s[j] = 48) + (the number of indices j with k <= j < n and s[j] = 49). Let M = max { score(k) | 1 <= k <= n-1 }. Then max_score(s) returns a result r (i.e. it does not fail), and when r is interpreted as an integer in [-2^63, 2^63-1], its value equals M.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_1 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∃ r : I64, Aegis.MaxScore.max_score s = Result.ok r ∧ r.val = (maxScore s : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∃ r : I64, Aegis.MaxScore.max_score s = Result.ok r ∧ r.val = (maxScore s : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, max_score(s) returns a result (some 64-bit integer r) and does not fail.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_2 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∃ r : I64, Aegis.MaxScore.max_score s = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∃ r : I64, Aegis.MaxScore.max_score s = Result.ok r) := by
    sorry

  /-- Whenever max_score(s) returns a result r, the integer value of r is at least 0.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_3 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever max_score(s) returns a result r, the integer value of r is at most len(s).
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_4 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → r.val ≤ (slen s : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → r.val ≤ (slen s : ℤ)) := by
    sorry

  /-- Whenever max_score(s) returns a result r, there exists an integer k with 1 <= k <= len(s)-1 such that r = score(k), where score(k) = (the number of indices j with 0 <= j < k and s[j] = 48) + (the number of indices j with k <= j < len(s) and s[j] = 49).
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_5 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ slen s - 1 ∧ r.val = (score s k : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ slen s - 1 ∧ r.val = (score s k : ℤ)) := by
    sorry

  /-- Whenever max_score(s) returns a result r, for every integer k with 1 <= k <= len(s)-1, score(k) <= r, where score(k) = (the number of indices j with 0 <= j < k and s[j] = 48) + (the number of indices j with k <= j < len(s) and s[j] = 49).
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_6 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        ∀ k : ℕ, 1 ≤ k → k ≤ slen s - 1 → (score s k : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          ∀ k : ℕ, 1 ≤ k → k ≤ slen s - 1 → (score s k : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever max_score(s) returns a result r, the integer value of r equals len(s) - 1.
    Preconditions: 2 <= len(s) <= 500, and every byte s[j] with 0 <= j < len(s) is the ASCII code of '1' (49). -/
  theorem spec_7 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500)
      (hones : ∀ b ∈ s.val, b.val = codeOne) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → r.val = (slen s : ℤ) - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500)
        (hones : ∀ b ∈ s.val, b.val = codeOne), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r → r.val = (slen s : ℤ) - 1) := by
    sorry

  /-- Whenever max_score(s) returns a result r, the integer value of r equals (1 if s[0] = 48 else 0) + (1 if s[1] = 49 else 0).
    Preconditions: len(s) = 2, and each byte s[0], s[1] is either 48 ('0') or 49 ('1'). -/
  theorem spec_8 (s : Slice U8) (hlen : slen s = 2)
      (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        r.val = (if byteAt s 0 = codeZero then (1 : ℤ) else 0)
                  + (if byteAt s 1 = codeOne then (1 : ℤ) else 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (hlen : slen s = 2)
        (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          r.val = (if byteAt s 0 = codeZero then (1 : ℤ) else 0)
                    + (if byteAt s 1 = codeOne then (1 : ℤ) else 0)) := by
    sorry

  /-- Let n = len(s), let total_ones = the number of indices j with 0 <= j < n and s[j] = 49, and for 1 <= k <= n-1 let balance(k) = (the number of indices j with 0 <= j < k and s[j] = 48) - (the number of indices j with 0 <= j < k and s[j] = 49). Then whenever max_score(s) returns a result r, the integer value of r equals total_ones + max { balance(k) | 1 <= k <= n-1 }.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_9 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        r.val = (totalOnes s : ℤ) + maxBalance s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          r.val = (totalOnes s : ℤ) + maxBalance s) := by
    sorry

  /-- Let n = len(s), and let t be the byte string of length n defined by: for each i with 0 <= i < n, t[i] = 49 if s[n-1-i] = 48, and t[i] = 48 if s[n-1-i] = 49. Then whenever max_score(s) returns a result r and max_score(t) returns a result r_t, the integer value of r equals the integer value of r_t.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_10 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        ∀ r_t : I64, Aegis.MaxScore.max_score (complementReverse s) = Result.ok r_t →
          r.val = r_t.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          ∀ r_t : I64, Aegis.MaxScore.max_score (complementReverse s) = Result.ok r_t →
            r.val = r_t.val) := by
    sorry

  /-- Let total_ones = the number of indices j with 0 <= j < len(s) and s[j] = 49, and total_zeros = the number of indices j with 0 <= j < len(s) and s[j] = 48. Whenever max_score(s) returns a result r, the integer value of r is at least max(total_ones, total_zeros) - 1.
    Preconditions: 2 <= len(s) <= 500, and for every index j with 0 <= j < len(s), the byte s[j] is either the ASCII code of '0' (48) or the ASCII code of '1' (49). -/
  theorem spec_11 (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s) :
      ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
        ((max (totalOnes s) (totalZeros s) : ℕ) : ℤ) - 1 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (h2 : 2 ≤ slen s) (h500 : slen s ≤ 500) (hb : IsBinary s), ∀ r : I64, Aegis.MaxScore.max_score s = Result.ok r →
          ((max (totalOnes s) (totalZeros s) : ℕ) : ℤ) - 1 ≤ r.val) := by
    sorry

  end AegisSpec.MaxScore
