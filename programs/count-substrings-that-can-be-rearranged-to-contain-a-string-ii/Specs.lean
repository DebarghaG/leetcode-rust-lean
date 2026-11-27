import Aegis.ValidSubstringCount.Code.Funs

/-!
# Specifications of `Aegis.ValidSubstringCount.valid_substring_count`

LeetCode problem `count-substrings-that-can-be-rearranged-to-contain-a-string-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidSubstringCount

  def countByte (s : List Std.U8) (b : ℕ) : ℕ := s.countP (fun c => c.val == b)

  def countByteRange (s : List Std.U8) (i j b : ℕ) : ℕ :=
    ((s.drop i).take (j + 1 - i)).countP (fun c => c.val == b)

  def allBytesInRange (s : List Std.U8) : Prop :=
    ∀ c ∈ s, 97 ≤ c.val ∧ c.val ≤ 122

  def occursIn (s : List Std.U8) (i j b : ℕ) : Prop :=
    ∃ k : ℕ, i ≤ k ∧ k ≤ j ∧ ∃ h : k < s.length, (s[k]'h).val = b

  def windowCovers (w1 w2 : List Std.U8) (i j : ℕ) : Prop :=
    ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte w2 b ≤ countByteRange w1 i j b

  noncomputable def coveringPairCount (w1 w2 : List Std.U8) : ℕ := by
    classical
    exact (Finset.filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ windowCovers w1 w2 p.1 p.2)
      ((Finset.range w1.length).product (Finset.range w1.length))).card

  def countUpperBound (n m : ℕ) : ℕ :=
    if m ≤ n then (n - m + 1) * (n - m + 2) / 2 else 0

  def sameCounts (w1 w2 : List Std.U8) : Prop :=
    ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte w1 b = countByte w2 b

  noncomputable def sameCountsValue (w1 w2 : List Std.U8) : ℤ := by
    classical
    exact if sameCounts w1 w2 then 1 else 0

  noncomputable def exactWindowCount (w1 w2 : List Std.U8) : ℕ := by
    classical
    exact if w2.length ≤ w1.length then
        (Finset.filter
          (fun i : ℕ => ∀ b : ℕ, 97 ≤ b → b ≤ 122 →
            countByteRange w1 i (i + w2.length - 1) b = countByte w2 b)
          (Finset.range (w1.length - w2.length + 1))).card
      else 0

  def windowMeetsNeeds (w1 w2 : List Std.U8) (i j : ℕ) : Prop :=
    ∀ b : ℕ, 97 ≤ b → b ≤ 122 → 0 < countByte w2 b → occursIn w1 i j b

  noncomputable def patternPairCount (w1 w2 : List Std.U8) : ℕ := by
    classical
    exact (Finset.filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ windowMeetsNeeds w1 w2 p.1 p.2)
      ((Finset.range w1.length).product (Finset.range w1.length))).card

  /-- Whenever the function returns Result.ok r, let v be the integer value represented by r. Then v equals the number of pairs (i,j) of natural numbers such that 0 <= i <= j < len(word1) and, for every byte b with 97 <= b <= 122, the number of indices k with i <= k <= j and word1[k] = b is at least the number of indices k with 0 <= k < len(word2) and word2[k] = b.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and for every index i with 0 <= i < len(word1), 97 <= word1[i] <= 122, and for every index i with 0 <= i < len(word2), 97 <= word2[i] <= 122. -/
  theorem spec_1 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      r.val = ((coveringPairCount word1.val word2.val : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), r.val = ((coveringPairCount word1.val word2.val : ℕ) : ℤ)) := by
    sorry

  /-- For every word1 and word2 satisfying the preconditions, the function returns Result.ok r for some r : Std.I64; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and all bytes of word1 and word2 have codes between 97 and 122 inclusive. -/
  theorem spec_2 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val) :
      ∃ r : Std.I64, Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val), ∃ r : Std.I64, Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) := by
    sorry

  /-- Whenever the function returns Result.ok r, let v be the integer value represented by r, n = len(word1), and m = len(word2). Let T = 0 if m > n, and T = (n - m + 1) * (n - m + 2) / 2 if m <= n. Then v <= T.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and all bytes of word1 and word2 have codes between 97 and 122 inclusive. -/
  theorem spec_3 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      r.val ≤ ((countUpperBound word1.val.length word2.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), r.val ≤ ((countUpperBound word1.val.length word2.val.length : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns Result.ok r, let v be the integer value represented by r. Then v = 1 if for every byte b with 97 <= b <= 122 the number of indices k with word1[k] = b equals the number of indices k with word2[k] = b; otherwise v = 0.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, all bytes of word1 and word2 have codes between 97 and 122 inclusive, and len(word1) = len(word2). -/
  theorem spec_4 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (hlen : word1.val.length = word2.val.length)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      r.val = sameCountsValue word1.val word2.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (hlen : word1.val.length = word2.val.length)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), r.val = sameCountsValue word1.val word2.val) := by
    sorry

  /-- If there exists a byte b with 97 <= b <= 122 such that the number of indices k with word2[k] = b is greater than the number of indices k with word1[k] = b, then whenever the function returns Result.ok r, the integer value represented by r is 0.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and all bytes of word1 and word2 have codes between 97 and 122 inclusive. -/
  theorem spec_5 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (hmissing : ∃ b : ℕ, 97 ≤ b ∧ b ≤ 122 ∧ countByte word1.val b < countByte word2.val b)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (hmissing : ∃ b : ℕ, 97 ≤ b ∧ b ≤ 122 ∧ countByte word1.val b < countByte word2.val b)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns Result.ok r, the integer value represented by r is at least 1.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, all bytes of word1 and word2 have codes between 97 and 122 inclusive, and for every byte b with 97 <= b <= 122, the number of indices k with word1[k] = b is at least the number of indices k with word2[k] = b. -/
  theorem spec_6 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (hcovers : ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte word2.val b ≤ countByte word1.val b)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (hcovers : ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte word2.val b ≤ countByte word1.val b)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), 1 ≤ r.val) := by
    sorry

  /-- Let rA be the result of valid_substring_count word1 word2a and rB be the result of valid_substring_count word1 word2b. Whenever both rA and rB are Result.ok values, the integer value represented by rA is at least the integer value represented by rB.
    Preconditions: word1, word2a, and word2b are slices of Std.U8; len(word1) is between 1 and 1000000; len(word2a) and len(word2b) are between 1 and 10000; all bytes of these slices have codes between 97 and 122 inclusive; and for every byte b with 97 <= b <= 122, the number of indices k with word2a[k] = b is at most the number of indices k with word2b[k] = b. -/
  theorem spec_7 (word1 word2a word2b : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2alo : 1 ≤ word2a.val.length) (h2ahi : word2a.val.length ≤ 10000)
      (h2blo : 1 ≤ word2b.val.length) (h2bhi : word2b.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val)
      (hbytes2a : allBytesInRange word2a.val) (hbytes2b : allBytesInRange word2b.val)
      (hle : ∀ b : ℕ, 97 ≤ b → b ≤ 122 →
        countByte word2a.val b ≤ countByte word2b.val b)
      (rA rB : Std.I64)
      (hrA : Aegis.ValidSubstringCount.valid_substring_count word1 word2a = ok rA)
      (hrB : Aegis.ValidSubstringCount.valid_substring_count word1 word2b = ok rB) :
      rB.val ≤ rA.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word1 word2a word2b : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2alo : 1 ≤ word2a.val.length) (h2ahi : word2a.val.length ≤ 10000)
        (h2blo : 1 ≤ word2b.val.length) (h2bhi : word2b.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val)
        (hbytes2a : allBytesInRange word2a.val) (hbytes2b : allBytesInRange word2b.val)
        (hle : ∀ b : ℕ, 97 ≤ b → b ≤ 122 →
          countByte word2a.val b ≤ countByte word2b.val b)
        (rA rB : Std.I64)
        (hrA : Aegis.ValidSubstringCount.valid_substring_count word1 word2a = ok rA)
        (hrB : Aegis.ValidSubstringCount.valid_substring_count word1 word2b = ok rB), rB.val ≤ rA.val) := by
    sorry

  /-- If valid_substring_count word1 word2a returns Result.ok rA and valid_substring_count word1 word2b returns Result.ok rB, then the integer value represented by rA equals the integer value represented by rB.
    Preconditions: word1, word2a, and word2b are slices of Std.U8; len(word1) is between 1 and 1000000; len(word2a) and len(word2b) are between 1 and 10000; all bytes of these slices have codes between 97 and 122 inclusive; and for every byte b with 97 <= b <= 122, the number of indices k with word2a[k] = b equals the number of indices k with word2b[k] = b. -/
  theorem spec_8 (word1 word2a word2b : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2alo : 1 ≤ word2a.val.length) (h2ahi : word2a.val.length ≤ 10000)
      (h2blo : 1 ≤ word2b.val.length) (h2bhi : word2b.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val)
      (hbytes2a : allBytesInRange word2a.val) (hbytes2b : allBytesInRange word2b.val)
      (heq : ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte word2a.val b = countByte word2b.val b)
      (rA rB : Std.I64)
      (hrA : Aegis.ValidSubstringCount.valid_substring_count word1 word2a = ok rA)
      (hrB : Aegis.ValidSubstringCount.valid_substring_count word1 word2b = ok rB) :
      rA.val = rB.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word1 word2a word2b : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2alo : 1 ≤ word2a.val.length) (h2ahi : word2a.val.length ≤ 10000)
        (h2blo : 1 ≤ word2b.val.length) (h2bhi : word2b.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val)
        (hbytes2a : allBytesInRange word2a.val) (hbytes2b : allBytesInRange word2b.val)
        (heq : ∀ b : ℕ, 97 ≤ b → b ≤ 122 → countByte word2a.val b = countByte word2b.val b)
        (rA rB : Std.I64)
        (hrA : Aegis.ValidSubstringCount.valid_substring_count word1 word2a = ok rA)
        (hrB : Aegis.ValidSubstringCount.valid_substring_count word1 word2b = ok rB), rA.val = rB.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, let v be the integer value represented by r, n = len(word1), and m = len(word2). Let W = 0 if m > n. If m <= n, let W be the number of indices i with 0 <= i <= n - m such that for every byte b with 97 <= b <= 122, the number of k with i <= k <= i + m - 1 and word1[k] = b equals the number of k with 0 <= k < len(word2) and word2[k] = b. Then v >= W.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and all bytes of word1 and word2 have codes between 97 and 122 inclusive. -/
  theorem spec_9 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      ((exactWindowCount word1.val word2.val : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), ((exactWindowCount word1.val word2.val : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, let v be the integer value represented by r. Let A be the number of pairs (i,j) with 0 <= i <= j < len(word1) such that for every byte b with 97 <= b <= 122 for which the number of k with word2[k] = b is positive, there exists an index k with i <= k <= j and word1[k] = b. Then v <= A.
    Preconditions: len(word1) >= 1, len(word1) <= 1000000, len(word2) >= 1, len(word2) <= 10000, and all bytes of word1 and word2 have codes between 97 and 122 inclusive. -/
  theorem spec_10 (word1 word2 : Slice Std.U8)
      (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
      (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
      (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
      (r : Std.I64)
      (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r) :
      r.val ≤ ((patternPairCount word1.val word2.val : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8)
        (h1lo : 1 ≤ word1.val.length) (h1hi : word1.val.length ≤ 1000000)
        (h2lo : 1 ≤ word2.val.length) (h2hi : word2.val.length ≤ 10000)
        (hbytes1 : allBytesInRange word1.val) (hbytes2 : allBytesInRange word2.val)
        (r : Std.I64)
        (hr : Aegis.ValidSubstringCount.valid_substring_count word1 word2 = ok r), r.val ≤ ((patternPairCount word1.val word2.val : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.ValidSubstringCount
