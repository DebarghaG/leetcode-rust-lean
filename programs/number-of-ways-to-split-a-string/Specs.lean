import Aegis.NumWays.Code.Funs

/-!
# Specifications of `Aegis.NumWays.num_ways`

LeetCode problem `number-of-ways-to-split-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumWays

  def countOnes (l : List Std.U8) : ℕ := (l.filter fun b => b.val = 49).length

  def onesCount (s : Slice Std.U8) : ℕ := countOnes s.val

  def allBytes (s : Slice Std.U8) (c : ℕ) : Prop := ∀ b ∈ s.val, b.val = c

  def onesPositions (s : Slice Std.U8) : List ℕ :=
    ((List.finRange s.val.length).filter fun i => (s.val.get i).val = 49).map fun i => i.val

  abbrev IsValidCut (s : Slice Std.U8) (i j : ℕ) : Prop :=
    0 < i ∧ i < j ∧ j < s.val.length ∧
      countOnes (s.val.take i) = countOnes ((s.val.drop i).take (j - i)) ∧
        countOnes (s.val.take i) = countOnes (s.val.drop j)

  def numValidCuts (s : Slice Std.U8) : ℕ :=
    (((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1))).filter
      fun (p : ℕ × ℕ) => IsValidCut s p.1 p.2).card

  def totalCutPairs (n : ℕ) : ℕ := (n - 1) * (n - 2) / 2

  def IsUniformLength3 (s : Slice Std.U8) : Prop :=
    (s.val.length = 3 ∧ allBytes s 48) ∨ (s.val.length = 3 ∧ allBytes s 49)

  /-- The function returns Ok r (it does not fail), where r is the unique integer with 0 <= r < 1000000007 and r is congruent modulo 1000000007 to N, the number of pairs of cut positions (i, j) such that 0 < i < j < len(s) and the three non-empty contiguous parts s[0..i], s[i..j], and s[j..len(s)] each contain the same number of bytes equal to 49. Equivalently, r = N mod 1000000007.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49 (ASCII codes for '0' and '1'). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = ((numValidCuts s : ℤ) % 1000000007) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val = ((numValidCuts s : ℤ) % 1000000007)) := by
    sorry

  /-- The function returns a result r with 0 <= r < 1000000007.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- The function returns a result r such that r is at most the total number of pairs of cut positions (i, j) with 0 < i < j < len(s), namely ((len(s) - 1) * (len(s) - 2)) / 2, without any modulo reduction of that bound.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
        r.val ≤ (totalCutPairs s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
          r.val ≤ (totalCutPairs s.val.length : ℤ)) := by
    sorry

  /-- The function returns the result ((len(s) - 1) * (len(s) - 2)) / 2 modulo 1000000007.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and every byte of s is 48 ('0'), i.e. for every i with 0 <= i < len(s), s[i] = 48. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hzero : ∀ b ∈ s.val, b.val = 48) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
        r.val = ((totalCutPairs s.val.length : ℤ) % 1000000007) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hzero : ∀ b ∈ s.val, b.val = 48), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
          r.val = ((totalCutPairs s.val.length : ℤ) % 1000000007)) := by
    sorry

  /-- The function returns 0.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and the number of bytes equal to 49 in s is not divisible by 3. -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hnotdiv : ¬ (3 ∣ onesCount s)) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hnotdiv : ¬ (3 ∣ onesCount s)), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 0) := by
    sorry

  /-- If the length of s is at most 3, then the function returns 1 exactly when either len(s) = 3 and all three bytes are equal to 48, or len(s) = 3 and all three bytes are equal to 49; otherwise, for len(s) = 3 with mixed bytes, the function returns 0.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (hlen : s.val.length ≤ 3) :
      ((∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 1) ↔ IsUniformLength3 s) ∧
        (¬ IsUniformLength3 s →
          ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (hlen : s.val.length ≤ 3), ((∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 1) ↔ IsUniformLength3 s) ∧
          (¬ IsUniformLength3 s →
            ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧ r.val = 0)) := by
    sorry

  /-- If the function returns a result r with r > 0, then there exists at least one pair of cut positions (i, j) with 0 < i < j < len(s) such that s[0..i], s[i..j], and s[j..len(s)] contain the same number of bytes equal to 49.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (r : Std.I64) (hres : Aegis.NumWays.num_ways s = ok r) (hpos : 0 < r.val) :
      ∃ i j : ℕ, IsValidCut s i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (r : Std.I64) (hres : Aegis.NumWays.num_ways s = ok r) (hpos : 0 < r.val), ∃ i j : ℕ, IsValidCut s i j) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or access memory out of bounds on any input satisfying the preconditions.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r) := by
    sorry

  /-- Let p_0 < p_1 < ... < p_{3k-1} be the 0-indexed positions of the bytes equal to 49 in s. Then the function returns Ok r, where r is the unique integer with 0 <= r < 1000000007 and r is congruent modulo 1000000007 to (p_k - p_{k-1}) * (p_{2k} - p_{2k-1}); equivalently r = ((p_k - p_{k-1}) * (p_{2k} - p_{2k-1})) mod 1000000007.
    Preconditions: len(s) >= 3 and len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49, and the number of bytes equal to 49 in s is 3*k for some integer k > 0. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
      (k : ℕ) (hk : 0 < k) (hcount : (onesPositions s).length = 3 * k) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = (((((onesPositions s).get ⟨k, by omega⟩ : ℕ) : ℤ) -
                     (((onesPositions s).get ⟨k - 1, by omega⟩ : ℕ) : ℤ)) *
                    ((((onesPositions s).get ⟨2 * k, by omega⟩ : ℕ) : ℤ) -
                     (((onesPositions s).get ⟨2 * k - 1, by omega⟩ : ℕ) : ℤ))) %
                    1000000007 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hbin : ∀ b ∈ s.val, b.val = 48 ∨ b.val = 49)
        (k : ℕ) (hk : 0 < k) (hcount : (onesPositions s).length = 3 * k), ∃ r : Std.I64, Aegis.NumWays.num_ways s = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val = (((((onesPositions s).get ⟨k, by omega⟩ : ℕ) : ℤ) -
                       (((onesPositions s).get ⟨k - 1, by omega⟩ : ℕ) : ℤ)) *
                      ((((onesPositions s).get ⟨2 * k, by omega⟩ : ℕ) : ℤ) -
                       (((onesPositions s).get ⟨2 * k - 1, by omega⟩ : ℕ) : ℤ))) %
                      1000000007) := by
    sorry

  end AegisSpec.NumWays
