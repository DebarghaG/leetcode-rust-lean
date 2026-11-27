import Aegis.CheckZeroOnes.Code.Funs

/-!
# Specifications of `Aegis.CheckZeroOnes.check_zero_ones`

LeetCode problem `longer-contiguous-segments-of-ones-than-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckZeroOnes

  def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ := (s.val.getD i (0#u8)).val

  def hasRun (s : Slice Std.U8) (d : ℕ) (L : ℕ) : Prop :=
    ∃ l u : ℕ, l < u ∧ u ≤ s.val.length ∧ u - l = L ∧
      ∀ k, l ≤ k → k < u → byteAt s k = d

  noncomputable def maxRun (s : Slice Std.U8) (d : ℕ) : ℕ :=
    sSup { L : ℕ | hasRun s d L }

  noncomputable def L1 (s : Slice Std.U8) : ℕ := maxRun s 49

  noncomputable def L0 (s : Slice Std.U8) : ℕ := maxRun s 48

  def flipDigit (b : Std.U8) : Std.U8 := if b = (49#u8) then (48#u8) else (49#u8)

  /-- Define L1(s) as the largest L for which there exist integers l and u with 0 <= l < u <= len(s), u - l = L, and s[k] = 49 for every k with l <= k < u; if no such L exists, let L1(s) = 0. Define L0(s) analogously with s[k] = 48. The function returns a result r and r = true if and only if L1(s) > L0(s).
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_1
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ (r = true ↔ L1 s > L0 s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ (r = true ↔ L1 s > L0 s)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every s satisfying the preconditions.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_2
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r) := by
    sorry

  /-- If s[i] = 49 for every i with 0 <= i < len(s), then the function returns true.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_3
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (hones : ∀ i, i < s.val.length → byteAt s i = 49) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (hones : ∀ i, i < s.val.length → byteAt s i = 49), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true) := by
    sorry

  /-- If s[i] = 48 for every i with 0 <= i < len(s), then the function returns false.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_4
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (hzeros : ∀ i, i < s.val.length → byteAt s i = 48) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (hzeros : ∀ i, i < s.val.length → byteAt s i = 48), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false) := by
    sorry

  /-- If len(s) = 1, then the function returns true if and only if s[0] = 49.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_5
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (hlen : s.val.length = 1) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ (r = true ↔ byteAt s 0 = 49) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (hlen : s.val.length = 1), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ (r = true ↔ byteAt s 0 = 49)) := by
    sorry

  /-- Define L1(s) and L0(s) as the longest lengths of nonempty contiguous all-49 and all-48 segments, respectively, with value 0 when the corresponding digit is absent. If L1(s) = L0(s), then the function returns false.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_6
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (heq : L1 s = L0 s) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (heq : L1 s = L0 s), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false) := by
    sorry

  /-- Define L1(s) and L0(s) as the longest lengths of nonempty contiguous all-49 and all-48 segments, respectively, with value 0 when the corresponding digit is absent. If L1(s) = 1 and there exists an index i with 0 <= i < len(s) and s[i] = 48, then the function returns false.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_7
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (h1 : L1 s = 1) (h0 : ∃ i, i < s.val.length ∧ byteAt s i = 48) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (h1 : L1 s = 1) (h0 : ∃ i, i < s.val.length ∧ byteAt s i = 48), ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false) := by
    sorry

  /-- Define L0(s) as the largest length of a nonempty contiguous all-48 segment, or 0 if there is no 48. Whenever the function returns a result r with r = true, there exist integers l and u such that 0 <= l < u <= len(s), u - l = L0(s) + 1, and s[k] = 49 for every k with l <= k < u.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_8
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r → r = true →
        ∃ l u : ℕ, l < u ∧ u ≤ s.val.length ∧ u - l = L0 s + 1 ∧
          ∀ k, l ≤ k → k < u → byteAt s k = 49 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r → r = true →
          ∃ l u : ℕ, l < u ∧ u ≤ s.val.length ∧ u - l = L0 s + 1 ∧
            ∀ k, l ≤ k → k < u → byteAt s k = 49) := by
    sorry

  /-- Define L0(s) as the largest length of a nonempty contiguous all-48 segment, or 0 if there is no 48. Whenever the function returns a result r with r = false, L0(s) >= 1 and every nonempty contiguous interval of indices on which all bytes are 49 has length at most L0(s).
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_9
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r → r = false →
        1 ≤ L0 s ∧
          ∀ l u : ℕ, l < u → u ≤ s.val.length →
            (∀ k, l ≤ k → k < u → byteAt s k = 49) → u - l ≤ L0 s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r → r = false →
          1 ≤ L0 s ∧
            ∀ l u : ℕ, l < u → u ≤ s.val.length →
              (∀ k, l ≤ k → k < u → byteAt s k = 49) → u - l ≤ L0 s) := by
    sorry

  /-- Let t be the byte slice of length len(s) defined by t[i] = s[len(s) - 1 - i] for every i with 0 <= i < len(s). The Boolean result returned by the function on input t equals the Boolean result returned by the function on input s.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_10
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (t : Slice Std.U8) (ht : t.val = s.val.reverse) :
      ∃ rs rt, Aegis.CheckZeroOnes.check_zero_ones s = ok rs ∧
        Aegis.CheckZeroOnes.check_zero_ones t = ok rt ∧ rs = rt := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (t : Slice Std.U8) (ht : t.val = s.val.reverse), ∃ rs rt, Aegis.CheckZeroOnes.check_zero_ones s = ok rs ∧
          Aegis.CheckZeroOnes.check_zero_ones t = ok rt ∧ rs = rt) := by
    sorry

  /-- Let t be the byte slice of length len(s) defined by t[i] = 48 when s[i] = 49, and t[i] = 49 when s[i] = 48, for every i with 0 <= i < len(s). Define L1(s) and L0(s) as the longest lengths of nonempty contiguous all-49 and all-48 segments, respectively, with value 0 when the corresponding digit is absent. If L1(s) != L0(s), then the Boolean result returned on input t is the negation of the Boolean result returned on input s.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_11
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (t : Slice Std.U8) (ht : t.val = s.val.map flipDigit)
      (hne : L1 s ≠ L0 s) :
      ∃ rs rt, Aegis.CheckZeroOnes.check_zero_ones s = ok rs ∧
        Aegis.CheckZeroOnes.check_zero_ones t = ok rt ∧ rt = Bool.not rs := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (t : Slice Std.U8) (ht : t.val = s.val.map flipDigit)
        (hne : L1 s ≠ L0 s), ∃ rs rt, Aegis.CheckZeroOnes.check_zero_ones s = ok rs ∧
          Aegis.CheckZeroOnes.check_zero_ones t = ok rt ∧ rt = Bool.not rs) := by
    sorry

  /-- Let t be the byte slice of length len(s) + 1 with t[i] = s[i] for 0 <= i < len(s) and t[len(s)] = 49. If the function returns true on input s, then the function returns true on input t.
    Preconditions: 1 <= len(s) <= 99 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_12
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 99)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (t : Slice Std.U8) (ht : t.val = s.val ++ [49#u8])
      (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 99)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (t : Slice Std.U8) (ht : t.val = s.val ++ [49#u8])
        (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true), ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = true) := by
    sorry

  /-- Let t be the byte slice of length len(s) + 1 with t[i] = s[i] for 0 <= i < len(s) and t[len(s)] = 48. If the function returns false on input s, then the function returns false on input t.
    Preconditions: 1 <= len(s) <= 99 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_13
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 99)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (t : Slice Std.U8) (ht : t.val = s.val ++ [48#u8])
      (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = false := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 99)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (t : Slice Std.U8) (ht : t.val = s.val ++ [48#u8])
        (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false), ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = false) := by
    sorry

  /-- For every index i with 0 <= i < len(s) and s[i] = 48, let t be the byte slice of the same length as s with t[i] = 49 and t[j] = s[j] for every j with 0 <= j < len(s) and j != i. If the function returns true on input s, then the function returns true on input t.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_14
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (i : ℕ) (hi : i < s.val.length) (hi48 : byteAt s i = 48)
      (t : Slice Std.U8) (ht : t.val = s.val.set i (49#u8))
      (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = true := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (i : ℕ) (hi : i < s.val.length) (hi48 : byteAt s i = 48)
        (t : Slice Std.U8) (ht : t.val = s.val.set i (49#u8))
        (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = true), ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = true) := by
    sorry

  /-- For every index i with 0 <= i < len(s) and s[i] = 49, let t be the byte slice of the same length as s with t[i] = 48 and t[j] = s[j] for every j with 0 <= j < len(s) and j != i. If the function returns false on input s, then the function returns false on input t.
    Preconditions: 1 <= len(s) <= 100 and for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_15
      (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
      (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (i : ℕ) (hi : i < s.val.length) (hi49 : byteAt s i = 49)
      (t : Slice Std.U8) (ht : t.val = s.val.set i (48#u8))
      (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false) :
      ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = false := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100)
        (hbytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (i : ℕ) (hi : i < s.val.length) (hi49 : byteAt s i = 49)
        (t : Slice Std.U8) (ht : t.val = s.val.set i (48#u8))
        (hs : ∃ r, Aegis.CheckZeroOnes.check_zero_ones s = ok r ∧ r = false), ∃ r, Aegis.CheckZeroOnes.check_zero_ones t = ok r ∧ r = false) := by
    sorry

  end AegisSpec.CheckZeroOnes
